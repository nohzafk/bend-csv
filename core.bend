import Base

# Records: every LF (or CRLF) ends a record, so a blank line is a record of one
# empty field. The end of input ends a record only if one is unfinished, so
# the empty input holds no record and a final terminator adds no extra row.
# The parser: one walk over the string, finished fields and records built
# directly, no token list, no state record.
# Mode and accumulators are separate arguments of `go`. The character class is
# computed once per character and ONE match on (mode, class) does the whole step.

type Ans is Data:
  Parsed{rows: List<&2, List<&2, String>>}
  Rejected{}

# character class: all nullary, so a class is a shared constant, never allocated
type CK is Data:
  CLf{}
  CCr{}
  CSep{}
  CQuote{}
  CText{}

# mode: S = at field start, B = in bare field, E = in escaped field,
# Q = just after a quote in an escaped field; SC/BC/QC = the same with one CR
# held back (it is content only if the next char continues the record).
type FM is Data:
  MS{}
  MB{}
  ME{}
  MQ{}
  MSC{}
  MBC{}
  MQC{}
  MBad{}

def cls_go(+lf: Bool, +cr: Bool, +sep: Bool, +quote: Bool) -> CK:
  match lf:
    case True{}:
      CLf{}
    case False{}:
      match cr:
        case True{}:
          CCr{}
        case False{}:
          match sep:
            case True{}:
              CSep{}
            case False{}:
              match quote:
                case True{}:
                  CQuote{}
                case False{}:
                  CText{}

def cls_u(+sep: U32, +u: U32) -> CK:
  cls_go(U32.is_eq(u, 10), U32.is_eq(u, 13), U32.is_eq(sep, u), U32.is_eq(u, 34))

def cls(+sep: U32, +c: Char) -> CK:
  cls_u(sep, Char.to_u32(c))

def close_empty(+flds: List<&2, String>, +rows: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  match flds:
    case Nil{}:
      rows
    case Con{_, _}:
      Con{List.reverse(&2, String, Con{SNil{}, flds}), rows}

def row(+txt: String, +flds: List<&2, String>, +rows: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  Con{List.reverse(&2, String, Con{txt, flds}), rows}

def one(+c: Char) -> String:
  SCon{c, SNil{}}

def fin(+m: FM, +txt: String, +flds: List<&2, String>, +rows: List<&2, List<&2, String>>) -> Ans:
  match m:
    case MS{}:
      Parsed{List.reverse(&2, List<&2, String>, close_empty(flds, rows))}
    case MSC{}:
      Parsed{List.reverse(&2, List<&2, String>, row(SNil{}, flds, rows))}
    case MB{}:
      Parsed{List.reverse(&2, List<&2, String>, row(txt, flds, rows))}
    case MBC{}:
      Parsed{List.reverse(&2, List<&2, String>, row(txt, flds, rows))}
    case MQ{}:
      Parsed{List.reverse(&2, List<&2, String>, row(txt, flds, rows))}
    case MQC{}:
      Parsed{List.reverse(&2, List<&2, String>, row(txt, flds, rows))}
    case ME{}:
      Rejected{}
    case MBad{}:
      Rejected{}

# class of the first character of a string (CText for the empty string: unused)
def cls_of(+sep: U32, +s: String) -> CK:
  match s:
    case SNil{}:
      CText{}
    case SCon{c, _}:
      cls(sep, c)

# the one walk: input first (it shrinks), then mode, then the class of the head
# character (computed once, by the caller), then everything else. ONE match on
# (input, mode, class) per character; a rejecting pair returns at once.
def go(+s: String, +m: FM, +k: CK, +sep: U32, +txt: String, +flds: List<&2, String>, +rows: List<&2, List<&2, String>>) -> Ans:
  match s m k:
    case SNil{} _ _:
      fin(m, txt, flds, rows)
    case SCon{c, t} MS{} CLf{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, row(SNil{}, flds, rows))
    case SCon{c, t} MS{} CCr{}:
      go(t, MSC{}, cls_of(sep, t), sep, SNil{}, flds, rows)
    case SCon{c, t} MS{} CSep{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Con{SNil{}, flds}, rows)
    case SCon{c, t} MS{} CQuote{}:
      go(t, ME{}, cls_of(sep, t), sep, SNil{}, flds, rows)
    case SCon{c, t} MS{} CText{}:
      go(t, MB{}, cls_of(sep, t), sep, one(c), flds, rows)
    case SCon{c, t} MB{} CLf{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, row(txt, flds, rows))
    case SCon{c, t} MB{} CCr{}:
      go(t, MBC{}, cls_of(sep, t), sep, txt, flds, rows)
    case SCon{c, t} MB{} CSep{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Con{txt, flds}, rows)
    case SCon{_, _} MB{} CQuote{}:
      Rejected{}
    case SCon{c, t} MB{} CText{}:
      go(t, MB{}, cls_of(sep, t), sep, String.append(txt, one(c)), flds, rows)
    case SCon{c, t} ME{} CQuote{}:
      go(t, MQ{}, cls_of(sep, t), sep, txt, flds, rows)
    case SCon{c, t} ME{} CLf{}:
      go(t, ME{}, cls_of(sep, t), sep, String.append(txt, one(Chr{10})), flds, rows)
    case SCon{c, t} ME{} CCr{}:
      go(t, ME{}, cls_of(sep, t), sep, String.append(txt, one(Chr{13})), flds, rows)
    case SCon{c, t} ME{} _:
      go(t, ME{}, cls_of(sep, t), sep, String.append(txt, one(c)), flds, rows)
    case SCon{c, t} MQ{} CLf{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, row(txt, flds, rows))
    case SCon{c, t} MQ{} CCr{}:
      go(t, MQC{}, cls_of(sep, t), sep, txt, flds, rows)
    case SCon{c, t} MQ{} CSep{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Con{txt, flds}, rows)
    case SCon{c, t} MQ{} CQuote{}:
      go(t, ME{}, cls_of(sep, t), sep, String.append(txt, one(Chr{34})), flds, rows)
    case SCon{_, _} MQ{} CText{}:
      Rejected{}
    case SCon{c, t} MSC{} CLf{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, row(SNil{}, flds, rows))
    case SCon{c, t} MSC{} CCr{}:
      go(t, MBC{}, cls_of(sep, t), sep, one(Chr{13}), flds, rows)
    case SCon{c, t} MSC{} CSep{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Con{one(Chr{13}), flds}, rows)
    case SCon{_, _} MSC{} CQuote{}:
      Rejected{}
    case SCon{c, t} MSC{} CText{}:
      go(t, MB{}, cls_of(sep, t), sep, SCon{Chr{13}, one(c)}, flds, rows)
    case SCon{c, t} MBC{} CLf{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, row(txt, flds, rows))
    case SCon{c, t} MBC{} CCr{}:
      go(t, MBC{}, cls_of(sep, t), sep, String.append(txt, one(Chr{13})), flds, rows)
    case SCon{c, t} MBC{} CSep{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Con{String.append(txt, one(Chr{13})), flds}, rows)
    case SCon{_, _} MBC{} CQuote{}:
      Rejected{}
    case SCon{c, t} MBC{} CText{}:
      go(t, MB{}, cls_of(sep, t), sep, String.append(String.append(txt, one(Chr{13})), one(c)), flds, rows)
    case SCon{c, t} MQC{} CLf{}:
      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, row(txt, flds, rows))
    case SCon{_, _} MQC{} _:
      Rejected{}
    case SCon{_, _} MBad{} _:
      Rejected{}

def parse_sep(+sep: U32, +s: String) -> Ans:
  go(s, MS{}, cls_of(sep, s), sep, SNil{}, Nil{}, Nil{})

def parse(+s: String) -> Ans:
  parse_sep(44, s)
