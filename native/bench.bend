import Base
import ../core.bend as A

# The native build of csv-abnf, as a host runs it: `bench <file>` parses the
# file with `A.parse` (the comma) and prints what it got -- records, fields and
# field characters, or that it is not a file -- and the milliseconds the parse
# took. native/scale.ts builds it and measures it on a generated corpus.
#
# The parser has no positions, so a refusal has nothing to print beyond itself.

def fsum(fs: List<&2, String>, +acc: Nat) -> Nat:
  match fs:
    case Nil{}:
      acc
    case f <> t:
      fsum(t, Nat.add(acc, String.length(f)))

def rsum(rs: List<&2, List<&2, String>>, +nr: Nat, +nf: Nat, +nc: Nat) -> String:
  match rs:
    case Nil{}:
      Nat.show(nr) ++ " rows " ++ Nat.show(nf) ++ " fields " ++ Nat.show(nc) ++ " chars"
    case +r <> t:
      rsum(t, Nat.add(nr, 1n), Nat.add(nf, List.length(&2, String, r)), fsum(r, nc))

def report(r: A.Ans) -> String:
  match r:
    case A.Parsed{rows}:
      rsum(rows, 0n, 0n, 0n)
    case A.Rejected{}:
      "not a file 0 rows 0 fields 0 chars"

def path_of(xs: List<&1, String>) -> String:
  match xs:
    case Nil{}:
      "in.csv"
    case p <> t:
      match t:
        case Nil{}:
          "in.csv"
        case q <> u:
          q

def text_of(t: File & Result<&1, &1, U32 & String, String>) -> String:
  (f2, r) = t
  match r:
    case Done{s}:
      s
    case Fail{e}:
      ""

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    f : File <- IO.try(File, File.open(path_of(args), "r"))
    got : File & Result<&1, &1, U32 & String, String> <- File.read(f, 2000000000)
    t0 : Nat <- IO.now()
    line : String = report(A.parse_sep(44, text_of(got)))
    IO.print(line)
    t1 : Nat <- IO.now()
    IO.print("ms " ++ Nat.show(Nat.sub(t1, t0)))
