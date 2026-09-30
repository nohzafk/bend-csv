#!/bin/sh
# What the runtime's thread flag does to this parser, on one file.
#
#   sh native/threads.sh /tmp/some.csv
#
# Not much: the parse is one dependent chain, so there is nothing for a runtime
# to split.
#
# Peak resident set comes from macOS's `time -l`.

F=${1:-/tmp/bend-csv-bench-1mb.csv}
B=$(dirname "$0")/bench

peak() {
  rg -o "[0-9]+ +maximum resident set size" /tmp/t | rg -o "^[0-9]+" | awk '{printf "peak %.0f MB", $1/1048576}'
}
one() {
  label=$1
  shift
  out=$(/usr/bin/time -l "$@" 2>/tmp/t | tail -2 | tr '\n' ' ' | tr -s ' ')
  printf '%-26s %-50s %s\n' "$label" "$out" "$(peak)"
}

echo "input: $F"
one "bend-csv, default"    "$B" "$F"
one "bend-csv, --threads 1"  "$B" --threads 1 "$F"
one "bend-csv, --threads 10" "$B" --threads 10 "$F"
