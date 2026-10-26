/-
  Command line front end, used by the tests.

  Reads one request per line and prints one answer per line. A
  request is an operation and its input as comma-separated
  decimal character codes.

    parse 49,46,48,97,49          prints  ok:49,46,48,46,97,49
    parse 49,46,48,43,49          prints  none
    cmp 49,46,48,59,49,46,48,46,48   prints  eq

  The operations are `parse` and `cmp`.

  `parse` takes the character codes of one version text. Its
  answer is `ok:` and the character codes of the canonical print
  of the parsed version, or `none` when the text is rejected.

  `cmp` takes the codes of two version texts split by one code
  59, the semicolon, which cannot appear in a version text. Its
  answer is `lt`, `eq`, or `gt` for the precedence of the first
  text against the second, or `none` when either text is
  rejected.

  A request is an operation, then optionally one space and its
  numbers; with no numbers after the space, the input is empty. A
  malformed request prints `error`: any other line, an unknown
  operation, a number that is not plain decimal digits, a
  character code that is not a Unicode scalar value, or a `cmp`
  request with no semicolon code in it. A line may end in LF or
  CR LF; nothing else around a request is ignored.

  The parsing, printing, and comparing here call `Pep440.parse`,
  `Pep440.print`, and `Pep440.compare` directly. The line
  handling is covered by the tests, not by a proof.
-/

import Pep440

open Pep440

/-- A number in plain decimal digits. Longer numbers than any
    character code are refused before they are converted, since
    that takes time quadratic in their length. -/
def number (t : String) : Option Nat :=
  let ds := t.toList
  if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
  else t.toNat?

/-- The comma-separated numbers in `s`. -/
def numbers (s : String) : Option (List Nat) :=
  if s.isEmpty then some [] else (s.splitOn ",").mapM number

def toChars (ns : List Nat) : Option (List Char) :=
  ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none

def showCodes (cs : List Char) : String :=
  ",".intercalate (cs.map fun c => toString c.toNat)

/-- Split a character list at its first semicolon. -/
def splitSemi : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs =>
    if c = ';' then some ([], cs)
    else (splitSemi cs).map fun (a, b) => (c :: a, b)

/-- The answer to one request, or `none` when the request is
    malformed. -/
def answer (op : String) (ns : List Nat) : Option String :=
  match op with
  | "parse" =>
    match toChars ns with
    | none => none
    | some cs =>
      match parse cs with
      | some v => some ("ok:" ++ showCodes (print v))
      | none => some "none"
  | "cmp" =>
    match toChars ns with
    | none => none
    | some cs =>
      match splitSemi cs with
      | none => none
      | some (a, b) =>
        match parse a, parse b with
        | some x, some y =>
          some (match compare x y with
            | Ordering.lt => "lt"
            | Ordering.eq => "eq"
            | Ordering.gt => "gt")
        | _, _ => some "none"
  | _ => none

/-- The answer to one line: an operation, then optionally one space
    and its numbers. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | [op] => answer op []
  | [op, arg] => numbers arg >>= answer op
  | _ => none

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := chomp line
    stdout.putStrLn ((request line).getD "error")
