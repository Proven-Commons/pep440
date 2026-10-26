/-
  The parser, reading a PEP 440 version from a list of
  characters. Each reader returns the value it read and the
  characters left over, or `none` when the text breaks the
  grammar. The reader never reads past the end of its input.

  The grammar is read in stages: an optional leading v, the
  epoch, the release, then the pre-release, post-release, and
  dev-release segments in that order. A segment that is not
  there reads as absent and leaves the input untouched; a text
  with anything left over at the end is rejected. A plus sign,
  which would open a local version, is never consumed, so local
  versions are rejected by the end check.
-/

import Pep440.Version

namespace Pep440

/-- The longest run of digit characters at the front of the
    input, and what is left. -/
def takeDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if isDigit c then
      let (a, b) := takeDigits cs
      (c :: a, b)
    else ([], c :: cs)

/-- The value of a list of digit characters, most significant
    first. The caller checks that every character is a digit. -/
def digitsValue (ds : List Char) : Nat :=
  ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0

/-- Read one number: a nonempty run of digits. PEP 440 sets no
    leading zero rule on any number, so 01 reads as 1. -/
def parseNum (cs : List Char) : Option (Nat × List Char) :=
  let (ds, rest) := takeDigits cs
  if ds.isEmpty then none else some (digitsValue ds, rest)

/-- Drop one separator character (dot, hyphen, or underscore)
    from the front, when there is one. -/
def dropSep : List Char → List Char
  | c :: cs => if isSep c then cs else c :: cs
  | [] => []

/-- An optional number behind an optional separator: one
    separator may come first, then digits. With no digits, the
    number is 0 and the input after the separator is returned. -/
def optNum (cs : List Char) : Nat × List Char :=
  let (ds, rest) := takeDigits (dropSep cs)
  (digitsValue ds, rest)

/-- Match a word at the front of the input, case
    insensitively: the word is given in lowercase, and each
    input character is lowered before it is compared. On a
    match, what follows the word is returned. -/
def matchWord : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | _ :: _, [] => none
  | p :: ps, c :: cs => if lower c = p then matchWord ps cs else none

/-- Try a table of words in order, returning the value of the
    first that matches, with what follows it. The order of the
    table carries weight wherever one word is a prefix of
    another: the longer word is tried first. -/
def matchAny : List (List Char × α) → List Char → Option (α × List Char)
  | [], _ => none
  | (pat, val) :: tbl, cs =>
    match matchWord pat cs with
    | some rest => some (val, rest)
    | none => matchAny tbl cs

/-- Try a table of words in order, returning what follows the
    first that matches. -/
def matchAnyPat : List (List Char) → List Char → Option (List Char)
  | [], _ => none
  | pat :: tbl, cs =>
    match matchWord pat cs with
    | some rest => some rest
    | none => matchAnyPat tbl cs

/-- The pre-release spellings, longest first, with the kind
    each one reads as. From PEP 440: alpha reads as a, beta as
    b, and c, pre, and preview all read as rc. -/
def preSpellings : List (List Char × PreKind) :=
  [("alpha".toList, .a), ("beta".toList, .b), ("preview".toList, .rc),
   ("pre".toList, .rc), ("rc".toList, .rc), ("a".toList, .a),
   ("b".toList, .b), ("c".toList, .rc)]

/-- The post-release spellings, longest first. -/
def postSpellings : List (List Char) :=
  ["post".toList, "rev".toList, "r".toList]

/-- Read the epoch: digits and a bang. When the digits are not
    followed by a bang, there is no epoch: the epoch is 0 and
    the input is returned untouched, for the release reader. -/
def parseEpoch (cs : List Char) : Nat × List Char :=
  let (ds, rest) := takeDigits cs
  if ds.isEmpty then (0, cs)
  else if rest.head? = some '!' then (digitsValue ds, rest.tail)
  else (0, cs)

/-- True when the release continues: a dot followed by a digit
    opens another release segment. A dot followed by anything
    else belongs to a later segment. -/
def moreRelease : List Char → Bool
  | '.' :: c :: _ => isDigit c
  | _ => false

/-- Read the release: numbers split by dots. The fuel is found
    by the caller; each segment takes at least one character, so
    the length of the input bounds the count. -/
def parseNumsGo : Nat → List Char → Option (List Nat × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match parseNum cs with
    | none => none
    | some (n, rest) =>
      if moreRelease rest then
        match parseNumsGo fuel rest.tail with
        | some (ns, rest') => some (n :: ns, rest')
        | none => none
      else some ([n], rest)

/-- Read the release, with the input length as fuel. -/
def parseRelease (cs : List Char) : Option (List Nat × List Char) :=
  parseNumsGo (cs.length + 1) cs

/-- Read the pre-release segment. One separator may come
    before the spelling, and an optional number, behind an
    optional separator of its own, may follow it; a missing
    number is 0. When no spelling matches, the segment is
    absent and the input is returned untouched. -/
def parsePre (cs : List Char) : Option (PreKind × Nat) × List Char :=
  match matchAny preSpellings (dropSep cs) with
  | some (k, rest) =>
    let (n, rest') := optNum rest
    (some (k, n), rest')
  | none => (none, cs)

/-- Read the labelled post-release segment: an optional
    separator, one of the spellings post, rev, or r, and an
    optional number defaulting to 0. -/
def parsePostLabeled (cs : List Char) : Option Nat × List Char :=
  match matchAnyPat postSpellings (dropSep cs) with
  | some rest =>
    let (n, rest') := optNum rest
    (some n, rest')
  | none => (none, cs)

/-- Read the post-release segment. The implicit form, a hyphen
    and a number, is tried first; then the labelled forms. When
    neither is there, the segment is absent and the input is
    returned untouched. -/
def parsePost (cs : List Char) : Option Nat × List Char :=
  match cs with
  | '-' :: rest =>
    match rest with
    | c :: _ =>
      if isDigit c then
        match parseNum rest with
        | some (n, rest') => (some n, rest')
        | none => (none, cs)
      else parsePostLabeled cs
    | [] => parsePostLabeled cs
  | _ => parsePostLabeled cs

/-- Read the dev-release segment: an optional separator, the
    word dev, and an optional number defaulting to 0. -/
def parseDev (cs : List Char) : Option Nat × List Char :=
  match matchWord "dev".toList (dropSep cs) with
  | some rest =>
    let (n, rest') := optNum rest
    (some n, rest')
  | none => (none, cs)

/-- Drop a leading v, either case, when there is one. The
    canonical pattern of PEP 440 opens with an optional v; the
    printer never writes one. -/
def stripV (cs : List Char) : List Char :=
  if cs.head? = some 'v' || cs.head? = some 'V' then cs.tail else cs

/-- Read a whole version, returning the version and the
    characters left over. -/
def parseVersion (cs₀ : List Char) : Option (Version × List Char) :=
  let cs := stripV cs₀
  let (e, rest₁) := parseEpoch cs
  (parseRelease rest₁).map fun (rel, rest₂) =>
    let (pre, rest₃) := parsePre rest₂
    let (post, rest₄) := parsePost rest₃
    let (dev, rest₅) := parseDev rest₄
    ({ epoch := e, release := rel, pre := pre, post := post,
       dev := dev }, rest₅)

/-- Parse a version from a character list. Anything after the
    version makes the text rejected, as does any grammar break. -/
def parse (cs : List Char) : Option Version :=
  match parseVersion cs with
  | some (v, []) => some v
  | _ => none

end Pep440
