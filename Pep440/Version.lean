/-
  The version value type, the printer, and the precedence
  comparison, for PEP 440 version identifiers without a local
  version part.

  A version holds an epoch, a release list of numbers, an
  optional pre-release (one of the kinds a, b, rc, with a
  number), an optional post-release number, and an optional
  dev-release number. The spellings a text may use for these
  parts are the parser's business; the value holds the three
  pre-release kinds the ordering uses.
-/

namespace Pep440

/-- A pre-release kind. The texts alpha, a stand for `a`; beta,
    b for `b`; and c, rc, pre, preview for `rc`. -/
inductive PreKind where
  | a
  | b
  | rc
  deriving DecidableEq, Repr

/-- The order of the pre-release kinds: a below b below rc. -/
def PreKind.rank : PreKind → Nat
  | .a => 0
  | .b => 1
  | .rc => 2

/-- The canonical text of a pre-release kind. -/
def PreKind.text : PreKind → List Char
  | .a => ['a']
  | .b => ['b']
  | .rc => ['r', 'c']

/-- A PEP 440 version, without a local part. The release list
    holds at least one number in a well formed version. -/
structure Version where
  epoch : Nat
  release : List Nat
  pre : Option (PreKind × Nat)
  post : Option Nat
  dev : Option Nat
  deriving DecidableEq, Repr

/-- A version is well formed when its release list is not
    empty. Every other part is a number or an optional number,
    and numbers print canonically by construction. -/
def WF (v : Version) : Prop := v.release ≠ []

/-! ## Characters and digits -/

/-- A digit character, as a proposition. -/
def IsDigit (c : Char) : Prop := 48 ≤ c.toNat ∧ c.toNat ≤ 57

/-- A digit character, as a test. -/
def isDigit (c : Char) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

theorem isDigit_iff {c : Char} : isDigit c = true ↔ IsDigit c := by
  simp [isDigit, IsDigit, Bool.and_eq_true]

/-- The separator characters of the grammar: dot, hyphen, and
    underscore. -/
def isSep (c : Char) : Bool := c = '.' || c = '-' || c = '_'

/-- Lowercase one character: an ASCII capital becomes its small
    letter, and every other character stays as it is. The
    spelling words of the grammar are matched case
    insensitively, through this function. -/
def lower (c : Char) : Char :=
  if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then Char.ofNat (c.toNat + 32) else c

/-- The character for a digit value below 10. Any other value
    gives '0'; the lemmas about this function all ask for a value
    below 10. -/
def digitChar : Nat → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | _ => '0'

/-- The digits of a number, least significant first, built with
    fuel so the definition is structural. The top level call gives
    one more fuel than the number, which is always enough: each
    step divides by 10. -/
def digitsRevAux : Nat → Nat → List Nat
  | 0, _ => []
  | _ + 1, 0 => []
  | fuel + 1, n + 1 => (n + 1) % 10 :: digitsRevAux fuel ((n + 1) / 10)

/-- The digits of a number, least significant first. The digits
    of 0 are the empty list; `printNat` handles 0 on its own. -/
def digitsRev (n : Nat) : List Nat := digitsRevAux (n + 1) n

/-- The printed form of a natural number: decimal digits, no
    leading zeros. -/
def printNat (n : Nat) : List Char :=
  if n = 0 then ['0'] else (digitsRev n).reverse.map digitChar

/-- A list of printed parts joined by dots. -/
def joinDots : List (List Char) → List Char
  | [] => []
  | [p] => p
  | p :: ps => p ++ '.' :: joinDots ps

/-! ## Printing -/

/-- The epoch part: the number and a bang, when the epoch is
    above zero; nothing when it is zero. -/
def printEpoch (e : Nat) : List Char :=
  if e = 0 then [] else printNat e ++ ['!']

/-- The release part: the numbers, joined by dots. -/
def printRelease (rel : List Nat) : List Char := joinDots (rel.map printNat)

/-- The pre-release part: a dot, the kind, and the number. -/
def printPre : Option (PreKind × Nat) → List Char
  | none => []
  | some (k, n) => '.' :: (k.text ++ printNat n)

/-- The post-release part: a dot, the word post, and the
    number. -/
def printPost : Option Nat → List Char
  | none => []
  | some n => '.' :: ("post".toList ++ printNat n)

/-- The dev-release part: a dot, the word dev, and the number. -/
def printDev : Option Nat → List Char
  | none => []
  | some n => '.' :: ("dev".toList ++ printNat n)

/-- The canonical text of a version. -/
def print (v : Version) : List Char :=
  printEpoch v.epoch ++ printRelease v.release ++ printPre v.pre ++
    printPost v.post ++ printDev v.dev

/-! ## Precedence, following the ordering key of PEP 440 -/

/-- Three-way comparison of two numbers. -/
def cmpNat (a b : Nat) : Ordering :=
  if a < b then .lt else if b < a then .gt else .eq

/-- Lexicographic comparison of two number lists. When one is
    a prefix of the other, the shorter one is lower. -/
def cmpListNat : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match cmpNat a b with
    | .eq => cmpListNat as bs
    | o => o

/-- A list padded with zeros at the end, up to length `m`. -/
def padZeros (m : Nat) (l : List Nat) : List Nat :=
  l ++ List.replicate (m - l.length) 0

/-- Release segments compare after padding the shorter list
    with zeros, so 1.0 and 1.0.0 compare equal. -/
def cmpRelease (a b : List Nat) : Ordering :=
  let m := max a.length b.length
  cmpListNat (padZeros m a) (padZeros m b)

/-- A key component with a value below all numbers and a value
    above all numbers. -/
inductive Key where
  | negInf
  | num (n : Nat)
  | posInf
  deriving DecidableEq, Repr

/-- Compare two key components. -/
def cmpKey : Key → Key → Ordering
  | .negInf, .negInf => .eq
  | .negInf, _ => .lt
  | _, .negInf => .gt
  | .posInf, .posInf => .eq
  | .posInf, _ => .gt
  | _, .posInf => .lt
  | .num a, .num b => cmpNat a b

/-- The pre-release key component, with a middle form that
    holds a kind rank and a number. -/
inductive PreKey where
  | negInf
  | kind (rank num : Nat)
  | posInf
  deriving DecidableEq, Repr

/-- Compare two pre-release key components. -/
def cmpPreKey : PreKey → PreKey → Ordering
  | .negInf, .negInf => .eq
  | .negInf, _ => .lt
  | _, .negInf => .gt
  | .posInf, .posInf => .eq
  | .posInf, _ => .gt
  | _, .posInf => .lt
  | .kind r₁ n₁, .kind r₂ n₂ =>
    match cmpNat r₁ r₂ with
    | .eq => cmpNat n₁ n₂
    | o => o

/-- The pre-release key of a version. A version with a dev
    number and no pre-release and no post-release sorts before
    everything at its release: its key is the bottom value. A
    version with no pre-release at all sorts after every
    pre-release: its key is the top value. -/
def preKey (v : Version) : PreKey :=
  match v.pre with
  | some (k, n) => .kind k.rank n
  | none => if v.post.isNone && v.dev.isSome then .negInf else .posInf

/-- The post-release key: a missing post sorts before every
    post. -/
def postKey (v : Version) : Key :=
  match v.post with
  | none => .negInf
  | some n => .num n

/-- The dev-release key: a missing dev sorts after every dev. -/
def devKey (v : Version) : Key :=
  match v.dev with
  | none => .posInf
  | some n => .num n

/-- Precedence, as the ordering key of PEP 440 gives it: epoch,
    then the padded release, then the pre, post, and dev keys. -/
def compare (v w : Version) : Ordering :=
  match cmpNat v.epoch w.epoch with
  | .eq =>
    match cmpRelease v.release w.release with
    | .eq =>
      match cmpPreKey (preKey v) (preKey w) with
      | .eq =>
        match cmpKey (postKey v) (postKey w) with
        | .eq => cmpKey (devKey v) (devKey w)
        | o => o
      | o => o
    | o => o
  | o => o

end Pep440
