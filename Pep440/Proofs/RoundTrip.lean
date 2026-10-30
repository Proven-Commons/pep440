/-
  The round trip: parsing the printed form of a well formed
  version gives the version back.

  The proof follows the shape of the printer. Numbers first:
  the digits the printer writes read back to the same number.
  Then the release list, then the three optional segments one
  by one, then the whole version.
-/

import Pep440

namespace Pep440.Proofs

open Pep440

/-! ## Digit characters -/

theorem digitChar_toNat {d : Nat} (h : d < 10) : (digitChar d).toNat = d + 48 := by
  have h9 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨
      d = 8 ∨ d = 9 := by omega
  rcases h9 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem isDigit_digitChar {d : Nat} (h : d < 10) : isDigit (digitChar d) = true := by
  rw [isDigit_iff]
  show 48 ≤ (digitChar d).toNat ∧ (digitChar d).toNat ≤ 57
  rw [digitChar_toNat h]
  constructor <;> omega

/-! ## The digits of a number -/

/-- The value of a list of digits, least significant first. -/
def digitsVal (ds : List Nat) : Nat := ds.foldr (fun d acc => d + 10 * acc) 0

theorem digitsRevAux_zero (f : Nat) : digitsRevAux f 0 = [] := by
  cases f <;> rfl

/-- Everything the printer needs to know about the digit builder,
    in one induction on the fuel: the digits read back to the
    number, every digit is below 10, and a positive number ends
    (at the most significant side) in a nonzero digit. -/
theorem digitsRevAux_spec : ∀ (f n : Nat), n < f →
    digitsVal (digitsRevAux f n) = n ∧
    (∀ d ∈ digitsRevAux f n, d < 10) ∧
    (n = 0 ∨ ∃ ds d, digitsRevAux f n = ds ++ [d] ∧ d ≠ 0) := by
  intro f
  induction f with
  | zero => intro n hn; omega
  | succ f ih =>
    intro n hn
    cases n with
    | zero =>
      have hz : digitsRevAux (f + 1) 0 = [] := digitsRevAux_zero _
      refine ⟨?_, ?_, Or.inl rfl⟩
      · rw [hz]
        rfl
      · intro d hd
        rw [hz] at hd
        simp at hd
    | succ n =>
      have hlt : (n + 1) / 10 < f := by
        by_cases h0 : (n + 1) / 10 = 0
        · omega
        · have h2 : (n + 1) / 10 < n + 1 := Nat.div_lt_self (by omega) (by omega)
          omega
      obtain ⟨hval, hmem, hform⟩ := ih ((n + 1) / 10) hlt
      have hmod : (n + 1) % 10 < 10 := Nat.mod_lt _ (by omega)
      refine ⟨?_, ?_, ?_⟩
      · show digitsVal ((n + 1) % 10 :: digitsRevAux f ((n + 1) / 10)) = n + 1
        show (n + 1) % 10 + 10 * digitsVal (digitsRevAux f ((n + 1) / 10)) = n + 1
        rw [hval]
        have := Nat.div_add_mod (n + 1) 10
        omega
      · intro d hd
        have hd' : d ∈ (n + 1) % 10 :: digitsRevAux f ((n + 1) / 10) := hd
        rcases List.mem_cons.mp hd' with rfl | hd''
        · exact hmod
        · exact hmem d hd''
      · by_cases h0 : (n + 1) / 10 = 0
        · refine Or.inr ⟨[], (n + 1) % 10, ?_, ?_⟩
          · show digitsRevAux (f + 1) (n + 1) = [] ++ [(n + 1) % 10]
            show (n + 1) % 10 :: digitsRevAux f ((n + 1) / 10) = [(n + 1) % 10]
            rw [h0, digitsRevAux_zero]
          · have hlt10 : n + 1 < 10 := by
              rcases Nat.lt_or_ge (n + 1) 10 with hlt | hge
              · exact hlt
              · have hpos := Nat.div_pos hge (by omega : 0 < 10)
                omega
            rw [Nat.mod_eq_of_lt hlt10]
            omega
        · rcases hform with h | ⟨ds, d, hds, hd⟩
          · exact absurd h h0
          · refine Or.inr ⟨(n + 1) % 10 :: ds, d, ?_, hd⟩
            show (n + 1) % 10 :: digitsRevAux f ((n + 1) / 10) =
              ((n + 1) % 10 :: ds) ++ [d]
            rw [hds]
            rfl

/-- The specification of `digitsRev`, from the fuelled builder. -/
theorem digitsRev_spec (n : Nat) :
    digitsVal (digitsRev n) = n ∧
    (∀ d ∈ digitsRev n, d < 10) ∧
    (n = 0 ∨ ∃ ds d, digitsRev n = ds ++ [d] ∧ d ≠ 0) :=
  digitsRevAux_spec (n + 1) n (Nat.lt_succ_self n)

/-! ## Reading digits back -/

/-- Reading a digit list with one more digit at the end: the
    fold multiplies what it had and adds the digit. -/
theorem digitsValue_append_single (ds : List Char) (c : Char) :
    digitsValue (ds ++ [c]) = digitsValue ds * 10 + (c.toNat - 48) := by
  unfold digitsValue
  rw [List.foldl_append]
  rfl

/-- Reading the printed digits of a digit list gives the value of
    the list. Induction on the digit list, least significant
    first: the reversed print puts the head digit last, and the
    fold that reads digits most significant first turns appending
    one digit into a multiply and an add. -/
theorem digitsValue_printDigits : ∀ (ds : List Nat), (∀ d ∈ ds, d < 10) →
    digitsValue (ds.reverse.map digitChar) = digitsVal ds := by
  intro ds
  induction ds with
  | nil => intro _; rfl
  | cons d ds ih =>
    intro hmem
    have hd : d < 10 := hmem d (by simp)
    have hds : ∀ d' ∈ ds, d' < 10 := fun d' hd' => hmem d' (by simp [hd'])
    rw [List.reverse_cons]
    show digitsValue ((ds.reverse ++ [d]).map digitChar) = digitsVal (d :: ds)
    rw [List.map_append, List.map_singleton, digitsValue_append_single, ih hds]
    show digitsVal ds * 10 + ((digitChar d).toNat - 48) = d + 10 * digitsVal ds
    rw [digitChar_toNat hd]
    have h48 : d + 48 - 48 = d := by omega
    rw [h48]
    omega

/-- The printed form of a number reads back to the number. -/
theorem digitsValue_printNat (n : Nat) : digitsValue (printNat n) = n := by
  by_cases h0 : n = 0
  · subst h0
    rfl
  · obtain ⟨hval, hmem, _⟩ := digitsRev_spec n
    have hprint : printNat n = (digitsRev n).reverse.map digitChar := by
      unfold printNat
      rw [if_neg h0]
    rw [hprint, digitsValue_printDigits (digitsRev n) hmem, hval]

/-- Every character the printer writes for a number is a digit. -/
theorem printNat_isDigit {n : Nat} : ∀ c ∈ printNat n, isDigit c = true := by
  by_cases h0 : n = 0
  · subst h0
    intro c hc
    simp [printNat] at hc
    subst hc
    decide
  · obtain ⟨_, hmem, _⟩ := digitsRev_spec n
    intro c hc
    simp [printNat, h0] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    exact isDigit_digitChar (hmem d hd)

/-- The print of a number is never empty. -/
theorem printNat_ne_nil (n : Nat) : printNat n ≠ [] := by
  by_cases h0 : n = 0
  · subst h0
    simp [printNat]
  · obtain ⟨_, _, hform⟩ := digitsRev_spec n
    rcases hform with h | ⟨ds, d, hds, _⟩
    · omega
    · have hprint : printNat n = digitChar d :: (ds.reverse.map digitChar) := by
        unfold printNat
        rw [if_neg h0, hds]
        simp [List.reverse_append]
      rw [hprint]
      simp

/-- A printed number starts with a digit character. -/
theorem printNat_head (n : Nat) :
    ∃ c cs, printNat n = c :: cs ∧ isDigit c = true := by
  cases h : printNat n with
  | nil => exact absurd h (printNat_ne_nil n)
  | cons c cs =>
    exact ⟨c, cs, rfl, printNat_isDigit c (by rw [h]; simp)⟩

/-! ## Taking runs from the front -/

/-- A condition on what follows a printed part: nothing, or a
    character that ends the run. -/
def HeadOk (test : Char → Bool) (rest : List Char) : Prop :=
  match rest with
  | [] => True
  | c :: _ => test c = false

theorem takeDigits_append (ds rest : List Char) (hall : ∀ c ∈ ds, isDigit c = true)
    (h : HeadOk isDigit rest) : takeDigits (ds ++ rest) = (ds, rest) := by
  induction ds with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c cs =>
      have hc : isDigit c = false := h
      show takeDigits (c :: cs) = ([], c :: cs)
      simp [takeDigits, hc]
  | cons d ds ih =>
    have hd : isDigit d = true := hall d (by simp)
    have hds : ∀ c ∈ ds, isDigit c = true := fun c hc => hall c (by simp [hc])
    show takeDigits (d :: (ds ++ rest)) = (d :: ds, rest)
    simp [takeDigits, hd, ih hds]

theorem headOk_dot_digit (r : List Char) : HeadOk isDigit ('.' :: r) := by
  show isDigit '.' = false
  decide

theorem headOk_nil (test : Char → Bool) : HeadOk test [] := trivial

/-! ## Reading printed numbers back -/

/-- A printed number reads back as the number, over any tail
    that does not start with a digit. -/
theorem parseNum_printNat (n : Nat) (rest : List Char) (h : HeadOk isDigit rest) :
    parseNum (printNat n ++ rest) = some (n, rest) := by
  unfold parseNum
  rw [takeDigits_append (printNat n) rest printNat_isDigit h]
  simp [printNat_ne_nil, digitsValue_printNat]

/-- A digit character is never a separator. -/
theorem isSep_digit {c : Char} (h : isDigit c = true) : isSep c = false := by
  have h2 : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := isDigit_iff.mp h
  have hne : ∀ d : Char, d.toNat < 48 ∨ 57 < d.toNat → c ≠ d := by
    intro d hd hcon
    have h3 : c.toNat = d.toNat := congrArg Char.toNat hcon
    omega
  unfold isSep
  simp [hne '.' (by decide), hne '-' (by decide), hne '_' (by decide)]

/-- The separator drop leaves a printed number alone: its first
    character is a digit, not a separator. -/
theorem dropSep_printNat (n : Nat) (rest : List Char) :
    dropSep (printNat n ++ rest) = printNat n ++ rest := by
  obtain ⟨c, cs, hpn, hc⟩ := printNat_head n
  have h1 : printNat n ++ rest = c :: (cs ++ rest) := by rw [hpn]; rfl
  rw [h1]
  simp [dropSep, isSep_digit hc]

/-- The optional number of a segment reads a printed number
    back, over any tail that does not start with a digit. -/
theorem optNum_printNat (n : Nat) (rest : List Char) (h : HeadOk isDigit rest) :
    optNum (printNat n ++ rest) = (n, rest) := by
  unfold optNum
  rw [dropSep_printNat, takeDigits_append (printNat n) rest printNat_isDigit h]
  show (digitsValue (printNat n), rest) = (n, rest)
  rw [digitsValue_printNat]

/-! ## Lowercase matching -/

/-- Lowering a digit character changes nothing: a digit is not
    an ASCII capital. -/
theorem lower_digit {c : Char} (h : isDigit c = true) : lower c = c := by
  have h2 : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := isDigit_iff.mp h
  unfold lower
  rw [if_neg (by omega : ¬ (65 ≤ c.toNat ∧ c.toNat ≤ 90))]

/-- A digit character never lowers to a lowercase letter. -/
theorem lower_ne_of_digit {c : Char} (h : isDigit c = true) {p : Char}
    (hp : 97 ≤ p.toNat) : lower c ≠ p := by
  rw [lower_digit h]
  have h2 : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := isDigit_iff.mp h
  intro hcon
  have h3 : c.toNat = p.toNat := congrArg Char.toNat hcon
  omega

/-- A word match fails at once when its first letter differs
    from the lowered first input character. -/
theorem matchWord_none_of_ne {p : Char} {ps : List Char} {c : Char}
    {cs : List Char} (h : lower c ≠ p) :
    matchWord (p :: ps) (c :: cs) = none := by
  show (if lower c = p then matchWord ps cs else none) = none
  rw [if_neg h]

/-- A word match steps over a matching first character. -/
theorem matchWord_cons_of_eq {p : Char} {ps : List Char} {c : Char}
    {cs : List Char} (h : lower c = p) :
    matchWord (p :: ps) (c :: cs) = matchWord ps cs := by
  show (if lower c = p then matchWord ps cs else none) = matchWord ps cs
  rw [if_pos h]

/-! ## Joined prints -/

/-- A joined list of nonempty parts is at least as long as the
    number of parts, less the dots it saves at the end: the
    length of the join plus one is at least the number of
    parts. -/
theorem joinDots_length : ∀ (ps : List (List Char)), (∀ p ∈ ps, p ≠ []) →
    ps.length ≤ (joinDots ps).length + 1 := by
  intro ps
  induction ps with
  | nil => intro _; exact Nat.zero_le _
  | cons p ps ih =>
    intro hne
    cases ps with
    | nil =>
      show 1 ≤ (joinDots [p]).length + 1
      show 1 ≤ p.length + 1
      omega
    | cons q qs =>
      have ih' := ih (fun x hx => hne x (by simp [hx]))
      have hp : 0 < p.length := by
        cases p with
        | nil => exact absurd rfl (hne _ (by simp))
        | cons c cs => simp
      show (p :: q :: qs).length ≤ (joinDots (p :: q :: qs)).length + 1
      show (q :: qs).length + 1 ≤ (p ++ '.' :: joinDots (q :: qs)).length + 1
      rw [List.length_append]
      simp only [List.length_cons] at ih' ⊢
      omega

/-- The number of release segments is at most the length of
    their joined print, plus the tail. -/
theorem release_length_le (ns : List Nat) (tail : List Char) :
    ns.length ≤ (joinDots (ns.map printNat) ++ tail).length + 1 := by
  rw [List.length_append]
  have h := joinDots_length (ns.map printNat) (by
    intro p hp
    obtain ⟨n, -, rfl⟩ := List.mem_map.mp hp
    exact printNat_ne_nil n)
  simp only [List.length_map] at h
  omega

/-- The separator drop on a dot. -/
theorem dropSep_dot (cs : List Char) : dropSep ('.' :: cs) = cs := by
  show (if isSep '.' then cs else '.' :: cs) = cs
  rw [if_pos (by decide : isSep '.' = true)]

/-! ## The spelling tables on printed words -/

/-- The pre-release table on a printed a segment: the head is
    the letter a and what follows starts with a digit. -/
theorem matchAny_pre_a {c : Char} {cs : List Char} (hc : isDigit c = true) :
    matchAny preSpellings ('a' :: c :: cs) = some (PreKind.a, c :: cs) := by
  have hα : matchWord "alpha".toList ('a' :: c :: cs) = none := by
    have h1 : matchWord "alpha".toList ('a' :: c :: cs)
        = matchWord "lpha".toList (c :: cs) :=
      matchWord_cons_of_eq (by decide : lower 'a' = 'a')
    rw [h1]
    exact matchWord_none_of_ne (lower_ne_of_digit hc (p := 'l') (by decide))
  have hβ : matchWord "beta".toList ('a' :: c :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'a' ≠ 'b')
  have hprev : matchWord "preview".toList ('a' :: c :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'a' ≠ 'p')
  have hpre : matchWord "pre".toList ('a' :: c :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'a' ≠ 'p')
  have hrc : matchWord "rc".toList ('a' :: c :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'a' ≠ 'r')
  have ha : matchWord "a".toList ('a' :: c :: cs) = some (c :: cs) :=
    matchWord_cons_of_eq (by decide : lower 'a' = 'a')
  simp only [preSpellings, matchAny, hα, hβ, hprev, hpre, hrc, ha]

/-- The pre-release table on a printed b segment. -/
theorem matchAny_pre_b {c : Char} {cs : List Char} (hc : isDigit c = true) :
    matchAny preSpellings ('b' :: c :: cs) = some (PreKind.b, c :: cs) := by
  have hα : matchWord "alpha".toList ('b' :: c :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'b' ≠ 'a')
  have hβ : matchWord "beta".toList ('b' :: c :: cs) = none := by
    have h1 : matchWord "beta".toList ('b' :: c :: cs)
        = matchWord "eta".toList (c :: cs) :=
      matchWord_cons_of_eq (by decide : lower 'b' = 'b')
    rw [h1]
    exact matchWord_none_of_ne (lower_ne_of_digit hc (p := 'e') (by decide))
  have hprev : matchWord "preview".toList ('b' :: c :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'b' ≠ 'p')
  have hpre : matchWord "pre".toList ('b' :: c :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'b' ≠ 'p')
  have hrc : matchWord "rc".toList ('b' :: c :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'b' ≠ 'r')
  have ha : matchWord "a".toList ('b' :: c :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'b' ≠ 'a')
  have hb : matchWord "b".toList ('b' :: c :: cs) = some (c :: cs) :=
    matchWord_cons_of_eq (by decide : lower 'b' = 'b')
  simp only [preSpellings, matchAny, hα, hβ, hprev, hpre, hrc, ha, hb]

/-- The pre-release table on a printed rc segment. -/
theorem matchAny_pre_rc {cs : List Char} :
    matchAny preSpellings ('r' :: 'c' :: cs) = some (PreKind.rc, cs) := by
  have hα : matchWord "alpha".toList ('r' :: 'c' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'r' ≠ 'a')
  have hβ : matchWord "beta".toList ('r' :: 'c' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'r' ≠ 'b')
  have hprev : matchWord "preview".toList ('r' :: 'c' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'r' ≠ 'p')
  have hpre : matchWord "pre".toList ('r' :: 'c' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'r' ≠ 'p')
  have hrc : matchWord "rc".toList ('r' :: 'c' :: cs) = some cs := by
    have h1 : matchWord "rc".toList ('r' :: 'c' :: cs)
        = matchWord "c".toList ('c' :: cs) :=
      matchWord_cons_of_eq (by decide : lower 'r' = 'r')
    rw [h1]
    exact matchWord_cons_of_eq (by decide : lower 'c' = 'c')
  simp only [preSpellings, matchAny, hα, hβ, hprev, hpre, hrc]

/-- The pre-release table finds nothing in a printed post word:
    each spelling fails on its first two letters. -/
theorem matchAny_pre_none_po {cs : List Char} :
    matchAny preSpellings ('p' :: 'o' :: cs) = none := by
  have hα : matchWord "alpha".toList ('p' :: 'o' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'p' ≠ 'a')
  have hβ : matchWord "beta".toList ('p' :: 'o' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'p' ≠ 'b')
  have hprev : matchWord "preview".toList ('p' :: 'o' :: cs) = none := by
    have h1 : matchWord "preview".toList ('p' :: 'o' :: cs)
        = matchWord "review".toList ('o' :: cs) :=
      matchWord_cons_of_eq (by decide : lower 'p' = 'p')
    rw [h1]
    exact matchWord_none_of_ne (by decide : lower 'o' ≠ 'r')
  have hpre : matchWord "pre".toList ('p' :: 'o' :: cs) = none := by
    have h1 : matchWord "pre".toList ('p' :: 'o' :: cs)
        = matchWord "re".toList ('o' :: cs) :=
      matchWord_cons_of_eq (by decide : lower 'p' = 'p')
    rw [h1]
    exact matchWord_none_of_ne (by decide : lower 'o' ≠ 'r')
  have hrc : matchWord "rc".toList ('p' :: 'o' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'p' ≠ 'r')
  have ha : matchWord "a".toList ('p' :: 'o' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'p' ≠ 'a')
  have hb : matchWord "b".toList ('p' :: 'o' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'p' ≠ 'b')
  have hc : matchWord "c".toList ('p' :: 'o' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'p' ≠ 'c')
  simp only [preSpellings, matchAny, hα, hβ, hprev, hpre, hrc, ha, hb, hc]

/-- The pre-release table finds nothing at a d: no spelling
    starts with one. -/
theorem matchAny_pre_none_d {cs : List Char} :
    matchAny preSpellings ('d' :: cs) = none := by
  have hα : matchWord "alpha".toList ('d' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'd' ≠ 'a')
  have hβ : matchWord "beta".toList ('d' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'd' ≠ 'b')
  have hprev : matchWord "preview".toList ('d' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'd' ≠ 'p')
  have hpre : matchWord "pre".toList ('d' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'd' ≠ 'p')
  have hrc : matchWord "rc".toList ('d' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'd' ≠ 'r')
  have ha : matchWord "a".toList ('d' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'd' ≠ 'a')
  have hb : matchWord "b".toList ('d' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'd' ≠ 'b')
  have hc : matchWord "c".toList ('d' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'd' ≠ 'c')
  simp only [preSpellings, matchAny, hα, hβ, hprev, hpre, hrc, ha, hb, hc]

/-- The post-release table on a printed post word. -/
theorem matchAnyPat_post {cs : List Char} :
    matchAnyPat postSpellings ('p' :: 'o' :: 's' :: 't' :: cs) = some cs := by
  have hpost : matchWord "post".toList ('p' :: 'o' :: 's' :: 't' :: cs)
      = some cs := by
    have h1 : matchWord "post".toList ('p' :: 'o' :: 's' :: 't' :: cs)
        = matchWord "ost".toList ('o' :: 's' :: 't' :: cs) :=
      matchWord_cons_of_eq (by decide : lower 'p' = 'p')
    rw [h1]
    have h2 : matchWord "ost".toList ('o' :: 's' :: 't' :: cs)
        = matchWord "st".toList ('s' :: 't' :: cs) :=
      matchWord_cons_of_eq (by decide : lower 'o' = 'o')
    rw [h2]
    have h3 : matchWord "st".toList ('s' :: 't' :: cs)
        = matchWord "t".toList ('t' :: cs) :=
      matchWord_cons_of_eq (by decide : lower 's' = 's')
    rw [h3]
    exact matchWord_cons_of_eq (by decide : lower 't' = 't')
  simp only [postSpellings, matchAnyPat, hpost]

/-- The post-release table finds nothing at a d. -/
theorem matchAnyPat_none_d {cs : List Char} :
    matchAnyPat postSpellings ('d' :: cs) = none := by
  have hpost : matchWord "post".toList ('d' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'd' ≠ 'p')
  have hrev : matchWord "rev".toList ('d' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'd' ≠ 'r')
  have hr : matchWord "r".toList ('d' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower 'd' ≠ 'r')
  simp only [postSpellings, matchAnyPat, hpost, hrev, hr]

/-- The dev word matches itself. -/
theorem matchWord_dev {cs : List Char} :
    matchWord "dev".toList ('d' :: 'e' :: 'v' :: cs) = some cs := by
  have h1 : matchWord "dev".toList ('d' :: 'e' :: 'v' :: cs)
      = matchWord "ev".toList ('e' :: 'v' :: cs) :=
    matchWord_cons_of_eq (by decide : lower 'd' = 'd')
  rw [h1]
  have h2 : matchWord "ev".toList ('e' :: 'v' :: cs)
      = matchWord "v".toList ('v' :: cs) :=
    matchWord_cons_of_eq (by decide : lower 'e' = 'e')
  rw [h2]
  exact matchWord_cons_of_eq (by decide : lower 'v' = 'v')

/-! ## Reading the printed release back -/

/-- A dot in front of a printed release list means the release
    continues: the next character is the first digit of the
    next printed number. -/
theorem moreRelease_dot_print (ns : List Nat) (hne : ns ≠ [])
    (rest : List Char) :
    moreRelease ('.' :: (joinDots (ns.map printNat) ++ rest)) = true := by
  cases ns with
  | nil => exact absurd rfl hne
  | cons n ns' =>
    obtain ⟨c, cs, hpn, hc⟩ := printNat_head n
    cases ns' with
    | nil =>
      show moreRelease ('.' :: (printNat n ++ rest)) = true
      rw [hpn]
      show isDigit c = true
      exact hc
    | cons m ns'' =>
      show moreRelease
          ('.' :: ((printNat n ++ '.' :: joinDots ((m :: ns'').map printNat)) ++ rest)) = true
      rw [List.append_assoc, hpn]
      show isDigit c = true
      exact hc

/-- A printed release reads back. The tail after it must not
    start with a digit, and must not continue the release: a
    dot after it never opens another number. Induction on the
    fuel. -/
theorem parseNumsGo_print : ∀ (fuel : Nat) (ns : List Nat) (rest : List Char),
    ns ≠ [] → HeadOk isDigit rest → moreRelease rest = false →
    ns.length ≤ fuel →
    parseNumsGo fuel (joinDots (ns.map printNat) ++ rest) = some (ns, rest) := by
  intro fuel
  induction fuel with
  | zero =>
    intro ns rest hne _ _ hlen
    cases ns with
    | nil => exact absurd rfl hne
    | cons n ns => simp at hlen
  | succ f ih =>
    intro ns rest hne hok hmr hlen
    cases ns with
    | nil => exact absurd rfl hne
    | cons n ns' =>
      cases ns' with
      | nil =>
        show parseNumsGo (f + 1) (printNat n ++ rest) = some ([n], rest)
        show (match parseNum (printNat n ++ rest) with
          | none => none
          | some (m, rest') =>
            if moreRelease rest' then
              match parseNumsGo f rest'.tail with
              | some (ms, rest'') => some (m :: ms, rest'')
              | none => none
            else some ([m], rest')) = some ([n], rest)
        rw [parseNum_printNat n rest hok]
        show (if moreRelease rest then
            match parseNumsGo f rest.tail with
            | some (ms, rest'') => some (n :: ms, rest'')
            | none => none
          else some ([n], rest)) = some ([n], rest)
        rw [if_neg (by simp [hmr] : ¬ (moreRelease rest = true))]
      | cons n₂ ns'' =>
        show parseNumsGo (f + 1)
            ((printNat n ++ '.' :: joinDots ((n₂ :: ns'').map printNat)) ++ rest) =
          some (n :: n₂ :: ns'', rest)
        rw [List.append_assoc]
        show (match parseNum
            (printNat n ++ ('.' :: (joinDots ((n₂ :: ns'').map printNat) ++ rest))) with
          | none => none
          | some (m, rest') =>
            if moreRelease rest' then
              match parseNumsGo f rest'.tail with
              | some (ms, rest'') => some (m :: ms, rest'')
              | none => none
            else some ([m], rest')) = some (n :: n₂ :: ns'', rest)
        rw [parseNum_printNat n _ (headOk_dot_digit _)]
        show (if moreRelease ('.' :: (joinDots ((n₂ :: ns'').map printNat) ++ rest)) then
            match parseNumsGo f
                ('.' :: (joinDots ((n₂ :: ns'').map printNat) ++ rest)).tail with
            | some (ms, rest'') => some (n :: ms, rest'')
            | none => none
          else some ([n], '.' :: (joinDots ((n₂ :: ns'').map printNat) ++ rest))) =
          some (n :: n₂ :: ns'', rest)
        rw [if_pos (moreRelease_dot_print (n₂ :: ns'') (by simp) _)]
        show (match parseNumsGo f (joinDots ((n₂ :: ns'').map printNat) ++ rest) with
          | some (ms, rest'') => some (n :: ms, rest'')
          | none => none) = some (n :: n₂ :: ns'', rest)
        rw [ih (n₂ :: ns'') rest (by simp) hok hmr (by simp at hlen; omega)]

/-- The release reader on a printed release, with a tail
    behind it. -/
theorem parseRelease_print (ns : List Nat) (hne : ns ≠ []) (suffix : List Char)
    (hok : HeadOk isDigit suffix) (hmr : moreRelease suffix = false) :
    parseRelease (printRelease ns ++ suffix) = some (ns, suffix) := by
  show parseNumsGo ((printRelease ns ++ suffix).length + 1)
      (printRelease ns ++ suffix) = some (ns, suffix)
  exact parseNumsGo_print _ ns suffix hne hok hmr (release_length_le ns suffix)

/-! ## Reading the printed epoch back -/

theorem headOk_bang (r : List Char) : HeadOk isDigit ('!' :: r) := by
  show isDigit '!' = false
  decide

/-- With no epoch in the print, the epoch reader takes the
    first printed number's digits, finds no bang, and gives
    the whole text back with epoch 0. -/
theorem parseEpoch_zero {n : Nat} {rest : List Char} (hok : HeadOk isDigit rest)
    (hbang : rest.head? ≠ some '!') :
    parseEpoch (printNat n ++ rest) = (0, printNat n ++ rest) := by
  show (let (ds, rest') := takeDigits (printNat n ++ rest);
    if ds.isEmpty then (0, printNat n ++ rest)
    else if rest'.head? = some '!' then (digitsValue ds, rest'.tail)
    else (0, printNat n ++ rest)) = (0, printNat n ++ rest)
  rw [takeDigits_append (printNat n) rest printNat_isDigit hok]
  show (if (printNat n).isEmpty then (0, printNat n ++ rest)
    else if rest.head? = some '!' then (digitsValue (printNat n), rest.tail)
    else (0, printNat n ++ rest)) = (0, printNat n ++ rest)
  rw [if_neg (by rw [List.isEmpty_iff]; exact printNat_ne_nil n :
      ¬ ((printNat n).isEmpty = true)), if_neg hbang]

/-- A printed epoch reads back: the digits, the bang, and then
    the rest of the text untouched. -/
theorem parseEpoch_pos {e : Nat} {rest : List Char} :
    parseEpoch (printNat e ++ ('!' :: rest)) = (e, rest) := by
  show (let (ds, rest') := takeDigits (printNat e ++ ('!' :: rest));
    if ds.isEmpty then (0, printNat e ++ ('!' :: rest))
    else if rest'.head? = some '!' then (digitsValue ds, rest'.tail)
    else (0, printNat e ++ ('!' :: rest))) = (e, rest)
  rw [takeDigits_append (printNat e) _ printNat_isDigit (headOk_bang _)]
  show (if (printNat e).isEmpty then (0, printNat e ++ ('!' :: rest))
    else if (('!' :: rest).head? = some '!') then
      (digitsValue (printNat e), ('!' :: rest).tail)
    else (0, printNat e ++ ('!' :: rest))) = (e, rest)
  have hbang : ('!' :: rest).head? = some '!' := rfl
  rw [if_neg (by rw [List.isEmpty_iff]; exact printNat_ne_nil e :
      ¬ ((printNat e).isEmpty = true)), if_pos hbang, digitsValue_printNat]
  rfl

/-- The epoch reader on a printed release with no epoch: it
    takes the first number's digits, finds no bang behind
    them, and gives the whole text back with epoch 0. -/
theorem parseEpoch_release {rel : List Nat} (hne : rel ≠ []) (suffix : List Char)
    (hok : HeadOk isDigit suffix) (hbang : suffix.head? ≠ some '!') :
    parseEpoch (printRelease rel ++ suffix) = (0, printRelease rel ++ suffix) := by
  cases rel with
  | nil => exact absurd rfl hne
  | cons n ns =>
    cases ns with
    | nil =>
      show parseEpoch (printNat n ++ suffix) = (0, printNat n ++ suffix)
      exact parseEpoch_zero hok hbang
    | cons m ns' =>
      show parseEpoch ((printNat n ++ '.' :: joinDots ((m :: ns').map printNat)) ++ suffix)
          = (0, (printNat n ++ '.' :: joinDots ((m :: ns').map printNat)) ++ suffix)
      rw [List.append_assoc]
      have hh : ((('.' :: joinDots ((m :: ns').map printNat)) ++ suffix).head?
          = some '.') := rfl
      have hbang' : ((('.' :: joinDots ((m :: ns').map printNat)) ++ suffix).head?
          ≠ some '!') := by
        rw [hh]
        exact fun h => (by decide : ('.' : Char) ≠ '!') (Option.some.inj h)
      exact parseEpoch_zero (headOk_dot_digit _) hbang'

/-! ## Reading the printed tail segments back -/

/-- A printed pre-release reads back: the spelling table
    finds the printed spelling, and the printed number
    follows it. -/
theorem parsePre_printPre (k : PreKind) (n : Nat) (tail : List Char)
    (hok : HeadOk isDigit tail) :
    parsePre (printPre (some (k, n)) ++ tail) = (some (k, n), tail) := by
  cases k with
  | a =>
    obtain ⟨c, cs, hpn, hc⟩ := printNat_head n
    show parsePre ('.' :: ('a' :: (printNat n ++ tail)))
        = (some (PreKind.a, n), tail)
    show (match matchAny preSpellings (dropSep ('.' :: ('a' :: (printNat n ++ tail)))) with
      | some (k, rest) => let (n, rest') := optNum rest; (some (k, n), rest')
      | none => (none, '.' :: ('a' :: (printNat n ++ tail))))
        = (some (PreKind.a, n), tail)
    rw [dropSep_dot, hpn, List.cons_append, matchAny_pre_a hc]
    show (let (n', rest') := optNum (c :: (cs ++ tail));
        (some (PreKind.a, n'), rest')) = (some (PreKind.a, n), tail)
    rw [← List.cons_append, ← hpn, optNum_printNat n tail hok]
  | b =>
    obtain ⟨c, cs, hpn, hc⟩ := printNat_head n
    show parsePre ('.' :: ('b' :: (printNat n ++ tail)))
        = (some (PreKind.b, n), tail)
    show (match matchAny preSpellings (dropSep ('.' :: ('b' :: (printNat n ++ tail)))) with
      | some (k, rest) => let (n, rest') := optNum rest; (some (k, n), rest')
      | none => (none, '.' :: ('b' :: (printNat n ++ tail))))
        = (some (PreKind.b, n), tail)
    rw [dropSep_dot, hpn, List.cons_append, matchAny_pre_b hc]
    show (let (n', rest') := optNum (c :: (cs ++ tail));
        (some (PreKind.b, n'), rest')) = (some (PreKind.b, n), tail)
    rw [← List.cons_append, ← hpn, optNum_printNat n tail hok]
  | rc =>
    show parsePre ('.' :: ('r' :: 'c' :: (printNat n ++ tail)))
        = (some (PreKind.rc, n), tail)
    show (match matchAny preSpellings (dropSep ('.' :: ('r' :: 'c' :: (printNat n ++ tail)))) with
      | some (k, rest) => let (n, rest') := optNum rest; (some (k, n), rest')
      | none => (none, '.' :: ('r' :: 'c' :: (printNat n ++ tail))))
        = (some (PreKind.rc, n), tail)
    rw [dropSep_dot, matchAny_pre_rc]
    show (let (n', rest') := optNum (printNat n ++ tail);
        (some (PreKind.rc, n'), rest')) = (some (PreKind.rc, n), tail)
    rw [optNum_printNat n tail hok]

/-- With a post word next, the pre-release reader finds no
    spelling and gives the text back. -/
theorem parsePre_none_po {cs : List Char} :
    parsePre ('.' :: 'p' :: 'o' :: cs) = (none, '.' :: 'p' :: 'o' :: cs) := by
  show (match matchAny preSpellings (dropSep ('.' :: 'p' :: 'o' :: cs)) with
    | some (k, rest) => let (n, rest') := optNum rest; (some (k, n), rest')
    | none => (none, '.' :: 'p' :: 'o' :: cs)) = (none, '.' :: 'p' :: 'o' :: cs)
  rw [dropSep_dot, matchAny_pre_none_po]

/-- With a dev word next, the pre-release reader finds no
    spelling and gives the text back. -/
theorem parsePre_none_d {cs : List Char} :
    parsePre ('.' :: 'd' :: cs) = (none, '.' :: 'd' :: cs) := by
  show (match matchAny preSpellings (dropSep ('.' :: 'd' :: cs)) with
    | some (k, rest) => let (n, rest') := optNum rest; (some (k, n), rest')
    | none => (none, '.' :: 'd' :: cs)) = (none, '.' :: 'd' :: cs)
  rw [dropSep_dot, matchAny_pre_none_d]

/-- On empty text the pre-release reader finds nothing. -/
theorem parsePre_none_nil : parsePre [] = (none, []) := by decide

/-- A printed post-release reads back. -/
theorem parsePost_printPost (n : Nat) (tail : List Char) (hok : HeadOk isDigit tail) :
    parsePost (printPost (some n) ++ tail) = (some n, tail) := by
  show parsePost ('.' :: 'p' :: 'o' :: 's' :: 't' :: (printNat n ++ tail))
      = (some n, tail)
  show (match matchAnyPat postSpellings
      (dropSep ('.' :: 'p' :: 'o' :: 's' :: 't' :: (printNat n ++ tail))) with
    | some rest => let (m, rest') := optNum rest; (some m, rest')
    | none => (none, '.' :: 'p' :: 'o' :: 's' :: 't' :: (printNat n ++ tail)))
      = (some n, tail)
  rw [dropSep_dot, matchAnyPat_post]
  show (let (m, rest') := optNum (printNat n ++ tail); (some m, rest'))
      = (some n, tail)
  rw [optNum_printNat n tail hok]

/-- With a dev word next, the post-release reader finds no
    spelling and gives the text back. -/
theorem parsePost_none_d {cs : List Char} :
    parsePost ('.' :: 'd' :: cs) = (none, '.' :: 'd' :: cs) := by
  show (match matchAnyPat postSpellings (dropSep ('.' :: 'd' :: cs)) with
    | some rest => let (m, rest') := optNum rest; (some m, rest')
    | none => (none, '.' :: 'd' :: cs)) = (none, '.' :: 'd' :: cs)
  rw [dropSep_dot, matchAnyPat_none_d]

/-- On empty text the post-release reader finds nothing: an
    empty text does not start with a dash either. -/
theorem parsePost_none_nil : parsePost [] = (none, []) := by decide

/-- A printed dev-release reads back. -/
theorem parseDev_printDev (n : Nat) (tail : List Char) (hok : HeadOk isDigit tail) :
    parseDev (printDev (some n) ++ tail) = (some n, tail) := by
  show parseDev ('.' :: 'd' :: 'e' :: 'v' :: (printNat n ++ tail)) = (some n, tail)
  show (match matchWord "dev".toList
      (dropSep ('.' :: 'd' :: 'e' :: 'v' :: (printNat n ++ tail))) with
    | some rest => let (m, rest') := optNum rest; (some m, rest')
    | none => (none, '.' :: 'd' :: 'e' :: 'v' :: (printNat n ++ tail))) = (some n, tail)
  rw [dropSep_dot, matchWord_dev]
  show (let (m, rest') := optNum (printNat n ++ tail); (some m, rest'))
      = (some n, tail)
  rw [optNum_printNat n tail hok]

/-- A printed dev-release at the very end of the text reads
    back. -/
theorem parseDev_printDev_last (n : Nat) :
    parseDev (printDev (some n)) = (some n, []) := by
  have h := parseDev_printDev n [] (headOk_nil (test := isDigit))
  rwa [List.append_nil] at h

/-- On empty text the dev-release reader finds nothing. -/
theorem parseDev_none_nil : parseDev [] = (none, []) := by decide

/-! ## Reading the printed local part back -/

/-- A digit character is a letter-or-digit character. -/
theorem isAlnum_of_isDigit {c : Char} (h : isDigit c = true) : isAlnum c = true := by
  show (isDigit c || isAlpha c) = true
  simp [h]

/-- A lowercase letter is not a digit: their code ranges do
    not meet. -/
theorem isDigit_false_of_isLetter {c : Char} (h : isLetter c = true) :
    isDigit c = false := by
  cases hd : isDigit c with
  | false => rfl
  | true =>
    exfalso
    have h2 : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := isDigit_iff.mp hd
    have hh : ((97 ≤ c.toNat) && (c.toNat ≤ 122)) = true := h
    rw [Bool.and_eq_true] at hh
    have h97 : 97 ≤ c.toNat := of_decide_eq_true hh.1
    omega

/-- Lowering a lowercase letter changes nothing: a letter is
    not an ASCII capital. -/
theorem lower_of_isLetter {c : Char} (h : isLetter c = true) : lower c = c := by
  have hh : ((97 ≤ c.toNat) && (c.toNat ≤ 122)) = true := h
  rw [Bool.and_eq_true] at hh
  have h97 : 97 ≤ c.toNat := of_decide_eq_true hh.1
  unfold lower
  rw [if_neg (by omega : ¬ (65 ≤ c.toNat ∧ c.toNat ≤ 90))]

/-- Lowering a character of a held text segment changes
    nothing: the character is a digit or a lowercase letter,
    and neither is an ASCII capital. -/
theorem lower_of_isLowerAlnum {c : Char} (h : isLowerAlnum c = true) :
    lower c = c := by
  have hh : (isDigit c || isLetter c) = true := h
  rw [Bool.or_eq_true] at hh
  rcases hh with hd | hl
  · exact lower_digit hd
  · exact lower_of_isLetter hl

/-- A character held in a text segment is a letter-or-digit
    character. -/
theorem isAlnum_of_isLowerAlnum {c : Char} (h : isLowerAlnum c = true) :
    isAlnum c = true := by
  have hh : (isDigit c || isLetter c) = true := h
  rw [Bool.or_eq_true] at hh
  rcases hh with hd | hl
  · exact isAlnum_of_isDigit hd
  · show (isDigit c || isAlpha c) = true
    have ha : isAlpha c = true := by
      show ((65 ≤ c.toNat && c.toNat ≤ 90) || isLetter c) = true
      simp [hl]
    simp [ha]

/-- Every character of a list passes a test, so the `all` of
    the test passes. -/
theorem all_true_of_forall {p : Char → Bool} {cs : List Char}
    (h : ∀ c ∈ cs, p c = true) : cs.all p = true := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    show (p c && cs.all p) = true
    rw [h c (by simp), ih (fun x hx => h x (by simp [hx])), Bool.and_true]

/-- One character of a list fails a test, so the `all` of the
    test fails. -/
theorem all_false_of_mem {p : Char → Bool} {cs : List Char} {c : Char}
    (hmem : c ∈ cs) (hc : p c = false) : cs.all p = false := by
  induction cs with
  | nil => simp at hmem
  | cons x xs ih =>
    show (p x && xs.all p) = false
    rcases List.mem_cons.mp hmem with rfl | hxs
    · rw [hc, Bool.false_and]
    · rw [ih hxs, Bool.and_false]

/-- Lowering every character of a list whose characters all
    lower to themselves gives the list back. -/
theorem map_lower_of_forall {cs : List Char} (h : ∀ c ∈ cs, lower c = c) :
    cs.map lower = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    show lower c :: cs.map lower = c :: cs
    rw [h c (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- A dot in front of a run ends the run: a dot is not a
    letter or a digit. -/
theorem headOk_dot_alnum (r : List Char) : HeadOk isAlnum ('.' :: r) := by
  show isAlnum '.' = false
  decide

/-- A letter-or-digit run reads a printed list of such
    characters back, over any tail that does not start with
    one. -/
theorem takeAlnum_append (ds rest : List Char)
    (hall : ∀ c ∈ ds, isAlnum c = true) (h : HeadOk isAlnum rest) :
    takeAlnum (ds ++ rest) = (ds, rest) := by
  induction ds with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c cs =>
      have hc : isAlnum c = false := h
      show takeAlnum (c :: cs) = ([], c :: cs)
      simp [takeAlnum, hc]
  | cons d ds ih =>
    have hd : isAlnum d = true := hall d (by simp)
    have hds : ∀ c ∈ ds, isAlnum c = true := fun c hc => hall c (by simp [hc])
    show takeAlnum (d :: (ds ++ rest)) = (d :: ds, rest)
    simp [takeAlnum, hd, ih hds]

/-- A printed segment reads back as the segment, over any
    tail that does not start with a letter or a digit. -/
theorem parseLocalSeg_print (s : LocalSeg) (hs : LocalSeg.WF s)
    (rest : List Char) (hok : HeadOk isAlnum rest) :
    parseLocalSeg (printLocalSeg s ++ rest) = some (s, rest) := by
  cases s with
  | num n =>
    show parseLocalSeg (printNat n ++ rest) = some (LocalSeg.num n, rest)
    unfold parseLocalSeg
    rw [takeAlnum_append (printNat n) rest
      (fun c hc => isAlnum_of_isDigit (printNat_isDigit c hc)) hok]
    show (if (printNat n).isEmpty then none
      else if (printNat n).all isDigit then
        some (LocalSeg.num (digitsValue (printNat n)), rest)
      else some (LocalSeg.str ((printNat n).map lower), rest))
      = some (LocalSeg.num n, rest)
    rw [if_neg (by rw [List.isEmpty_iff]; exact printNat_ne_nil n :
        ¬ ((printNat n).isEmpty = true)),
      if_pos (all_true_of_forall printNat_isDigit), digitsValue_printNat]
  | str cs =>
    obtain ⟨hne, halnum, c₀, hc₀mem, hc₀letter⟩ := hs
    have hnotall : ¬ (cs.all isDigit = true) := by
      have hf : cs.all isDigit = false :=
        all_false_of_mem hc₀mem (isDigit_false_of_isLetter hc₀letter)
      rw [hf]
      decide
    show parseLocalSeg (cs ++ rest) = some (LocalSeg.str cs, rest)
    unfold parseLocalSeg
    rw [takeAlnum_append cs rest
      (fun c hc => isAlnum_of_isLowerAlnum (halnum c hc)) hok]
    show (if cs.isEmpty then none
      else if cs.all isDigit then
        some (LocalSeg.num (digitsValue cs), rest)
      else some (LocalSeg.str (cs.map lower), rest))
      = some (LocalSeg.str cs, rest)
    rw [if_neg (by rw [List.isEmpty_iff]; exact hne :
        ¬ (cs.isEmpty = true)), if_neg hnotall,
      map_lower_of_forall (fun c hc => lower_of_isLowerAlnum (halnum c hc))]

/-- What the segment reader needs from what stands after a
    printed local part: nothing, or a first character that is
    neither a separator (which would make the reader read
    another segment) nor a letter or digit (which the last
    segment's run would swallow). -/
def SegEndOk (rest : List Char) : Prop :=
  match rest with
  | [] => True
  | c :: _ => isSep c = false ∧ isAlnum c = false

theorem segEndOk_nil : SegEndOk [] := trivial

theorem SegEndOk.headOk {rest : List Char} (h : SegEndOk rest) :
    HeadOk isAlnum rest := by
  cases rest with
  | nil => exact trivial
  | cons c cs => exact h.2

/-- The printed form of a segment is never empty. -/
theorem printLocalSeg_ne_nil (s : LocalSeg) (hs : LocalSeg.WF s) :
    printLocalSeg s ≠ [] := by
  cases s with
  | num n => exact printNat_ne_nil n
  | str cs => exact hs.1

/-- The number of local segments is at most the length of
    their joined print, plus the tail. -/
theorem local_length_le (segs : List LocalSeg)
    (hwf : ∀ s ∈ segs, LocalSeg.WF s) (tail : List Char) :
    segs.length ≤ (joinDots (segs.map printLocalSeg) ++ tail).length + 1 := by
  rw [List.length_append]
  have h := joinDots_length (segs.map printLocalSeg) (by
    intro p hp
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
    exact printLocalSeg_ne_nil s (hwf s hs))
  simp only [List.length_map] at h
  omega

/-- Printed local segments read back. Induction on the fuel,
    in the shape of the release reader's proof. -/
theorem parseLocalGo_print : ∀ (fuel : Nat) (segs : List LocalSeg)
    (rest : List Char), segs ≠ [] → (∀ s ∈ segs, LocalSeg.WF s) →
    SegEndOk rest → segs.length ≤ fuel →
    parseLocalGo fuel (joinDots (segs.map printLocalSeg) ++ rest)
      = some (segs, rest) := by
  intro fuel
  induction fuel with
  | zero =>
    intro segs rest hne _ _ hlen
    cases segs with
    | nil => exact absurd rfl hne
    | cons s ss => simp at hlen
  | succ f ih =>
    intro segs rest hne hwf hok hlen
    cases segs with
    | nil => exact absurd rfl hne
    | cons s ss =>
      cases ss with
      | nil =>
        show parseLocalGo (f + 1) (printLocalSeg s ++ rest) = some ([s], rest)
        show (match parseLocalSeg (printLocalSeg s ++ rest) with
          | none => none
          | some (t, rest') =>
            match rest' with
            | [] => some ([t], [])
            | c :: rest'' =>
              if isSep c then
                match parseLocalGo f rest'' with
                | some (ts, r) => some (t :: ts, r)
                | none => none
              else some ([t], c :: rest'')) = some ([s], rest)
        rw [parseLocalSeg_print s (hwf s (by simp)) rest hok.headOk]
        cases rest with
        | nil => rfl
        | cons c cs =>
          have hc : isSep c = false := hok.1
          show (if isSep c then
              match parseLocalGo f cs with
              | some (ts, r) => some (s :: ts, r)
              | none => none
            else some ([s], c :: cs)) = some ([s], c :: cs)
          rw [if_neg (by simp [hc] : ¬ (isSep c = true))]
      | cons s₂ ss' =>
        show parseLocalGo (f + 1)
            ((printLocalSeg s ++ '.' :: joinDots ((s₂ :: ss').map printLocalSeg))
              ++ rest) = some (s :: s₂ :: ss', rest)
        rw [List.append_assoc]
        show (match parseLocalSeg
            (printLocalSeg s ++ ('.' :: (joinDots ((s₂ :: ss').map printLocalSeg)
              ++ rest))) with
          | none => none
          | some (t, rest') =>
            match rest' with
            | [] => some ([t], [])
            | c :: rest'' =>
              if isSep c then
                match parseLocalGo f rest'' with
                | some (ts, r) => some (t :: ts, r)
                | none => none
              else some ([t], c :: rest'')) = some (s :: s₂ :: ss', rest)
        rw [parseLocalSeg_print s (hwf s (by simp)) _
          (headOk_dot_alnum _)]
        show (if isSep '.' then
            match parseLocalGo f (joinDots ((s₂ :: ss').map printLocalSeg)
              ++ rest) with
            | some (ts, r) => some (s :: ts, r)
            | none => none
          else some ([s], '.' :: (joinDots ((s₂ :: ss').map printLocalSeg)
            ++ rest))) = some (s :: s₂ :: ss', rest)
        rw [if_pos (by decide : isSep '.' = true),
          ih (s₂ :: ss') rest (by simp) (fun x hx => hwf x (by simp [hx])) hok
            (by simp at hlen; omega)]

/-- A printed local part reads back, with nothing left over. -/
theorem parseLocal_print (loc : Option (List LocalSeg))
    (h : LocalOptWF loc) : parseLocal (printLocal loc) = (loc, []) := by
  cases loc with
  | none => rfl
  | some segs =>
    obtain ⟨hne, hwf⟩ := h
    have hlen : segs.length ≤ (joinDots (segs.map printLocalSeg)).length + 1 := by
      have h := local_length_le segs hwf []
      rwa [List.append_nil] at h
    have hgo := parseLocalGo_print
      ((joinDots (segs.map printLocalSeg)).length + 1) segs [] hne hwf
      segEndOk_nil hlen
    rw [List.append_nil] at hgo
    show (match parseLocalGo ((joinDots (segs.map printLocalSeg)).length + 1)
        (joinDots (segs.map printLocalSeg)) with
      | some (ss, r) => (some ss, r)
      | none => (none, '+' :: joinDots (segs.map printLocalSeg)))
      = (some segs, [])
    rw [hgo]

/-- The separator drop on a plus. -/
theorem dropSep_plus (cs : List Char) : dropSep ('+' :: cs) = '+' :: cs := by
  show (if isSep '+' then cs else '+' :: cs) = '+' :: cs
  rw [if_neg (by decide : ¬ (isSep '+' = true))]

/-- The pre-release table finds nothing at a plus: no spelling
    starts with one. -/
theorem matchAny_pre_none_plus {cs : List Char} :
    matchAny preSpellings ('+' :: cs) = none := by
  have hα : matchWord "alpha".toList ('+' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower '+' ≠ 'a')
  have hβ : matchWord "beta".toList ('+' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower '+' ≠ 'b')
  have hprev : matchWord "preview".toList ('+' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower '+' ≠ 'p')
  have hpre : matchWord "pre".toList ('+' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower '+' ≠ 'p')
  have hrc : matchWord "rc".toList ('+' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower '+' ≠ 'r')
  have ha : matchWord "a".toList ('+' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower '+' ≠ 'a')
  have hb : matchWord "b".toList ('+' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower '+' ≠ 'b')
  have hc : matchWord "c".toList ('+' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower '+' ≠ 'c')
  simp only [preSpellings, matchAny, hα, hβ, hprev, hpre, hrc, ha, hb, hc]

/-- The post-release table finds nothing at a plus. -/
theorem matchAnyPat_none_plus {cs : List Char} :
    matchAnyPat postSpellings ('+' :: cs) = none := by
  have hpost : matchWord "post".toList ('+' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower '+' ≠ 'p')
  have hrev : matchWord "rev".toList ('+' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower '+' ≠ 'r')
  have hr : matchWord "r".toList ('+' :: cs) = none :=
    matchWord_none_of_ne (by decide : lower '+' ≠ 'r')
  simp only [postSpellings, matchAnyPat, hpost, hrev, hr]

/-- The dev word does not match at a plus. -/
theorem matchWord_dev_none_plus {cs : List Char} :
    matchWord "dev".toList ('+' :: cs) = none :=
  matchWord_none_of_ne (by decide : lower '+' ≠ 'd')

/-- With a local part next, the pre-release reader finds no
    spelling and gives the text back. -/
theorem parsePre_none_plus {cs : List Char} :
    parsePre ('+' :: cs) = (none, '+' :: cs) := by
  show (match matchAny preSpellings (dropSep ('+' :: cs)) with
    | some (k, rest) => let (n, rest') := optNum rest; (some (k, n), rest')
    | none => (none, '+' :: cs)) = (none, '+' :: cs)
  rw [dropSep_plus, matchAny_pre_none_plus]

/-- With a local part next, the post-release reader finds no
    spelling and gives the text back. -/
theorem parsePost_none_plus {cs : List Char} :
    parsePost ('+' :: cs) = (none, '+' :: cs) := by
  show (match matchAnyPat postSpellings (dropSep ('+' :: cs)) with
    | some rest => let (m, rest') := optNum rest; (some m, rest')
    | none => (none, '+' :: cs)) = (none, '+' :: cs)
  rw [dropSep_plus, matchAnyPat_none_plus]

/-- With a local part next, the dev-release reader finds
    nothing and gives the text back. -/
theorem parseDev_none_plus {cs : List Char} :
    parseDev ('+' :: cs) = (none, '+' :: cs) := by
  show (match matchWord "dev".toList (dropSep ('+' :: cs)) with
    | some rest => let (m, rest') := optNum rest; (some m, rest')
    | none => (none, '+' :: cs)) = (none, '+' :: cs)
  rw [dropSep_plus, matchWord_dev_none_plus]

/-- On a printed local part, the pre-release reader finds
    nothing. -/
theorem parsePre_none_local (loc : Option (List LocalSeg)) :
    parsePre (printLocal loc) = (none, printLocal loc) := by
  cases loc with
  | none => exact parsePre_none_nil
  | some segs => exact parsePre_none_plus

/-- On a printed local part, the post-release reader finds
    nothing. -/
theorem parsePost_none_local (loc : Option (List LocalSeg)) :
    parsePost (printLocal loc) = (none, printLocal loc) := by
  cases loc with
  | none => exact parsePost_none_nil
  | some segs => exact parsePost_none_plus

/-- On a printed local part, the dev-release reader finds
    nothing. -/
theorem parseDev_none_local (loc : Option (List LocalSeg)) :
    parseDev (printLocal loc) = (none, printLocal loc) := by
  cases loc with
  | none => exact parseDev_none_nil
  | some segs => exact parseDev_none_plus

/-- A printed local part never starts with a digit: it is
    empty, or it opens with a plus. -/
theorem local_tail_ok (loc : Option (List LocalSeg)) :
    HeadOk isDigit (printLocal loc) := by
  cases loc with
  | none => exact headOk_nil _
  | some segs =>
    show isDigit '+' = false
    decide

/-- A printed dev segment and a printed local part together
    never start with a digit. -/
theorem dev_local_facts (dev : Option Nat) (loc : Option (List LocalSeg)) :
    HeadOk isDigit (printDev dev ++ printLocal loc) := by
  cases dev with
  | some d => exact headOk_dot_digit _
  | none => exact local_tail_ok loc
/-! ## Facts about the printed tail -/

/-- The head of a cons is not a bang, when the character is
    not one. -/
theorem headBang_dot {c : Char} (hc : c ≠ '!') {cs : List Char} :
    (c :: cs).head? ≠ some '!' :=
  fun h => hc (Option.some.inj h)

/-- The printed tail (the pre, post, dev, and local segments,
    in that nesting) never starts with a digit, never continues
    the release, and never opens with a bang. In every case
    its first character, when it has one, is the dot of the
    first segment that is there, or the plus of the local
    part. -/
theorem suffix_facts (pre : Option (PreKind × Nat)) (post : Option Nat)
    (dev : Option Nat) (loc : Option (List LocalSeg)) :
    HeadOk isDigit
      (printPre pre ++ (printPost post ++ (printDev dev ++ printLocal loc))) ∧
    moreRelease
      (printPre pre ++ (printPost post ++ (printDev dev ++ printLocal loc)))
      = false ∧
    (printPre pre ++ (printPost post ++ (printDev dev ++ printLocal loc))).head?
      ≠ some '!' := by
  cases pre with
  | some p =>
    obtain ⟨k, -⟩ := p
    cases k with
    | a => exact ⟨headOk_dot_digit _, rfl, headBang_dot (by decide)⟩
    | b => exact ⟨headOk_dot_digit _, rfl, headBang_dot (by decide)⟩
    | rc => exact ⟨headOk_dot_digit _, rfl, headBang_dot (by decide)⟩
  | none =>
    cases post with
    | some m => exact ⟨headOk_dot_digit _, rfl, headBang_dot (by decide)⟩
    | none =>
      cases dev with
      | some d => exact ⟨headOk_dot_digit _, rfl, headBang_dot (by decide)⟩
      | none =>
        cases loc with
        | some segs =>
          exact ⟨local_tail_ok (some segs), rfl, headBang_dot (by decide)⟩
        | none => exact ⟨headOk_nil _, rfl, by decide⟩

/-- The printed post, dev, and local segments together never
    start with a digit. -/
theorem tail_facts (post : Option Nat) (dev : Option Nat)
    (loc : Option (List LocalSeg)) :
    HeadOk isDigit (printPost post ++ (printDev dev ++ printLocal loc)) := by
  cases post with
  | some m => exact headOk_dot_digit _
  | none =>
    cases dev with
    | some d => exact headOk_dot_digit _
    | none => exact local_tail_ok loc

/-! ## The print, taken apart -/

/-- A bang in front of a text is the bang character consed
    onto it. -/
theorem bang_append (rest : List Char) : (['!'] ++ rest) = '!' :: rest := rfl

/-- A print with epoch zero is the release print followed by
    the tail segments. The appends of the print lean left, so
    three associativity steps put the release in front. -/
theorem print_zero (rel : List Nat) (pre : Option (PreKind × Nat))
    (post : Option Nat) (dev : Option Nat) (loc : Option (List LocalSeg)) :
    print ⟨0, rel, pre, post, dev, loc⟩
      = printRelease rel ++ (printPre pre
          ++ (printPost post ++ (printDev dev ++ printLocal loc))) := by
  show printEpoch 0 ++ printRelease rel ++ printPre pre ++ printPost post
      ++ printDev dev ++ printLocal loc
    = printRelease rel ++ (printPre pre
        ++ (printPost post ++ (printDev dev ++ printLocal loc)))
  rw [show printEpoch 0 = [] from rfl, List.nil_append, List.append_assoc,
    List.append_assoc, List.append_assoc]

/-- A print with a positive epoch is the epoch digits, a
    bang, and then the release print and the tail segments.
    The appends of the print lean left, so five associativity
    steps bring the epoch to the front. -/
theorem print_pos {e : Nat} (he : e ≠ 0) (rel : List Nat)
    (pre : Option (PreKind × Nat)) (post : Option Nat) (dev : Option Nat)
    (loc : Option (List LocalSeg)) :
    print ⟨e, rel, pre, post, dev, loc⟩
      = printNat e ++ ('!' :: (printRelease rel
          ++ (printPre pre
            ++ (printPost post ++ (printDev dev ++ printLocal loc))))) := by
  show printEpoch e ++ printRelease rel ++ printPre pre ++ printPost post
      ++ printDev dev ++ printLocal loc
    = printNat e ++ ('!' :: (printRelease rel
        ++ (printPre pre
          ++ (printPost post ++ (printDev dev ++ printLocal loc)))))
  unfold printEpoch
  rw [if_neg he, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, List.append_assoc, bang_append]

/-- One release segment prints as its number. -/
theorem printRelease_one (n : Nat) : printRelease [n] = printNat n := rfl

/-- Two or more release segments print as the first number,
    a dot, and the joined rest. -/
theorem printRelease_cons2 (n m : Nat) (ns : List Nat) :
    printRelease (n :: m :: ns)
      = printNat n ++ '.' :: joinDots ((m :: ns).map printNat) := rfl

/-- The first character of a print is a digit: the epoch
    digits when the epoch is positive, else the first release
    number's digits. The prints here are written as the plain
    chains the printer builds, whose appends lean left. -/
theorem print_head_digit (v : Version) (h : WF v) :
    ∃ c cs, print v = c :: cs ∧ isDigit c = true := by
  obtain ⟨e, rel, pre, post, dev, loc⟩ := v
  cases rel with
  | nil => exact absurd rfl h.1
  | cons n ns =>
    by_cases he : e = 0
    · subst he
      obtain ⟨c, cs, hpn, hc⟩ := printNat_head n
      cases ns with
      | nil =>
        refine ⟨c, cs ++ printPre pre ++ printPost post ++ printDev dev
            ++ printLocal loc, ?_, hc⟩
        have hform : print ⟨0, [n], pre, post, dev, loc⟩
            = printNat n ++ printPre pre ++ printPost post ++ printDev dev
              ++ printLocal loc := by
          show printEpoch 0 ++ printRelease [n] ++ printPre pre
              ++ printPost post ++ printDev dev ++ printLocal loc
            = printNat n ++ printPre pre ++ printPost post ++ printDev dev
              ++ printLocal loc
          rw [show printEpoch 0 = [] from rfl, List.nil_append, printRelease_one]
        rw [hform, hpn]
        simp only [List.cons_append]
      | cons m ns' =>
        refine ⟨c, cs ++ ('.' :: joinDots ((m :: ns').map printNat))
            ++ printPre pre ++ printPost post ++ printDev dev
            ++ printLocal loc, ?_, hc⟩
        have hform : print ⟨0, n :: m :: ns', pre, post, dev, loc⟩
            = (printNat n ++ '.' :: joinDots ((m :: ns').map printNat))
              ++ printPre pre ++ printPost post ++ printDev dev
              ++ printLocal loc := by
          show printEpoch 0 ++ printRelease (n :: m :: ns') ++ printPre pre
              ++ printPost post ++ printDev dev ++ printLocal loc
            = (printNat n ++ '.' :: joinDots ((m :: ns').map printNat))
              ++ printPre pre ++ printPost post ++ printDev dev
              ++ printLocal loc
          rw [show printEpoch 0 = [] from rfl, List.nil_append, printRelease_cons2]
        rw [hform, hpn]
        simp only [List.cons_append]
    · obtain ⟨c, cs, hpe, hc⟩ := printNat_head e
      refine ⟨c, cs ++ ['!'] ++ printRelease (n :: ns) ++ printPre pre
          ++ printPost post ++ printDev dev ++ printLocal loc, ?_, hc⟩
      have hform : print ⟨e, n :: ns, pre, post, dev, loc⟩
          = (printNat e ++ ['!']) ++ printRelease (n :: ns) ++ printPre pre
            ++ printPost post ++ printDev dev ++ printLocal loc := by
        show printEpoch e ++ printRelease (n :: ns) ++ printPre pre
            ++ printPost post ++ printDev dev ++ printLocal loc
          = (printNat e ++ ['!']) ++ printRelease (n :: ns) ++ printPre pre
            ++ printPost post ++ printDev dev ++ printLocal loc
        unfold printEpoch
        rw [if_neg he]
      rw [hform, hpe]
      simp only [List.cons_append]

/-- Stripping a leading v leaves a digit alone. -/
theorem stripV_of_digit_head {c : Char} {cs : List Char} (hc : isDigit c = true) :
    stripV (c :: cs) = c :: cs := by
  have hb : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := isDigit_iff.mp hc
  have hv : ('v').toNat = 118 := rfl
  have hV : ('V').toNat = 86 := rfl
  have h1 : c ≠ 'v' := by
    intro hcon
    have h3 : c.toNat = ('v').toNat := congrArg Char.toNat hcon
    omega
  have h2 : c ≠ 'V' := by
    intro hcon
    have h3 : c.toNat = ('V').toNat := congrArg Char.toNat hcon
    omega
  simp [stripV, h1, h2]

/-- A print starts with a digit, so the leading v drop
    leaves it alone. -/
theorem stripV_print (v : Version) (h : WF v) : stripV (print v) = print v := by
  obtain ⟨c, cs, hform, hc⟩ := print_head_digit v h
  rw [hform]
  exact stripV_of_digit_head hc

/-! ## The whole text reads back -/

/-- Once the epoch is read, the rest of a print reads back:
    the release, then the four tail segments in order. -/
theorem parseRest_print (e : Nat) (rel : List Nat) (hrel : rel ≠ [])
    (pre : Option (PreKind × Nat)) (post : Option Nat) (dev : Option Nat)
    (loc : Option (List LocalSeg)) (hloc : LocalOptWF loc) :
    (parseRelease (printRelease rel
      ++ (printPre pre ++ (printPost post ++ (printDev dev
        ++ printLocal loc))))).map
      (fun (rel', rest₂) =>
        let (pre', rest₃) := parsePre rest₂
        let (post', rest₄) := parsePost rest₃
        let (dev', rest₅) := parseDev rest₄
        let (loc', rest₆) := parseLocal rest₅
        (({ epoch := e, release := rel', pre := pre', post := post',
            dev := dev', localPart := loc' } : Version), rest₆))
      = some (⟨e, rel, pre, post, dev, loc⟩, []) := by
  obtain ⟨hok, hmr, -⟩ := suffix_facts pre post dev loc
  rw [parseRelease_print rel hrel _ hok hmr]
  show some (let (pre', rest₃) := parsePre (printPre pre
        ++ (printPost post ++ (printDev dev ++ printLocal loc)));
      let (post', rest₄) := parsePost rest₃;
      let (dev', rest₅) := parseDev rest₄;
      let (loc', rest₆) := parseLocal rest₅;
      (({ epoch := e, release := rel, pre := pre', post := post',
          dev := dev', localPart := loc' } : Version), rest₆))
      = some (⟨e, rel, pre, post, dev, loc⟩, [])
  cases pre with
  | none =>
    cases post with
    | none =>
      cases dev with
      | none =>
        show some (let (pre', rest₃) := parsePre (printLocal loc);
            let (post', rest₄) := parsePost rest₃;
            let (dev', rest₅) := parseDev rest₄;
            let (loc', rest₆) := parseLocal rest₅;
            (({ epoch := e, release := rel, pre := pre', post := post',
                dev := dev', localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, none, none, none, loc⟩, [])
        rw [parsePre_none_local]
        show some (let (post', rest₄) := parsePost (printLocal loc);
            let (dev', rest₅) := parseDev rest₄;
            let (loc', rest₆) := parseLocal rest₅;
            (({ epoch := e, release := rel, pre := none, post := post',
                dev := dev', localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, none, none, none, loc⟩, [])
        rw [parsePost_none_local]
        show some (let (dev', rest₅) := parseDev (printLocal loc);
            let (loc', rest₆) := parseLocal rest₅;
            (({ epoch := e, release := rel, pre := none, post := none,
                dev := dev', localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, none, none, none, loc⟩, [])
        rw [parseDev_none_local]
        show some (let (loc', rest₆) := parseLocal (printLocal loc);
            (({ epoch := e, release := rel, pre := none, post := none,
                dev := none, localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, none, none, none, loc⟩, [])
        rw [parseLocal_print loc hloc]
      | some d =>
        show some (let (pre', rest₃) :=
              parsePre ('.' :: 'd' :: 'e' :: 'v' :: (printNat d ++ printLocal loc));
            let (post', rest₄) := parsePost rest₃;
            let (dev', rest₅) := parseDev rest₄;
            let (loc', rest₆) := parseLocal rest₅;
            (({ epoch := e, release := rel, pre := pre', post := post',
                dev := dev', localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, none, none, some d, loc⟩, [])
        rw [parsePre_none_d]
        show some (let (post', rest₄) :=
              parsePost ('.' :: 'd' :: 'e' :: 'v' :: (printNat d ++ printLocal loc));
            let (dev', rest₅) := parseDev rest₄;
            let (loc', rest₆) := parseLocal rest₅;
            (({ epoch := e, release := rel, pre := none, post := post',
                dev := dev', localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, none, none, some d, loc⟩, [])
        rw [parsePost_none_d]
        show some (let (dev', rest₅) :=
              parseDev (printDev (some d) ++ printLocal loc);
            let (loc', rest₆) := parseLocal rest₅;
            (({ epoch := e, release := rel, pre := none, post := none,
                dev := dev', localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, none, none, some d, loc⟩, [])
        rw [parseDev_printDev d _ (local_tail_ok loc)]
        show some (let (loc', rest₆) := parseLocal (printLocal loc);
            (({ epoch := e, release := rel, pre := none, post := none,
                dev := some d, localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, none, none, some d, loc⟩, [])
        rw [parseLocal_print loc hloc]
    | some m =>
      show some (let (pre', rest₃) :=
            parsePre ('.' :: 'p' :: 'o' :: 's' :: 't'
              :: (printNat m ++ (printDev dev ++ printLocal loc)));
          let (post', rest₄) := parsePost rest₃;
          let (dev', rest₅) := parseDev rest₄;
          let (loc', rest₆) := parseLocal rest₅;
          (({ epoch := e, release := rel, pre := pre', post := post',
              dev := dev', localPart := loc' } : Version), rest₆))
          = some (⟨e, rel, none, some m, dev, loc⟩, [])
      rw [parsePre_none_po]
      show some (let (post', rest₄) :=
            parsePost (printPost (some m) ++ (printDev dev ++ printLocal loc));
          let (dev', rest₅) := parseDev rest₄;
          let (loc', rest₆) := parseLocal rest₅;
          (({ epoch := e, release := rel, pre := none, post := post',
              dev := dev', localPart := loc' } : Version), rest₆))
          = some (⟨e, rel, none, some m, dev, loc⟩, [])
      rw [parsePost_printPost m _ (dev_local_facts dev loc)]
      show some (let (dev', rest₅) := parseDev (printDev dev ++ printLocal loc);
          let (loc', rest₆) := parseLocal rest₅;
          (({ epoch := e, release := rel, pre := none, post := some m,
              dev := dev', localPart := loc' } : Version), rest₆))
          = some (⟨e, rel, none, some m, dev, loc⟩, [])
      cases dev with
      | none =>
        show some (let (dev', rest₅) := parseDev (printLocal loc);
            let (loc', rest₆) := parseLocal rest₅;
            (({ epoch := e, release := rel, pre := none, post := some m,
                dev := dev', localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, none, some m, none, loc⟩, [])
        rw [parseDev_none_local]
        show some (let (loc', rest₆) := parseLocal (printLocal loc);
            (({ epoch := e, release := rel, pre := none, post := some m,
                dev := none, localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, none, some m, none, loc⟩, [])
        rw [parseLocal_print loc hloc]
      | some d =>
        show some (let (dev', rest₅) :=
              parseDev (printDev (some d) ++ printLocal loc);
            let (loc', rest₆) := parseLocal rest₅;
            (({ epoch := e, release := rel, pre := none, post := some m,
                dev := dev', localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, none, some m, some d, loc⟩, [])
        rw [parseDev_printDev d _ (local_tail_ok loc)]
        show some (let (loc', rest₆) := parseLocal (printLocal loc);
            (({ epoch := e, release := rel, pre := none, post := some m,
                dev := some d, localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, none, some m, some d, loc⟩, [])
        rw [parseLocal_print loc hloc]
  | some p =>
    obtain ⟨k, n⟩ := p
    rw [parsePre_printPre k n _ (tail_facts post dev loc)]
    show some (let (post', rest₄) :=
          parsePost (printPost post ++ (printDev dev ++ printLocal loc));
        let (dev', rest₅) := parseDev rest₄;
        let (loc', rest₆) := parseLocal rest₅;
        (({ epoch := e, release := rel, pre := some (k, n), post := post',
            dev := dev', localPart := loc' } : Version), rest₆))
        = some (⟨e, rel, some (k, n), post, dev, loc⟩, [])
    cases post with
    | none =>
      cases dev with
      | none =>
        show some (let (post', rest₄) := parsePost (printLocal loc);
            let (dev', rest₅) := parseDev rest₄;
            let (loc', rest₆) := parseLocal rest₅;
            (({ epoch := e, release := rel, pre := some (k, n), post := post',
                dev := dev', localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, some (k, n), none, none, loc⟩, [])
        rw [parsePost_none_local]
        show some (let (dev', rest₅) := parseDev (printLocal loc);
            let (loc', rest₆) := parseLocal rest₅;
            (({ epoch := e, release := rel, pre := some (k, n), post := none,
                dev := dev', localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, some (k, n), none, none, loc⟩, [])
        rw [parseDev_none_local]
        show some (let (loc', rest₆) := parseLocal (printLocal loc);
            (({ epoch := e, release := rel, pre := some (k, n), post := none,
                dev := none, localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, some (k, n), none, none, loc⟩, [])
        rw [parseLocal_print loc hloc]
      | some d =>
        show some (let (post', rest₄) :=
              parsePost ('.' :: 'd' :: 'e' :: 'v' :: (printNat d ++ printLocal loc));
            let (dev', rest₅) := parseDev rest₄;
            let (loc', rest₆) := parseLocal rest₅;
            (({ epoch := e, release := rel, pre := some (k, n), post := post',
                dev := dev', localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, some (k, n), none, some d, loc⟩, [])
        rw [parsePost_none_d]
        show some (let (dev', rest₅) :=
              parseDev (printDev (some d) ++ printLocal loc);
            let (loc', rest₆) := parseLocal rest₅;
            (({ epoch := e, release := rel, pre := some (k, n), post := none,
                dev := dev', localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, some (k, n), none, some d, loc⟩, [])
        rw [parseDev_printDev d _ (local_tail_ok loc)]
        show some (let (loc', rest₆) := parseLocal (printLocal loc);
            (({ epoch := e, release := rel, pre := some (k, n), post := none,
                dev := some d, localPart := loc' } : Version), rest₆))
            = some (⟨e, rel, some (k, n), none, some d, loc⟩, [])
        rw [parseLocal_print loc hloc]
    | some m =>
      show some (let (post', rest₄) :=
            parsePost (printPost (some m) ++ (printDev dev ++ printLocal loc));
          let (dev', rest₅) := parseDev rest₄;
          let (loc', rest₆) := parseLocal rest₅;
          (({ epoch := e, release := rel, pre := some (k, n), post := post',
              dev := dev', localPart := loc' } : Version), rest₆))
          = some (⟨e, rel, some (k, n), some m, dev, loc⟩, [])
      rw [parsePost_printPost m _ (dev_local_facts dev loc)]
      show some (let (dev', rest₅) := parseDev (printDev dev ++ printLocal loc);
          let (loc', rest₆) := parseLocal rest₅;
          (({ epoch := e, release := rel, pre := some (k, n), post := some m,
              dev := dev', localPart := loc' } : Version), rest₆))
          = some (⟨e, rel, some (k, n), some m, dev, loc⟩, [])
      cases dev with
      | none =>
        show some (let (dev', rest₅) := parseDev (printLocal loc);
            let (loc', rest₆) := parseLocal rest₅;
            (({ epoch := e, release := rel, pre := some (k, n),
                post := some m, dev := dev', localPart := loc' } : Version),
              rest₆))
            = some (⟨e, rel, some (k, n), some m, none, loc⟩, [])
        rw [parseDev_none_local]
        show some (let (loc', rest₆) := parseLocal (printLocal loc);
            (({ epoch := e, release := rel, pre := some (k, n),
                post := some m, dev := none, localPart := loc' } : Version),
              rest₆))
            = some (⟨e, rel, some (k, n), some m, none, loc⟩, [])
        rw [parseLocal_print loc hloc]
      | some d =>
        show some (let (dev', rest₅) :=
              parseDev (printDev (some d) ++ printLocal loc);
            let (loc', rest₆) := parseLocal rest₅;
            (({ epoch := e, release := rel, pre := some (k, n),
                post := some m, dev := dev', localPart := loc' } : Version),
              rest₆))
            = some (⟨e, rel, some (k, n), some m, some d, loc⟩, [])
        rw [parseDev_printDev d _ (local_tail_ok loc)]
        show some (let (loc', rest₆) := parseLocal (printLocal loc);
            (({ epoch := e, release := rel, pre := some (k, n),
                post := some m, dev := some d, localPart := loc' } : Version),
              rest₆))
            = some (⟨e, rel, some (k, n), some m, some d, loc⟩, [])
        rw [parseLocal_print loc hloc]

/-- The whole reader on a print: the leading v drop, the
    epoch, and then the rest. -/
theorem parseVersion_print (v : Version) (h : WF v) :
    parseVersion (print v) = some (v, []) := by
  obtain ⟨e, rel, pre, post, dev, loc⟩ := v
  have hrel : rel ≠ [] := h.1
  have hloc : LocalOptWF loc := h.2
  obtain ⟨hokS, -, hbang⟩ := suffix_facts pre post dev loc
  have hstrip : stripV (print ⟨e, rel, pre, post, dev, loc⟩)
      = print ⟨e, rel, pre, post, dev, loc⟩ :=
    stripV_print ⟨e, rel, pre, post, dev, loc⟩ h
  show parseVersion (print ⟨e, rel, pre, post, dev, loc⟩)
      = some (⟨e, rel, pre, post, dev, loc⟩, [])
  unfold parseVersion
  rw [hstrip]
  show (let (e', rest₁) := parseEpoch (print ⟨e, rel, pre, post, dev, loc⟩);
      (parseRelease rest₁).map fun (rel', rest₂) =>
        let (pre', rest₃) := parsePre rest₂
        let (post', rest₄) := parsePost rest₃
        let (dev', rest₅) := parseDev rest₄
        let (loc', rest₆) := parseLocal rest₅
        (({ epoch := e', release := rel', pre := pre', post := post',
            dev := dev', localPart := loc' } : Version), rest₆))
      = some (⟨e, rel, pre, post, dev, loc⟩, [])
  by_cases he : e = 0
  · subst he
    rw [print_zero, parseEpoch_release hrel _ hokS hbang]
    show (parseRelease (printRelease rel
        ++ (printPre pre ++ (printPost post ++ (printDev dev
          ++ printLocal loc))))).map
        (fun (rel', rest₂) =>
          let (pre', rest₃) := parsePre rest₂
          let (post', rest₄) := parsePost rest₃
          let (dev', rest₅) := parseDev rest₄
          let (loc', rest₆) := parseLocal rest₅
          (({ epoch := 0, release := rel', pre := pre', post := post',
              dev := dev', localPart := loc' } : Version), rest₆))
        = some (⟨0, rel, pre, post, dev, loc⟩, [])
    exact parseRest_print 0 rel hrel pre post dev loc hloc
  · rw [print_pos he, parseEpoch_pos]
    show (parseRelease (printRelease rel
        ++ (printPre pre ++ (printPost post ++ (printDev dev
          ++ printLocal loc))))).map
        (fun (rel', rest₂) =>
          let (pre', rest₃) := parsePre rest₂
          let (post', rest₄) := parsePost rest₃
          let (dev', rest₅) := parseDev rest₄
          let (loc', rest₆) := parseLocal rest₅
          (({ epoch := e, release := rel', pre := pre', post := post',
              dev := dev', localPart := loc' } : Version), rest₆))
        = some (⟨e, rel, pre, post, dev, loc⟩, [])
    exact parseRest_print e rel hrel pre post dev loc hloc

/-- The main theorem: parsing the printed form of a well
    formed version gives the version back. -/
theorem parse_print (v : Version) (h : WF v) : parse (print v) = some v := by
  show (match parseVersion (print v) with
    | some (v', []) => some v'
    | _ => none) = some v
  rw [parseVersion_print v h]

end Pep440.Proofs
