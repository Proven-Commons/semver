/-
  The round trip: parsing the printed form of a well formed
  version gives the version back.

  The proof follows the shape of the printer. Numbers first: the
  digits the printer writes read back to the same number. Then one
  prerelease identifier, then a dot separated list of them, then
  build identifiers the same way, then the whole version.
-/

import Semver

namespace Semver.Proofs

open Semver

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

theorem digitChar_ne_zero {d : Nat} (h : d < 10) (hd : d ≠ 0) : digitChar d ≠ '0' := by
  intro hcon
  have h1 : (digitChar d).toNat = ('0').toNat := congrArg Char.toNat hcon
  rw [digitChar_toNat h] at h1
  simp at h1
  omega

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

/-- Every character the printer writes for a number is an
    identifier character. -/
theorem printNat_isIdChar {n : Nat} : ∀ c ∈ printNat n, isIdChar c = true := by
  intro c hc
  rw [isIdChar_iff]
  exact Or.inl (isDigit_iff.mp (printNat_isDigit c hc))

/-- The number text check passes on any nonempty digit text
    whose first character is not 0, and on the text 0 itself.
    Stated for a text that does not start with 0. -/
theorem numTextOk_of_head {ds : List Char} (hne : ds ≠ [])
    (h : ds.head? ≠ some '0') : numTextOk ds = true := by
  cases hds : ds with
  | nil => exact absurd hds hne
  | cons c cs =>
    subst hds
    have hne' : (c :: cs).isEmpty = false := rfl
    have hhead : (c :: cs).head? = some c := rfl
    rw [hhead] at h
    have hbeq : ((c :: cs).head? == some '0') = false := by
      rw [hhead]
      cases hcc : (some c == some '0') with
      | false => rfl
      | true =>
        simp only [beq_iff_eq] at hcc
        exact absurd hcc h
    show numTextOk (c :: cs) = true
    show (!(c :: cs).isEmpty && (((c :: cs).length == 1) ||
      !((c :: cs).head? == some '0'))) = true
    rw [hne', hbeq]
    simp

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

/-- The number text check passes on a printed number. -/
theorem numTextOk_printNat (n : Nat) : numTextOk (printNat n) = true := by
  by_cases h0 : n = 0
  · subst h0
    rfl
  · obtain ⟨_, hmem, hform⟩ := digitsRev_spec n
    rcases hform with h | ⟨ds, d, hds, hd⟩
    · omega
    · have hprint : printNat n = digitChar d :: (ds.reverse.map digitChar) := by
        unfold printNat
        rw [if_neg h0, hds]
        simp [List.reverse_append]
      have hlt : d < 10 := hmem d (by rw [hds]; simp)
      have hhead : (printNat n).head? ≠ some '0' := by
        rw [hprint]
        simp [digitChar_ne_zero hlt hd]
      exact numTextOk_of_head (printNat_ne_nil n) hhead

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

theorem takeIdChars_append (ds rest : List Char) (hall : ∀ c ∈ ds, isIdChar c = true)
    (h : HeadOk isIdChar rest) : takeIdChars (ds ++ rest) = (ds, rest) := by
  induction ds with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c cs =>
      have hc : isIdChar c = false := h
      show takeIdChars (c :: cs) = ([], c :: cs)
      simp [takeIdChars, hc]
  | cons d ds ih =>
    have hd : isIdChar d = true := hall d (by simp)
    have hds : ∀ c ∈ ds, isIdChar c = true := fun c hc => hall c (by simp [hc])
    show takeIdChars (d :: (ds ++ rest)) = (d :: ds, rest)
    simp [takeIdChars, hd, ih hds]

/-! ## Reading the printed parts back -/

/-- A printed number reads back as the number, over any tail that
    does not start with a digit. -/
theorem parseCoreNum_printNat (n : Nat) (rest : List Char) (h : HeadOk isDigit rest) :
    parseCoreNum (printNat n ++ rest) = some (n, rest) := by
  simp [parseCoreNum, takeDigits_append (printNat n) rest printNat_isDigit h,
    numTextOk_printNat, digitsValue_printNat]

/-- The text of a numeric identifier reads back as that
    identifier. -/
theorem classifyPreId_printNat (n : Nat) : classifyPreId (printNat n) = some (.num n) := by
  have hall : (printNat n).all isDigit = true := by
    rw [List.all_eq_true]
    exact printNat_isDigit
  simp [classifyPreId, hall, numTextOk_printNat, digitsValue_printNat]

/-- The text of an alphanumeric identifier reads back as that
    identifier. -/
theorem classifyPreId_alpha (cs : List Char) (h : WFAlpha cs) :
    classifyPreId cs = some (.alpha cs) := by
  obtain ⟨hne, hchars, ⟨c, hc, hcd⟩⟩ := h
  unfold classifyPreId
  have hnotall : cs.all isDigit = false := by
    cases hall : cs.all isDigit with
    | false => rfl
    | true =>
      rw [List.all_eq_true] at hall
      exact absurd (isDigit_iff.mp (hall c hc)) hcd
  simp [hnotall]

/-- A printed prerelease identifier reads back, over a tail that
    does not start with an identifier character. -/
theorem parsePreId_printPreId (id : PreId) (h : WFPreId id) (rest : List Char)
    (hr : HeadOk isIdChar rest) :
    parsePreId (printPreId id ++ rest) = some (id, rest) := by
  cases id with
  | num n =>
    show parsePreId (printNat n ++ rest) = some (PreId.num n, rest)
    simp [parsePreId, takeIdChars_append (printNat n) rest printNat_isIdChar hr,
      classifyPreId_printNat, printNat_ne_nil]
  | alpha cs =>
    show parsePreId (cs ++ rest) = some (PreId.alpha cs, rest)
    simp [parsePreId, takeIdChars_append cs rest
      (fun c hc => isIdChar_iff.mpr (h.2.1 c hc)) hr, classifyPreId_alpha cs h, h.1]

/-- A printed build identifier reads back, over a tail that does
    not start with an identifier character. -/
theorem parseBuildId_print (cs : List Char) (h : WFBuildId cs) (rest : List Char)
    (hr : HeadOk isIdChar rest) :
    parseBuildId (cs ++ rest) = some (cs, rest) := by
  simp [parseBuildId, takeIdChars_append cs rest
    (fun c hc => isIdChar_iff.mpr (h.2 c hc)) hr, h.1]

/-! ## The delimiter characters end every run -/

theorem headOk_dot_digit (r : List Char) : HeadOk isDigit ('.' :: r) := by
  show isDigit '.' = false
  decide

theorem headOk_minus_digit (r : List Char) : HeadOk isDigit ('-' :: r) := by
  show isDigit '-' = false
  decide

theorem headOk_plus_digit (r : List Char) : HeadOk isDigit ('+' :: r) := by
  show isDigit '+' = false
  decide

theorem headOk_nil (test : Char → Bool) : HeadOk test [] := trivial

theorem headOk_dot_idChar (r : List Char) : HeadOk isIdChar ('.' :: r) := by
  show isIdChar '.' = false
  decide

theorem headOk_plus_idChar (r : List Char) : HeadOk isIdChar ('+' :: r) := by
  show isIdChar '+' = false
  decide

/-- A tail that starts with an appended hyphen part still starts
    with the hyphen. -/
theorem headOk_minus_append (J X : List Char) :
    HeadOk isDigit (('-' :: J) ++ X) := by
  show isDigit '-' = false
  decide

/-! ## Lengths of joined prints -/

/-- A joined list of nonempty parts is at least as long as the
    number of parts, less the dots it saves at the end: the length
    of the join plus one is at least the number of parts. -/
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

/-- A printed prerelease identifier is never empty. -/
theorem printPreId_ne_nil (id : PreId) (h : WFPreId id) : printPreId id ≠ [] := by
  cases id with
  | num n => exact printNat_ne_nil n
  | alpha cs => exact h.1

/-- The tail after a printed list must not start with a dot: a
    dot would open another identifier. Named so that statements
    share one form. -/
def NotDotHead (rest : List Char) : Prop :=
  match rest with
  | [] => True
  | c :: _ => c ≠ '.'

/-! ## Reading printed lists back -/

/-- A printed list of prerelease identifiers reads back. The tail
    after the list must not start with an identifier character,
    and must not start with a dot either: a dot would open another
    identifier. Induction on the fuel. -/
theorem parsePreIdsGo_print : ∀ (fuel : Nat) (ids : List PreId) (rest : List Char),
    ids ≠ [] → (∀ id ∈ ids, WFPreId id) → HeadOk isIdChar rest →
    NotDotHead rest →
    ids.length ≤ fuel →
    parsePreIdsGo fuel (joinDots (ids.map printPreId) ++ rest) = some (ids, rest) := by
  intro fuel
  induction fuel with
  | zero =>
    intro ids rest hne _ _ _ hlen
    cases ids with
    | nil => exact absurd rfl hne
    | cons id ids => simp at hlen
  | succ f ih =>
    intro ids rest hne hwf hr hrd hlen
    cases ids with
    | nil => exact absurd rfl hne
    | cons id ids' =>
      have hid : WFPreId id := hwf id (by simp)
      have hwf' : ∀ x ∈ ids', WFPreId x := fun x hx => hwf x (by simp [hx])
      cases ids' with
      | nil =>
        show parsePreIdsGo (f + 1) (printPreId id ++ rest) = some ([id], rest)
        show (match parsePreId (printPreId id ++ rest) with
          | none => none
          | some (x, rest') =>
            if rest'.head? = some '.' then
              match parsePreIdsGo f rest'.tail with
              | some (ids, rest'') => some (x :: ids, rest'')
              | none => none
            else some ([x], rest')) = some ([id], rest)
        rw [parsePreId_printPreId id hid rest hr]
        cases rest with
        | nil => rfl
        | cons c cs =>
          have hc : c ≠ '.' := hrd
          show (if (c :: cs).head? = some '.' then
              match parsePreIdsGo f (c :: cs).tail with
              | some (ids, rest'') => some (id :: ids, rest'')
              | none => none
            else some ([id], c :: cs)) = some ([id], c :: cs)
          rw [if_neg (by simp [hc])]
      | cons id₂ ids'' =>
        have hwf'' : ∀ x ∈ (id₂ :: ids''), WFPreId x := hwf'
        show parsePreIdsGo (f + 1)
            ((printPreId id ++ '.' :: joinDots ((id₂ :: ids'').map printPreId)) ++ rest) =
          some (id :: id₂ :: ids'', rest)
        rw [List.append_assoc]
        show (match parsePreId
            (printPreId id ++ ('.' :: (joinDots ((id₂ :: ids'').map printPreId) ++ rest))) with
          | none => none
          | some (x, rest') =>
            if rest'.head? = some '.' then
              match parsePreIdsGo f rest'.tail with
              | some (ids, rest'') => some (x :: ids, rest'')
              | none => none
            else some ([x], rest')) = some (id :: id₂ :: ids'', rest)
        rw [parsePreId_printPreId id hid _ (headOk_dot_idChar _)]
        show (if ('.' :: (joinDots ((id₂ :: ids'').map printPreId) ++ rest)).head? =
            some '.' then
            match parsePreIdsGo f
                ('.' :: (joinDots ((id₂ :: ids'').map printPreId) ++ rest)).tail with
            | some (ids, rest'') => some (id :: ids, rest'')
            | none => none
          else some ([id], '.' :: (joinDots ((id₂ :: ids'').map printPreId) ++ rest))) =
          some (id :: id₂ :: ids'', rest)
        rw [if_pos (by rfl : List.head?
          ('.' :: (joinDots ((id₂ :: ids'').map printPreId) ++ rest)) = some '.')]
        show (match parsePreIdsGo f (joinDots ((id₂ :: ids'').map printPreId) ++ rest) with
          | some (ids, rest'') => some (id :: ids, rest'')
          | none => none) = some (id :: id₂ :: ids'', rest)
        rw [ih (id₂ :: ids'') rest (by simp) hwf'' hr hrd (by
          simp at hlen
          omega)]

/-- A printed list of build identifiers reads back. The same
    shape as the prerelease list. -/
theorem parseBuildIdsGo_print : ∀ (fuel : Nat) (ids : List (List Char))
    (rest : List Char),
    ids ≠ [] → (∀ b ∈ ids, WFBuildId b) → HeadOk isIdChar rest →
    NotDotHead rest →
    ids.length ≤ fuel →
    parseBuildIdsGo fuel (joinDots ids ++ rest) = some (ids, rest) := by
  intro fuel
  induction fuel with
  | zero =>
    intro ids rest hne _ _ _ hlen
    cases ids with
    | nil => exact absurd rfl hne
    | cons id ids => simp at hlen
  | succ f ih =>
    intro ids rest hne hwf hr hrd hlen
    cases ids with
    | nil => exact absurd rfl hne
    | cons id ids' =>
      have hid : WFBuildId id := hwf id (by simp)
      have hwf' : ∀ x ∈ ids', WFBuildId x := fun x hx => hwf x (by simp [hx])
      cases ids' with
      | nil =>
        show parseBuildIdsGo (f + 1) (id ++ rest) = some ([id], rest)
        show (match parseBuildId (id ++ rest) with
          | none => none
          | some (x, rest') =>
            if rest'.head? = some '.' then
              match parseBuildIdsGo f rest'.tail with
              | some (ids, rest'') => some (x :: ids, rest'')
              | none => none
            else some ([x], rest')) = some ([id], rest)
        rw [parseBuildId_print id hid rest hr]
        cases rest with
        | nil => rfl
        | cons c cs =>
          have hc : c ≠ '.' := hrd
          show (if (c :: cs).head? = some '.' then
              match parseBuildIdsGo f (c :: cs).tail with
              | some (ids, rest'') => some (id :: ids, rest'')
              | none => none
            else some ([id], c :: cs)) = some ([id], c :: cs)
          rw [if_neg (by simp [hc])]
      | cons id₂ ids'' =>
        show parseBuildIdsGo (f + 1)
            ((id ++ '.' :: joinDots (id₂ :: ids'')) ++ rest) =
          some (id :: id₂ :: ids'', rest)
        rw [List.append_assoc]
        show (match parseBuildId
            (id ++ ('.' :: (joinDots (id₂ :: ids'') ++ rest))) with
          | none => none
          | some (x, rest') =>
            if rest'.head? = some '.' then
              match parseBuildIdsGo f rest'.tail with
              | some (ids, rest'') => some (x :: ids, rest'')
              | none => none
            else some ([x], rest')) = some (id :: id₂ :: ids'', rest)
        rw [parseBuildId_print id hid _ (headOk_dot_idChar _)]
        show (if ('.' :: (joinDots (id₂ :: ids'') ++ rest)).head? = some '.' then
            match parseBuildIdsGo f ('.' :: (joinDots (id₂ :: ids'') ++ rest)).tail with
            | some (ids, rest'') => some (id :: ids, rest'')
            | none => none
          else some ([id], '.' :: (joinDots (id₂ :: ids'') ++ rest))) =
          some (id :: id₂ :: ids'', rest)
        rw [if_pos (by rfl : List.head?
          ('.' :: (joinDots (id₂ :: ids'') ++ rest)) = some '.')]
        show (match parseBuildIdsGo f (joinDots (id₂ :: ids'') ++ rest) with
          | some (ids, rest'') => some (id :: ids, rest'')
          | none => none) = some (id :: id₂ :: ids'', rest)
        rw [ih (id₂ :: ids'') rest (by simp) hwf' hr hrd (by
          simp at hlen
          omega)]

/-! ## The whole version -/

/-- The fuel the identifier readers get from the printed text is
    always enough: the number of identifiers is at most the length
    of their joined print, plus the tail. -/
theorem ids_length_le (ids : List PreId) (hwf : ∀ id ∈ ids, WFPreId id)
    (tail : List Char) :
    ids.length ≤ (joinDots (ids.map printPreId) ++ tail).length + 1 := by
  rw [List.length_append]
  have h := joinDots_length (ids.map printPreId) (by
    intro p hp
    obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hp
    exact printPreId_ne_nil id (hwf id hid))
  simp at h
  omega

/-- The build side of the same fuel fact. -/
theorem build_length_le (ids : List (List Char))
    (hwf : ∀ b ∈ ids, WFBuildId b) (tail : List Char) :
    ids.length ≤ (joinDots ids ++ tail).length + 1 := by
  rw [List.length_append]
  have h := joinDots_length ids (fun b hb => (hwf b hb).1)
  omega

/-- A printed number at the very end reads back, with nothing
    left over. -/
theorem parseCoreNum_printNat_last (n : Nat) :
    parseCoreNum (printNat n) = some (n, []) := by
  have h := parseCoreNum_printNat n [] (headOk_nil _)
  simpa using h

/-- A dot at the front is read, and the rest returned. -/
theorem expectDot_cons (rest : List Char) : expectDot ('.' :: rest) = some rest := by
  simp [expectDot]

/-- The prerelease reader on a printed prerelease part, with a
    tail behind it. -/
theorem parseOptPre_printPre (ids : List PreId) (hne : ids ≠ [])
    (hwf : ∀ id ∈ ids, WFPreId id) (tail : List Char)
    (hr : HeadOk isIdChar tail)
    (hrd : NotDotHead tail) :
    parseOptPre (('-' :: joinDots (ids.map printPreId)) ++ tail) =
      some (ids, tail) := by
  show parsePreIdsGo ((joinDots (ids.map printPreId) ++ tail).length + 1)
      (joinDots (ids.map printPreId) ++ tail) = some (ids, tail)
  exact parsePreIdsGo_print _ _ _ hne hwf hr hrd (ids_length_le ids hwf tail)

/-- The prerelease reader on a printed prerelease part with
    nothing behind it. -/
theorem parseOptPre_printPre_last (ids : List PreId) (hne : ids ≠ [])
    (hwf : ∀ id ∈ ids, WFPreId id) :
    parseOptPre ('-' :: joinDots (ids.map printPreId)) = some (ids, []) := by
  show parsePreIdsGo ((joinDots (ids.map printPreId)).length + 1)
      (joinDots (ids.map printPreId)) = some (ids, [])
  have h := parsePreIdsGo_print ((joinDots (ids.map printPreId) ++ []).length + 1)
    ids [] hne hwf (headOk_nil _) True.intro (ids_length_le ids hwf [])
  simpa using h

/-- With a plus sign at the front, the prerelease reader reads
    nothing. -/
theorem parseOptPre_plus (rest : List Char) :
    parseOptPre ('+' :: rest) = some ([], '+' :: rest) := by
  simp [parseOptPre]

/-- With nothing at the front, the prerelease reader reads
    nothing. -/
theorem parseOptPre_nil : parseOptPre [] = some ([], []) := by
  simp [parseOptPre]

/-- The build reader on a printed build part. -/
theorem parseOptBuild_printBuild (ids : List (List Char)) (hne : ids ≠ [])
    (hwf : ∀ b ∈ ids, WFBuildId b) :
    parseOptBuild ('+' :: joinDots ids) = some (ids, []) := by
  show parseBuildIdsGo ((joinDots ids).length + 1) (joinDots ids) = some (ids, [])
  have h := parseBuildIdsGo_print ((joinDots ids ++ []).length + 1) ids []
    hne hwf (headOk_nil _) True.intro (build_length_le ids hwf [])
  simpa using h

/-- With nothing at the front, the build reader reads nothing. -/
theorem parseOptBuild_nil : parseOptBuild [] = some ([], []) := by
  simp [parseOptBuild]

/-- Parsing the printed form of a version gives the version and
    nothing left over. The four shapes of the optional parts are
    handled by the cases on the prerelease and build lists. Each
    case rewrites the readers one by one and then collapses the
    chain of binds over `some`. -/
theorem parseVersion_print (v : Version) (h : WF v) :
    parseVersion (print v) = some (v, []) := by
  obtain ⟨M, m, p, pre, build⟩ := v
  obtain ⟨hwfpre, hwfbuild⟩ := h
  cases pre with
  | nil =>
    cases build with
    | nil =>
      show parseVersion (printNat M ++ ('.' :: (printNat m ++ ('.' ::
        (printNat p ++ []))))) = some (⟨M, m, p, [], []⟩, [])
      unfold parseVersion
      rw [parseCoreNum_printNat M _ (headOk_dot_digit _)]
      simp only [Option.bind_some]
      try dsimp only
      rw [expectDot_cons]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseCoreNum_printNat m _ (headOk_dot_digit _)]
      simp only [Option.bind_some]
      try dsimp only
      rw [expectDot_cons]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseCoreNum_printNat p _ (headOk_nil _)]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseOptPre_nil]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseOptBuild_nil]
      simp only [Option.bind_some]
      try dsimp only
    | cons b bs =>
      show parseVersion (printNat M ++ ('.' :: (printNat m ++ ('.' ::
        (printNat p ++ ('+' :: joinDots (b :: bs))))))) =
        some (⟨M, m, p, [], b :: bs⟩, [])
      unfold parseVersion
      rw [parseCoreNum_printNat M _ (headOk_dot_digit _)]
      simp only [Option.bind_some]
      try dsimp only
      rw [expectDot_cons]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseCoreNum_printNat m _ (headOk_dot_digit _)]
      simp only [Option.bind_some]
      try dsimp only
      rw [expectDot_cons]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseCoreNum_printNat p _ (headOk_plus_digit _)]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseOptPre_plus]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseOptBuild_printBuild (b :: bs) (by simp) hwfbuild]
      simp only [Option.bind_some]
      try dsimp only
  | cons id ids =>
    cases build with
    | nil =>
      show parseVersion (printNat M ++ ('.' :: (printNat m ++ ('.' ::
        (printNat p ++ ('-' :: joinDots ((id :: ids).map printPreId))))))) =
        some (⟨M, m, p, id :: ids, []⟩, [])
      unfold parseVersion
      rw [parseCoreNum_printNat M _ (headOk_dot_digit _)]
      simp only [Option.bind_some]
      try dsimp only
      rw [expectDot_cons]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseCoreNum_printNat m _ (headOk_dot_digit _)]
      simp only [Option.bind_some]
      try dsimp only
      rw [expectDot_cons]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseCoreNum_printNat p _ (headOk_minus_digit _)]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseOptPre_printPre_last (id :: ids) (by simp) hwfpre]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseOptBuild_nil]
      simp only [Option.bind_some]
      try dsimp only
    | cons b bs =>
      show parseVersion (printNat M ++ ('.' :: (printNat m ++ ('.' ::
        (printNat p ++ (('-' :: joinDots ((id :: ids).map printPreId)) ++
          ('+' :: joinDots (b :: bs)))))))) =
        some (⟨M, m, p, id :: ids, b :: bs⟩, [])
      unfold parseVersion
      rw [parseCoreNum_printNat M _ (headOk_dot_digit _)]
      simp only [Option.bind_some]
      try dsimp only
      rw [expectDot_cons]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseCoreNum_printNat m _ (headOk_dot_digit _)]
      simp only [Option.bind_some]
      try dsimp only
      rw [expectDot_cons]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseCoreNum_printNat p _ (headOk_minus_append _ _)]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseOptPre_printPre (id :: ids) (by simp) hwfpre
        ('+' :: joinDots (b :: bs)) (headOk_plus_idChar _)
        (show ('+' : Char) ≠ '.' by decide)]
      simp only [Option.bind_some]
      try dsimp only
      rw [parseOptBuild_printBuild (b :: bs) (by simp) hwfbuild]
      simp only [Option.bind_some]
      try dsimp only

/-- The round trip: parsing the printed form of a well formed
    version gives the version back. -/
theorem parse_print (v : Version) (h : WF v) : parse (print v) = some v := by
  unfold parse
  rw [parseVersion_print v h]

end Semver.Proofs
