import Mathlib.Tactic
import Analysis.Section_2_1

/-!
# Analysis I, Section 2.2

This file is a translation of Section 2.2 of Analysis I to Lean 4.  All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.   When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Definition of addition and order for the "Chapter 2" natural numbers, `Chapter2.Nat`
- Establishment of basic properties of addition and order

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of `Chapter2.Nat` "by hand" for pedagogical purposes.
-/

namespace Chapter2


/-- Definition 2.2.1. (Addition of natural numbers). -/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

instance Nat.instAdd : Add Nat where
  add := add

theorem Nat.zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

theorem Nat.succ_add (n m: Nat) : n++ + m = (n+m)++ := by rfl

theorem Nat.one_add (m:Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl, succ_add, zero_add]

theorem Nat.two_add (m:Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl, succ_add, one_add]

example : (2:Nat) + 3 = 5 := by
  rw [Nat.two_add, show 3++=4 from rfl, show 4++=5 from rfl]

-- sum of two natural numbers is again a natural number
#check (fun (n m:Nat) ↦ n + m)

/-- Lemma 2.2.2 (n + 0 = n) -/
lemma Nat.add_zero (n:Nat) : n + 0 = n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . exact zero_add 0
  intro n ih
  calc
    (n++) + 0 = (n + 0)++ := by rfl
    _ = n++ := by rw [ih]

/-- Lemma 2.2.3 (n+(m++) = (n+m)++). -/
lemma Nat.add_succ (n m:Nat) : n + (m++) = (n + m)++ := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, zero_add]
  intro n ih
  rw [succ_add, ih]
  rw [succ_add]


/-- n++ = n + 1 (Why?) -/
theorem Nat.succ_eq_add_one (n:Nat) : n++ = n + 1 := by
  rw [show 1 = 0++ from rfl]
  rw[add_succ]
  rw[add_zero]

/-- Proposition 2.2.4 (Addition is commutative) -/
theorem Nat.add_comm (n m:Nat) : n + m = m + n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, add_zero]
  intro n ih
  rw [succ_add]
  rw [add_succ, ih]

/-- Proposition 2.2.5 (Addition is associative) / Exercise 2.2.1-/
theorem Nat.add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
  revert c
  apply induction
  · rw[add_zero,add_zero]
  intro n h
  rw [add_succ]
  rw[add_succ]
  rw[add_succ]
  rw[h]

/-- Proposition 2.2.6 (Cancellation law) -/
theorem Nat.add_cancel_left (a b c:Nat) (habc: a + b = a + c) : b = c := by
  -- this proof is written to follow the structure of the original text.
  revert a; apply induction
  . intro hbc
    rwa [zero_add, zero_add] at hbc
  intro a ih
  intro hbc
  rw [succ_add, succ_add] at hbc
  replace hbc := succ_cancel hbc
  exact ih hbc


/-- (Not from textbook) Nat can be given the structure of a commutative additive monoid. -/
instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- Definition 2.2.7 (Positive natural numbers).-/
def Nat.isPos (n:Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n:Nat) : n.isPos ↔ n ≠ 0 := by rfl

/-- Proposition 2.2.8 (positive plus natural number is positive).-/
theorem Nat.pos_add {a:Nat} (b:Nat) (ha: a.isPos) : (a + b).isPos := by
  -- this proof is written to follow the structure of the original text.
  revert b; apply induction
  . rwa [add_zero]
  intro b hab
  rw [add_succ]
  have : (a+b)++ ≠ 0 := succ_ne _
  exact this

theorem Nat.add_pos {a:Nat} (b:Nat) (ha: a.isPos) : (b + a).isPos := by
  rw [add_comm]
  exact pos_add _ ha

/-- Corollary 2.2.9 (if sum vanishes, then summands vanish).-/
theorem Nat.add_eq_zero (a b:Nat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  -- this proof is written to follow the structure of the original text.
  by_contra h
  simp only [not_and_or, ←ne_eq] at h
  rcases h with ha | hb
  . rw [← isPos_iff] at ha
    have : (a + b).isPos := pos_add _ ha
    contradiction
  rw [← isPos_iff] at hb
  have : (a + b).isPos := add_pos _ hb
  contradiction

--Textbook
--interesting induction proof
-- we don't make use of the induction axiomn in the inductive step, but it's still
--necessary since it makes our inductive goal step symmetric and allows us to make
--use of axiom 2.4 which states that if b++=a++ then b=a
/-- Lemma 2.2.10 (unique predecessor) / Exercise 2.2.2 -/
lemma Nat.uniq_succ_eq (a:Nat) (ha: a.isPos) : ∃! b, b++ = a := by
  revert a
  apply induction
  · rw[ Nat.isPos ]
    intro h
    contradiction
  intro a hd hp -- ⊢ ∃! b, b++ = a++ there exists a unique b such that b++ = a++ for all a
  use a
    -- our goal is that we want unique object b that exists
    -- when we say use a , we're saying that we pressupose that unique object b= a

  -- now goal changes to ⊢ (fun b ↦ b++ = a++) a ∧ ∀ (y : Nat),
          --fun b then b++= a++ is simply lambda calculus
          -- λ b, b++ = a+
          -- For all natural numbers y  ,  if y is true that
          -- for all natural nubmers y  that fulfills the lambda ocndition y is then equal to a
          -- that is all possibilities is narrowed to a unique a


        -- (fun b ↦ b++ = a++) y → y = a
        -- before  we had there exists a unique b such that b++=a++
        -- now have in a wordy form taht there an explicit a
  constructor -- we split into two goals
  · rfl
  intro c hc
  --c is some natural number, hc is c++ = a++
  exact Nat.succ_cancel hc

/-- Definition 2.2.11 (Ordering of the natural numbers) -/
instance Nat.instLE : LE Nat where
  le n m := ∃ a:Nat, m = n + a

/-- Definition 2.2.11 (Ordering of the natural numbers) -/
instance Nat.instLT : LT Nat where
  lt n m := (∃ a:Nat, m = n + a) ∧ n ≠ m

lemma Nat.le_iff (n m:Nat) : n ≤ m ↔ ∃ a:Nat, m = n + a := by rfl

lemma Nat.li_iff (n m:Nat) : n < m ↔ (∃ a:Nat, m = n + a) ∧ n ≠ m := by rfl

lemma Nat.ge_iff_le (n m:Nat) : n ≥ m ↔ m ≤ n := by rfl

lemma Nat.gt_iff_lt (n m:Nat) : n > m ↔ m < n := by rfl

lemma Nat.le_of_lt {n m:Nat} (hnm: n < m) : n ≤ m := hnm.1

lemma Nat.le_iff_lt_or_eq (n m:Nat) : n ≤ m ↔ n < m ∨ n = m := by
  rw [Nat.le_iff, Nat.li_iff]
  by_cases h : n = m
  . simp [h]
    use 0
    rw [add_zero]
  simp [h]

example : (8:Nat) > 5 := by
  rw [Nat.gt_iff_lt, Nat.li_iff]
  constructor
  . have : (8:Nat) = 5 + 3 := by rfl
    rw [this]
    use 3
  decide

--Textbook
theorem Nat.succ_gt (n:Nat) : n++ > n := by
  constructor
  use 1
  rw[succ_eq_add_one]
  rw[succ_eq_add_one]
  nth_rewrite 1 [← add_zero n]
  by_contra h
  apply add_cancel_left at h
  contradiction


/-- Proposition 2.2.12 (Basic properties of order for natural numbers) / Exercise 2.2.3
-- Proove reflexisivity,transitivity, and antisymmetrtric order,
(a) (Order is reflexive). -/
theorem Nat.ge_refl (a:Nat) : a ≥ a := by
  use 0
  symm
  rw[add_zero]

/-- (b) (Order is transitive) -/
theorem Nat.ge_trans {a b c:Nat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  rw[ge_iff_le]
  rw[ge_iff_le,le_iff] at hab
  rw[ge_iff_le,le_iff] at hbc
  rcases hab with ⟨k, rfl⟩      -- replaces `a` with `b + k`
  rcases hbc with ⟨l, rfl⟩      -- replaces `b` with `c + l`

  use l+k
  exact add_assoc c l k


/-- (c) (Order is anti-symmetric)  -/
theorem Nat.ge_antisymm {a b:Nat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  rw[ge_iff_le,le_iff] at hab
  rw[ge_iff_le,le_iff] at hba

  rcases hab with ⟨k, rfl⟩

  rcases hba with ⟨l, h⟩
  nth_rewrite 1 [← add_zero b] at h
  rw[add_assoc] at h

  apply add_cancel_left at h
  symm at h
  apply add_eq_zero at h
  rw[h.left]
  rw[add_zero]




/-- (d) (Addition preserves order)  -/
theorem Nat.add_ge_add_right (a b c:Nat) : a ≥ b ↔ a + c ≥ b + c := by
  constructor
  intro h
  rw[ge_iff_le,le_iff] at h
  rw[ge_iff_le,le_iff]
  rcases h with ⟨k,rfl ⟩
  rw[add_assoc]
  nth_rewrite 2 [add_comm]
  --nth_rewrite 1 [← add_assoc]
  rw[← add_assoc]
  use k
  intro h
  rw[ge_iff_le,le_iff] at h
  rw[ge_iff_le,le_iff]

  rcases h with ⟨k,hk ⟩
  use k

  rw[← add_comm] at hk
  nth_rewrite 1 [add_assoc] at hk

  nth_rewrite 2 [← add_comm] at hk
  rw[add_assoc] at hk

  apply add_cancel_left at hk
  rw[add_comm]
  exact hk





/-- (d) (Addition preserves order)  -/
theorem Nat.add_ge_add_left (a b c:Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

/-- (d) (Addition preserves order)  -/
theorem Nat.add_le_add_right (a b c:Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

/-- (d) (Addition preserves order)  -/
theorem Nat.add_le_add_left (a b c:Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _


--This took way longer that I thought it would. Is there a simpler way to prove this?
/-- (e) a < b iff a++ ≤ b. -/
theorem Nat.lt_iff_succ_le (a b:Nat) : a < b ↔ a++ ≤ b := by
  constructor
  · intro h
    rw[li_iff] at h
    --rw[le_iff]
    rcases h with ⟨h1,h2⟩
    rcases h1 with  ⟨m,h3⟩

    let h:m ≠ 0 := by
      rw[h3] at h2
      by_contra h3
      · rw[h3] at h2
        rw[add_zero]  at h2
        contradiction

    --use 0
    rw[← isPos_iff] at h
    apply uniq_succ_eq m at h
    rcases h with ⟨m, ⟨hb, _uniq⟩⟩
    subst hb
    rw[add_succ] at h3
    rw[← succ_add]  at h3
    --rw[succ_eq_add_one] at h3
    --rw[add_assoc]  at h3
    have h3_exists : ∃ m, b = a++ + m :=
  ⟨m, h3⟩


    rw[← le_iff] at h3_exists
    exact h3_exists
  intro h
  rw[le_iff] at h
  rcases h with ⟨m,h2⟩
  rw[li_iff]
  --rw[succ_add] at h2
  rw[succ_eq_add_one] at h2
  let hr: a≠b :=by
    by_contra h3
    rw[h3] at h2
    rw[add_assoc] at h2
    nth_rewrite 1[← add_zero b] at h2
    apply add_cancel_left at h2
    contradiction

  rw [add_assoc] at h2

  let h2_exists : ∃ a_1,b=a+a_1  := by
    use (1 + m)
  exact And.intro h2_exists hr


-- adding  a small lemma
--lemma Nat.succ_pos {a : Nat}  : (a++).isPos :=by exact Nat.succ_ne a


/-- (f) a < b if and only if b = a + d for positive d. -/
theorem Nat.lt_iff_add_pos (a b:Nat) : a < b ↔ ∃ d:Nat, d.isPos ∧ b = a + d := by
  constructor
  · intro h
    rw[lt_iff_succ_le] at h
    rw[le_iff] at h
    rw[succ_eq_add_one] at h
    rcases h with ⟨n,h2⟩
    rw[add_assoc] at h2
    nth_rewrite 2 [add_comm]  at h2
    rw[← succ_eq_add_one] at h2
    use (n++)
    let h3:  (n++).isPos  :=by exact Nat.succ_ne n
    exact ⟨h3,h2⟩
  · intro h
    rcases h with ⟨n,⟨h2,h3⟩⟩
    rw[isPos_iff] at h2
    --let h3_exists:∃m, b = a+n:=⟨n,b⟩
    rw[li_iff]
    have h_exists : ∃ m, b = a + m :=by use n
    have hnot: a≠ b:=by
      symm at h3
      by_contra h
      rw[h] at h3
      nth_rewrite 2 [← add_zero b] at h3
      apply add_cancel_left at h3
      contradiction
    --exact ⟨h_exists,hnot⟩
    tauto


/-- If a < b then a ̸= b,-/
theorem Nat.ne_of_lt (a b:Nat) : a < b → a ≠ b := by
  intro h; exact h.2

/-- if a > b then a ̸= b. -/
theorem Nat.ne_of_gt (a b:Nat) : a > b → a ≠ b := by
  intro h; exact h.2.symm

/-- If a > b and a < b then contradiction -/
theorem Nat.not_lt_of_gt (a b:Nat) : a < b ∧ a > b → False := by
  intro h
  have := (ge_antisymm (Nat.le_of_lt h.1) (Nat.le_of_lt h.2)).symm
  have := ne_of_lt _ _ h.1
  contradiction


/-- Proposition 2.2.13 (Trichotomy of order for natural numbers) / Exercise 2.2.4 -/
theorem Nat.trichotomous (a b:Nat) : a < b ∨ a = b ∨ a > b := by
  -- this proof is written to follow the structure of the original text.
  revert a; apply induction
  . have why : 0 ≤ b := by
      sorry
    replace why := (Nat.le_iff_lt_or_eq _ _).mp why
    tauto
  intro a ih
  rcases ih with case1 | case2 | case3
  . rw [lt_iff_succ_le] at case1
    rw [Nat.le_iff_lt_or_eq] at case1
    tauto
  . have why : a++ > b := by sorry
    tauto
  have why : a++ > b := by sorry
  tauto

/-- (Not from textbook) The order is decidable.  This exercise is only recommended for Lean experts. -/
instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := by
  sorry

/-- (Not from textbook) Nat has the structure of a linear ordering. -/
instance Nat.linearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_le := sorry
  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total := sorry
  toDecidableLE := decidableRel

/-- (Not from textbook) Nat has the structure of an ordered monoid. -/
instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left := by
    intro a b hab c
    exact (add_le_add_left a b c).mp hab

/-- Proposition 2.2.14 (Strong principle of induction) / Exercise 2.2.5
-/
theorem Nat.strong_induction {m₀:Nat} {P: Nat → Prop} (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) : ∀ m, m ≥ m₀ → P m := by
  sorry

/-- Exercise 2.2.6 (backwards induction) -/
theorem Nat.backwards_induction {n:Nat} {P: Nat → Prop}  (hind: ∀ m, P (m++) → P m) (hn: P n) : ∀ m, m ≤ n → P m := by
  sorry

/-- Exercise 2.2.7 (induction from a starting point) -/
theorem Nat.induction_from {n:Nat} {P: Nat → Prop} (hind: ∀ m, P m → P (m++)) : P n → ∀ m, m ≥ n → P m := by
  sorry



end Chapter2
