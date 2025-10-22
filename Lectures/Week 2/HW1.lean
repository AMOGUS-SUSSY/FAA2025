import Mathlib.Tactic
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option tactic.hygienic false

/- # Instruction
In this homework, you are not allowed to use tactics outside the basic tactics listed below.
Basic tactics: `rfl`, `intro`, `exact`, `constructor`, `apply`, `rw`, `left`, `right`, `cases`, `by_cases`, `ext`, `trivial`,`contradiction`,`assumption`,`have`, `by_contra`, `rintro`

If you need to use different tactics, please justify why basic tactics in the list above are not sufficient.
In particular, you are not allowed to use automation (simp, aesop, grind, ring, omega, etc) to finish the goal.

**Instruction**:
(1) Fill each `sorry` with the appropriate tactics.
(2) For each problem, give an informal explanation of the proof strategy. This should correspond to your Lean proof.
**Submission**:  HW1.lean file in Moodle. The grading will be based on (1) and (2).

-/

/-
  Proof strategy for l0 is:
  Given x ∉ A and x ∈ A ∪ B for some x show that x ∈ B
    by case distinction over x ∈ A and x ∈ B
-/
section
open Set
variable {α : Type*}
variable {T : α}
variable (A B C : Set α)

lemma l0 : T ∉ A → T ∈ A ∪ B → T ∈ B := by
  intro H G
  cases G
  · contradiction
  · trivial

/-
  Proof strategy for P1 is:
  Prove both implication directions seperately.
  -->
  Given (B ∪ C) ⊆ A show that B ⊆ A and C ⊆ A
  Given both x ∈ B and x ∈ C on their own show x ∈ B ∪ C which in turn implies x ∈ A
  <--
  Given B ⊆ A, C ⊆ A and x ∈ B ∪ C show that x ∈ A
    using case distinction over x ∈ B and x ∈ C
-/

lemma P1 : (B ∪ C) ⊆ A ↔ B ⊆ A ∧ C ⊆ A := by
  rw [subset_def,subset_def,subset_def]
  constructor
  · intro h
    constructor
    · intro x' inB
      apply h
      left; trivial
    · intro x' inC
      apply h
      right; trivial
  · intro h x' inBC
    cases inBC
    · apply h.left; trivial
    · apply h.right; trivial



/-
  Proof strategy for P2 is:
  Rewrite E1 = E2 into x ∈ E1 ↔ x ∈ E2 and prove both implication directions seperately.
  -->
  Given x ∈ A ∩ (B ∪ C), i.e. x ∈ A and x ∈ B ∪ C show that x ∈ A ∩ B or x ∈ A ∩ C
    using case distinction over x ∈ B ∪ C and x ∉ B ∪ C
  <--
  Given x ∈ (A ∩ B) ∪ (A ∩ C) show that x ∈ A and x ∈ B ∪ C
    using case distinction over x ∈ A ∩ B and x ∈ A ∩ B
-/

theorem P2 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext;constructor
  · intro H
    cases H
    cases right
    · left ;exact ⟨left,h⟩
    · right;exact ⟨left,h⟩
  · intro H
    constructor
    · cases H
      · cases h;trivial
      · cases h;trivial
    · cases H
      · left;cases h;trivial
      · right;cases h;trivial

/-
  Proof strategy for P2' is:
  Rewrite E1 = E2 into x ∈ E1 ↔ x ∈ E2 and prove both implication directions seperately.
  -->
  Given x ∈ A ∪ (B ∩ C) show that x ∈ A ∪ B and x ∈ A ∪ C
    using case distinction over x ∈ A and x ∈ B ∩ C
  <--
  Given x ∈ (A ∪ B) ∩ (A ∪ C) show that x ∈ A ∪ B ∩ C
    using case distinction over x ∈ A and x ∉ A with help of
  - lemma l0
-/

theorem P2' : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext;constructor
  · intro H
    cases H
    · constructor
      · left;trivial
      · left;trivial
    · constructor
      · right;exact h.left
      · right;exact h.right
  · intro H
    cases H
    by_cases case: x ∈ A
    · left;trivial
    · apply (l0 A B case) at left
      apply (l0 A C case) at right
      right;exact ⟨left,right⟩


/-
  Proof strategy for P3 is:
  Prove both implication directions seperately.
  -->
  Given x ∈ A ∪ B, x ∈ A ∪ C and x ∈ B ∪ C for a x
    show that x ∈ (A ∩ B) ∪ (A ∩ C) ∪ (B ∩ C)
    by case distinction over x ∈ A and x ∉ A
    using lemmas P2 and l0
  <--
  Show that x ∈ (A ∪ B) ∩ (A ∪ C) ∩ (B ∪ C)
    by case distinction over x ∈ A ∩ B, x ∈ A ∩ C and x ∈ B ∩ C
    using lemma P2'
-/

theorem P3 : (A ∪ B) ∩ (A ∪ C) ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) ∪ (B ∩ C) := by
  ext
  constructor
  · rintro ⟨l,r⟩
    cases l
    by_cases case : x ∈ A
    · left
      rw[← P2]
      exact ⟨case,r⟩
    · right
      apply (l0 A B case) at left
      apply (l0 A C case) at right
      exact ⟨left,right⟩
  · rintro ⟨l,r⟩
    · rw [← P2'];constructor
      · left;trivial
      · left;trivial
    · constructor
      cases h
      · rw [← P2']
        left;trivial
      · right;exact h.right
    · rw [← P2'];constructor
      · right;trivial
      · right;exact h.right


-- The set difference operation is denoted by B \ A
-- This can be simplified using rw [mem_diff] where
#check mem_diff

-- In this theorem, the partial proof has been outlined.
-- Your task is to fill in the sorry
-- the following theorem can be helpful
#check subset_union_left

/-
  Proof strategy for P4 is:
  -->
  Assuming A ∪ X = B and x ∈ A for some given x show that x ∈ B
  <--
  Assuming A ⊆ B show that A ∪ X = B if X is set to B \ A
  Rewrite E1 = E2 as E1 ⊆ E2 ↔ E2 ⊆ E1 and prove both directions seperately
    -->
    Given x ∈ A ∪ B \ A show that x ∈ B
      using case distinction over x ∈ A and x ∈ B \ A
    <--
    Given x ∈ B show that x ∈ A ∪ B \ A
      using case distinction over x ∈ A and x ∉ A
-/

theorem P4 : (∃ X : Set α, A ∪ X = B) ↔ A ⊆ B := by
  constructor
  · -- Forward direction: if there exists X such that A ∪ X = B, then A ⊆ B
    intro H x ha
    obtain ⟨ X,H ⟩ := H
    rewrite [<-H]
    left;trivial
  · -- Reverse direction: if A ⊆ B, then there exists X such that A ∪ X = B
    intro h           -- "Assume A ⊆ B"
    use B \ A         -- "Let X = B \ A"
    ext x
    constructor
    · intro H
      cases H
      · exact (h h_1)
      · rw [mem_diff] at h_1
        exact h_1.left
    · intro H
      by_cases case : x ∈ A
      · left;trivial
      · right;rw [mem_diff]
        exact ⟨H,case⟩

end

section
variable {α : Type*} [DecidableEq α]
variable (A B C : Finset α)

open Finset
-- Finset is a set whose cardinality is bounded
-- If A is a Finset, then #A is the cardinality of the set

/- Recall rw tactics:
If thm is a theorem a = b, then as a rewrite rule,
  rw [thm] means to replace a with b, and
  rw [← thm] means to replace b with a.
-/

def IsEven (n : ℕ) : Prop := ∃ k, n = 2 * k
def IsDisjoint (A B: Finset α) : Prop := A ∩ B = ∅

-- you may find the following operations useful
#check card_union
#check card_eq_zero
#check Nat.two_mul


/-
  Proof strategy for P5 is:
  First prove that the cardinality of the union of two disjoint finite sets is
  equal to the sum of the cardinalities of each using
  - Principle of Inclusion-Exclusion
  - Properties of disjoint sets
  - Cardinality of ∅ being equal to 0
  Using the assumptions and the proven statement above finish the the proof by applying
  - Definition of even-ness
  - Definition of multiplying by 2 (usually trivial)
-/

theorem P5 (U : Finset α) (A B : Finset α)
(hAB : IsDisjoint A B) (hcard : #A = #B) (htotal : A ∪ B = U) : IsEven (#U) := by
  -- Hint: First prove the following claim:
  have AB_eq: #(A ∪ B) = #A + #B := by
    rw [card_union]
    -- rw[hcard, ← Nat.two_mul]
    have empty: #(A ∩ B) = 0 := by
      exact (card_eq_zero).2 (hAB)
    rw [empty]
    rfl
  rw [hcard, ← Nat.two_mul, htotal] at AB_eq
  rw [IsEven]
  constructor
  apply AB_eq
  -- Then use AB_eq to finish the proof
