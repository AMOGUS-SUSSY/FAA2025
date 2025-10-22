import Mathlib.Tactic
set_option autoImplicit false
set_option tactic.hygienic false

-- All tactics are welcome.

-- # Problem 1: Predicate AllEven
-- Define Predicate `AllEven` is true if every number in the list is even.
-- e.g., [], [2], [8, 0, 4]
-- Complete the definition for AllEven. It should take a list of natural numbers (List ℕ) and return a Prop

def isEven (n :ℕ) : Prop := ∃k, n = 2*k

-- Your AllEven must use isEven function above
inductive AllEven : List ℕ → Prop
  | nil : AllEven []
  | succ (a : ℕ) (xs : List ℕ) : (isEven a) → AllEven xs → AllEven (a::xs)

-- Prove that your AllEven predicate is equivalent to checking if every element in the list is even.
-- Let's split into two parts

-- # Part 1
theorem Problem1_1 (l : List ℕ)  :
  AllEven l → ∀ n ∈ l, isEven n := by
  intro H
  induction' l with a xs' IH
  · simp
  · cases H
    simp_all

-- # Part 2
theorem Problem1_2 (l : List ℕ)  :
  (h : ∀ n ∈ l, isEven n) → AllEven l := by
  intro H
  induction' l with a xs' IH
  · tauto
  · simp_all
    apply AllEven.succ
    · simp_all
    · simp_all

-- # Sorted
-- We will use the following version of Sorted

def Nat.MinOfList (a :ℕ ) (t: List ℕ) : Prop := ∀ y ∈ t, a ≤ y

inductive Sorted: List ℕ  → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ ) (t : List ℕ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a :ℕ) (t : List ℕ) : a.MinOfList t  → Sorted (t) →  Sorted (a :: t)

-- # Problem 2: Prove that a list of length at most 1 is sorted.
def len : List ℕ → ℕ
| []     =>  0
| _ :: xs => 1 + len xs

lemma myCongr (xs : List ℕ) : (len xs) = (len []) ↔ xs = [] := by
  constructor
  · intro H
    unfold len at H
    cases xs <;> try trivial
    simp_all
  · intro H; subst H; trivial

theorem Problem2 (l : List ℕ) (h: len l ≤ 1): Sorted l := by
  fun_induction len l
  · tauto
  · simp_all; rewrite [←len.eq_1, myCongr] at h
    subst h
    tauto

-- # Problem 3: Prove basic properties of Sorted
theorem Problem3_1 {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) : Sorted xs := by
  induction' xs with x' xs' IH
  · tauto
  · cases hxs
    · trivial
    · simp_all

-- HELPER LEMMA 1 : allows me to remmove the head of List in a MinOfList relation
lemma min_elim {x y : ℕ} {t : List ℕ} : y.MinOfList (x::t) → y.MinOfList t := by
  intros h0
  unfold Nat.MinOfList at *
  induction' t with x' xs' IH
  · tauto
  · simp_all
-- HELPER LEMMA 2 : allows me to swap head from Sorted (Needed for HELPER LEMMA 3)
lemma sort_swap {x y : ℕ} {t : List ℕ} : x ≤ y → Sorted (y::t) → Sorted (x::t) := by
  intros h0 h1
  cases h1
  · tauto
  · grw [a_1] at h0
    apply Sorted.cons <;> trivial
  · unfold Nat.MinOfList at a_1
    grw [<-h0] at a_1
    apply Sorted.cons_min
    · unfold Nat.MinOfList; trivial
    · trivial
-- HELPER LEMMA 3 : allow me to remove the second element from Sorted
lemma mid_elim {x y : ℕ} {t : List ℕ} : Sorted (x::y::t) → Sorted (x::t) := by
  intro H
  cases H
  · apply (sort_swap a_1);trivial
  · unfold Nat.MinOfList at a_1
    specialize a_1 y
    simp_all
    apply (sort_swap a_1); trivial
theorem Problem3_2 {x y : ℕ} {t : List ℕ} (hsort : Sorted (x :: y :: t)) : y.MinOfList t := by
  by_contra cnt
  unfold Nat.MinOfList at cnt
  simp at cnt
  obtain ⟨z,⟨h0,h1⟩⟩ := cnt
  cases hsort
  · induction' t with x' xs' IH
    · trivial
    · apply IH
      simp at h0; cases h0
      · subst h
        cases a_2
        · omega
        · unfold Nat.MinOfList at a_3
          specialize a_3 z ; simp at a_3
          omega
      · trivial
      · apply mid_elim at a_2; trivial
  · apply min_elim at a_1
    unfold Nat.MinOfList at a_1
    induction' t with x' xs' IH
    · trivial
    · apply IH
      · specialize a_1 x'; simp at a_1
        simp at h0; cases h0
        · subst h
          cases a_2
          · omega
          · unfold Nat.MinOfList at a_3
            specialize a_3 z; simp at a_3
            omega
        · trivial
      · apply mid_elim at a_2; trivial
      · apply min_elim at a_1; trivial

-- # Problem 4: Alternate Definitions of Sorted
-- Consider the following inductive predicate
inductive Sorted2: List ℕ  → Prop
  | nil : Sorted2 []
  | single (a : ℕ) : Sorted2 [a]
  | cons (a b : ℕ ) (t : List ℕ ) : a ≤ b → Sorted2 (b :: t) → Sorted2 (a :: b :: t)

-- Prove that Sorted2 is equivalent to Sorted
-- You may find `ext` tactic useful
theorem Problem4 : Sorted2 = Sorted := by
  ext; constructor
  · induction' x with x' xs IH
    · tauto
    · intro H
      cases H
      · tauto
      · specialize IH a_2
        apply Sorted.cons <;> trivial
  · induction' x with x' xs IH
    · tauto
    · intro H
      cases H
      · tauto
      · specialize IH a_2
        apply Sorted2.cons <;> trivial
      · specialize IH a_2
        cases IH
        · tauto
        · apply Sorted2.cons
          · apply a_1
            simp_all only [List.mem_cons, List.not_mem_nil, or_false]
          · tauto
        · apply Sorted2.cons
          · unfold Nat.MinOfList at a_1
            specialize a_1 a; simp at a_1
            trivial
          · apply Sorted2.cons <;> trivial


-- # Problem 5: Binary Tree
-- Consider the following version of BinaryTree
inductive BinaryTree
  | nil
  | node (left : BinaryTree) (key : ℕ) (right : BinaryTree)

-- Define mirror operation as reversing the tree
def mirror : BinaryTree → BinaryTree
  | BinaryTree.nil        => BinaryTree.nil
  | BinaryTree.node l key r => BinaryTree.node (mirror r) key (mirror l)

-- Proof that mirror is injective
lemma inj_mirror : Function.Injective mirror := by
  unfold Function.Injective
  intro
  induction a₁
  · intro a l
    cases a
    · tauto
    · exfalso
      rw [mirror, mirror.eq_2] at l ; contradiction
  · intro a l
    induction a
    · contradiction
    · simp_all!
      obtain ⟨l0, ⟨ l1,l2 ⟩ ⟩ := l
      constructor
      · apply left_ih ; trivial
      · apply right_ih ; trivial

-- A binary tree is complete if every node has either two non-empty subtrees or two empty subtrees.
-- We can define it using inductive predicate as follows.

inductive Complete : BinaryTree  → Prop
  | leaf : Complete BinaryTree.nil
  | node  (l : BinaryTree) (key : ℕ) (r : BinaryTree)
      (hl : Complete l) (hr : Complete r)
      (hiff : l = BinaryTree.nil ↔ r = BinaryTree.nil) :
    Complete (BinaryTree.node l key r)

-- Prove that if a mirror of t is complete then t is complete
theorem Problem5:
    ∀t : BinaryTree, Complete (mirror t) → Complete t := by
    intro T h
    induction' T with tl k tr ihl ihr
    · tauto
    · rw [mirror] at h
      obtain ⟨ ⟩ := h
      apply Complete.node
      · specialize ihl hr ; trivial
      · specialize ihr hl ; trivial
      · obtain ⟨ ⟩ := hiff
        constructor
        · intro heq ; subst heq ; specialize mpr mirror.eq_1
          apply_fun mirror; rw [mirror] ; trivial
          apply inj_mirror
        · intro heq ; subst heq ; specialize mp mirror.eq_1
          apply_fun mirror ; rw [mirror] ; trivial
          apply inj_mirror
-- YIPPIE
