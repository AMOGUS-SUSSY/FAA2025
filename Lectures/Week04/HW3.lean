import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
set_option autoImplicit false
set_option tactic.hygienic false

-- DO NOT CHANGE THE THEOREM STATEMENT
-- Fill in the sorry

-- All tactics are welcome.

-- # Problem 1
-- Prove that the list reverse operation does not change the length of the list.
def reverse {α : Type} : List α → List α
| [] => []
| a :: xs => reverse xs ++ [a]

def len {α : Type} : List α → ℕ
| []     =>  0
| _ :: xs => 1 + len xs

-- Helper lemma
lemma ins_conc_eq_len (a b : ℕ) (xs : List ℕ): len (a::xs) = len (xs ++ [b]) := by
  revert a b; fun_induction len xs
  all_goals try rename' xs_1=>xs',ih1=>IH
  · simp!
  · intro a' b';rw [List.cons_append]
    simp only [len]; congr
    rw [<-len.eq_2 a']; apply IH

-- Hint: use induction over the list
theorem problem1 (xs: List ℕ): len xs = len (reverse xs) := by
  fun_induction len xs
  all_goals try rename' xs_1=>xs, ih1=>IH
  · simp!
  · unfold reverse
    rw [IH,<-len.eq_2 a]
    refine ins_conc_eq_len a a (reverse xs)


-- # Problem 2: Consider the following rescursive function
def S : ℕ → ℕ  → ℕ
  | 0, 0 => 1
  | 0, _ => 0
  | _, 0 => 0
  | n+1, k =>
    if n + 1 = k then 1
    else k* (S n k) + (S n (k-1))

#check Nat.twoStepInduction

-- Hint: use induction over n
theorem problem2 (n: ℕ) (h: 0 < n): (S n 1) = 1 := by
  induction n using Nat.twoStepInduction
  · trivial
  · trivial
  · simp_all!


-- # Problem 3
-- This is a continuation of Problem 2
-- You may want to use the result from theorem problem2 to prove problem3
theorem problem3 (n: ℕ): (S n 2) = 2^(n-1) - 1  := by
  unfold S;split
  all_goals expose_names; try trivial
  simp
  clear x_2
  by_cases cs : n_1 = 0
  · subst cs; simp!
  · split <;> (expose_names)
    · subst h; simp
    · by_cases ct : n_1 < 2
      · omega
      · clear cs h x x_1;simp_all
        induction' ct with n' ct' IH
        · simp!
        · simp_all;rw [problem2] at *
          swap; linarith
          swap; linarith
          rw [Nat.pow_add_one,mul_two,Nat.add_sub_assoc]
          swap; exact Nat.one_le_two_pow
          rw [<-IH, S]; split
          · simp_all
          · norm_num
            rw[problem2]
            swap;linarith
            rw[IH, Nat.mul_sub, mul_comm 2 1, mul_two]
            rw[←Nat.sub_add_comm]
            swap; grw [<-Nat.one_le_two_pow]; simp
            rw [←Nat.add_sub_assoc]
            swap; exact Nat.one_le_two_pow
            omega
          · tauto

-- # Problem 4
/-
Define R(r,s):
  R(r,2) = r
  R(2,s) = s
  R(r,s) = R(m-1,n) + R(m,n-1)
  Prove that T(m,n) ≤ 2^{m+n}
-/

def R (r s : ℕ ): ℕ :=
  if r = 0 ∨ s = 0 then 0
  else if r ≤ 1 ∨ s ≤ 1 then 1
  else if r = 2 ∨ s = 2 then 2
  else (R (r-1) s) + (R r (s-1))

-- You may find this useful
#check Nat.choose_eq_choose_pred_add

-- Hint: you may find functional induction useful
lemma problem4 (r s : ℕ): R r s ≤ (r+s-2).choose (r-1) := by
  fun_induction R
  · simp_all
  · obtain ⟨hl,hr⟩ := h_1
    · simp_all
    · simp at a
      subst a
      simp
    · rw [Nat.one_le_iff_ne_zero]
      refine Nat.pos_iff_ne_zero.mp ?_
      apply Nat.choose_pos
      omega
  · simp at h_1
    obtain ⟨hl,hr⟩ := h_2
    · simp_all
      trivial
    · simp_all!
      subst h_2
      refine Nat.succ_le_of_lt ?_
      rw [Nat.choose_symm ?_]
      aesop
      order
  · simp_all
    grw [ih1, ih2]
    rw [
      show (r_1 + (s_1 - 1) - 2) = (r_1 - 1 + s_1 - 2) from by omega,
      show 2 = 1+1 from by linarith,
      Nat.sub_add_eq,
      ←Nat.choose_eq_choose_pred_add,
      Nat.sub_add_eq
    ]
    nth_rw 2 [Nat.sub_add_comm];omega
    · omega
    · omega


-- # Problem 5.1

-- Part 1: Defining interleave function
-- Define a function called interleave that takes two lists, xs and ys, and returns a new list where the elements of xs and ys are alternated.
-- If one list is longer than the other, the remaining elements of the longer list should be appended at the end.

def interleave : List ℕ → List ℕ → List ℕ
  | [], xs => xs
  | xs, [] => xs
  | x::xs, y::ys => x::y::(interleave xs ys)

 #eval interleave [1, 2, 3] [4, 5, 6] = [1, 4, 2, 5, 3, 6]
 #eval interleave [1, 2] [3, 4, 5, 6] = [1, 3, 2, 4, 5, 6]
 #eval interleave [1, 2, 3, 4] [5, 6] = [1, 5, 2, 6, 3, 4]
 #eval interleave [] [1, 2] = [1, 2]
 #eval interleave [1, 2] [] = [1, 2]

/--
 * interleave [1, 2, 3] [4, 5, 6] should produce [1, 4, 2, 5, 3, 6].
 * interleave [1, 2] [3, 4, 5, 6] should produce [1, 3, 2, 4, 5, 6].
 * interleave [1, 2, 3, 4] [5, 6] should produce [1, 5, 2, 6, 3, 4].
 * interleave [] [1, 2] should produce [1, 2].
 * interleave [1, 2] [] should produce [1, 2].
 --/

-- # Problem 5.2
-- Recall len and reverse functions from Problem 5.1
theorem problem5_part2 (xs ys: List ℕ): len (reverse (interleave xs ys))  = len (reverse (xs)) + len ys  := by
  simp only [←problem1]
  fun_induction interleave
  · simp!
  · simp!
  · simp_all!
    ring
