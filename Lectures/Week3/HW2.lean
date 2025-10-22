import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
set_option autoImplicit false
set_option tactic.hygienic false

-- DO NOT CHANGE THE THEOREM STATEMENT
-- Fill in the sorry

-- Most tactics are welcome.
-- You are now allowed to use `aesop` and `grind` tactics.

-- Problem 1
def SumOdd : ℕ → ℕ
  | 0 => 0
  | n + 1 => SumOdd n + (2*n +1)

theorem P1 (n : ℕ) : SumOdd (n) = n^2 := by
  induction' n with n' IH
  · trivial
  · rw [SumOdd, IH]
    linarith

-- Problem 2 and 3
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
notation:10000 n "!" => factorial n

def isEven (n : ℕ) : Prop := ∃ k, n = 2*k

theorem P2 (n : ℕ) : isEven (n)! ↔ n ≥ 2 := by
  constructor
  · intro H
    induction' n with n' IH
    · simp_all! only [ factorial, isEven ]
      omega
    · by_cases prev : n' ≥ 1
      · grw [prev]
      · trans n'
        · omega
        · apply IH
          simp only [not_le, Nat.lt_one_iff] at prev
          subst n'
          simp_all! only [isEven, factorial]
  · intro H
    induction' n with n' IH
    · omega
    · by_cases prev : n' ≥ 2
      · specialize IH prev
        obtain ⟨k,hk⟩ := IH
        unfold factorial
        rw [hk]
        unfold isEven
        use (n' * k + k)
        ring
      · simp_all! only
          [ ge_iff_le,
            IsEmpty.forall_iff,
            Nat.reduceLeDiff,
            not_le,
            prev ]
        cases prev
        · simp_all! only
          [ zero_add,
            le_refl,
            Nat.reduceAdd,
            isEven ]
          norm_num
        · simp_all only
          [ Nat.succ_eq_add_one,
            zero_add,
            Nat.le_eq,
            add_le_iff_nonpos_left,
            nonpos_iff_eq_zero,
            one_mul,
            one_ne_zero ]

#check add_le_add_iff_left

theorem P3 : ∀ n > 0 , 3 ^ n > n ^ 2 := by
  intro n pre
  induction' pre with n pre' IH
  · trivial
  · by_cases cs : n ≤ 1
    · simp_all
      cases cs
      · trivial
      · simp_all
    · simp at cs
      clear pre'
      rw [show n.succ = n + 1 from rfl]
      calc
        3 ^ (n + 1) = 3 * 3 ^ n := by ring
        _ = 3^n + 3^n + 3^n := by ring
        _ > n^2 + 3^n := by grind
        _ ≥ n^2 + (2*n + 1) := by {
          simp_rw [add_le_add_iff_left]
          induction' cs with n' cs' IH0
          · trivial
          · simp_all
            nth_rw 2 [Nat.pow_succ] at IH
            simp_rw [add_sq, mul_one, one_pow] at IH
            trans (n' ^ 2 + 2 * n' + 1)
            · simp_rw [Nat.left_distrib, add_comm, add_le_add_iff_left]
              grw [<- cs']
              trivial
            · omega
        }
          _ = (n + 1) ^ 2 := by ring

-- # Problem 4:
-- in this problem, you are asked to solve the following recurrence relation.
-- g(n) = g(n/2) + 1, g(0) = 0
-- Prove that that g(n) ≤  Nat.log 2 n + 1 for all n
-- state the formal theorem and prove it

-- The following lemmas can be helpful
#check Nat.sub_add_cancel
#check Nat.le_log_of_pow_le

  def g4 : Nat → Nat
  | 0 => 0
  | n + 1 => g4 (n/2) + 1

  theorem P4 (x : ℕ) : g4 (x) ≤  Nat.log 2 x + 1 := by
    induction x using Nat.strong_induction_on
    rename' a => IH
    unfold g4
    if cs : n ≤ 2 then {
      split
      · norm_num
      · simp at cs
        specialize IH n_1
        simp_all
        cases n_1
        · norm_num
          unfold g4; trivial
        · simp_all
          unfold g4
          simp_all only [zero_le]
    }
    else {
      rw [ Nat.not_le ] at cs
      split
      · contradiction
      · rw [← Nat.add_one] at *
        rw [Nat.lt_add_one_iff] at cs
        specialize IH (n_1/2)
        rw [ Nat.log_div_base ] at IH
        rw [
          Nat.div_lt_iff_lt_mul (by omega),
          Nat.sub_add_cancel
        ] at IH
        have hp : (n_1 < (n_1 + 1) * 2) := by {
          ring_nf
          refine Nat.lt_add_left 2 ?_
          cases cs
          · norm_num
          · simp_all
        }
        specialize IH hp
        simp only [add_comm, add_le_add_iff_left]
        grw [IH]
        apply (Nat.log_mono_right)
        omega
        -- Where did this goal come from!? [I found out]
        apply Nat.log_pos
        · trivial
        · assumption
    }


-- # Problem 5
-- in this problem, you are asked to solve the following recurrence relation.
-- f(n) = 2*f(n-1) - f(n-2) + 2
-- where f(0) = 1 and f(1) = 1
-- Prove that that f(n) = n^2 - n + 1

  def g5 : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n+2 => 2*g5 (n+1) - g5 (n) + 2

  #eval g5 4

  theorem P5 (x : ℕ) : g5 (x) = x^2 - x + 1 := by
    induction x using Nat.twoStepInduction
    · trivial
    · trivial
    · rename' a => h0, a_1 => h1
      by_cases cs : n ≥ 2
      · unfold g5
        rw [h0, h1]
        simp
        rw [add_sq]; simp
        have fac0 : forall(x:Nat), x ≤ x ^ 2 := by {
          intro x; rw[pow_two]; refine Nat.le_mul_self x
        }
        -- REWRITING
        calc
          2 * (n ^ 2 + 2 * n - n + 1) - (n ^ 2 - n + 1) + 1
          _ = (n ^ 2 + n + 1) + ((n ^ 2 + n + 1) - (n ^ 2 - n + 1)) + 1 := by {
            rw [show 2*n = n+n by ring, Nat.add_sub_assoc];swap;linarith
            rw [Nat.add_sub_cancel, mul_comm 2, mul_two, Nat.add_sub_assoc];simp;linarith
          }
          _ = n ^ 2 + n + 1 + (n + 1 + (n ^ 2 - (n ^ 2 + 1 - n))) + 1 := by {
            nth_rw 2 [show n ^ 2 + n + 1 = n + 1 + n ^ 2 from by ring]
            rw [Nat.add_sub_assoc]
            swap;rw [←Nat.sub_add_comm];simp;omega;refine fac0 n
            rw [←Nat.sub_add_comm];refine fac0 n
          }
          _ = n ^ 2 + n + 1 + (n + ((n ^ 2 + 1) - (n ^ 2 + 1 - n))) + 1 := by omega
          _ = n ^ 2 + n + 1 + (n + n) + 1 := by {
            rw [Nat.sub_sub_self];nlinarith
          }
        -- REWRITING
        ring_nf
        symm
        calc
          4 + n * 4 + n ^ 2 - (2 + n)
          _ = n^2 + 3*n + 2 + (2 + n) - ( 2 + n ) := by omega
        rw [Nat.add_sub_assoc, Nat.add_sub_add_right]; simp; linarith
        rfl
      · simp at cs
        cases cs
        · simp_all!
        · simp_all!

-- state the formal theorem and prove it
-- Hint: you may find `zify` tactic useful
