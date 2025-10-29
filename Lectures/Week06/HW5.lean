
import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false


-- # Problem 1: Finding Min Recursively
def minimum (a b:ℕ ): ℕ := if a < b then a else b

-- Consider the following FindMin function
def FindMin (l : List ℕ) : ℕ :=
  match h: l with
  | [] => 0   -- Base case for empty list (0 is minimum in ℕ)
  | x::xs =>
      if he: xs = [] then x
      else
        have: 1 < l.length := by
          simp [h]
          by_contra!
          observe: xs.length = 0
          simp_all only [le_refl, List.length_eq_zero_iff]
        let n := l.length
        let left  := l.take (n / 2)
        let right := l.drop (n / 2)
        -- Recursive step: find max of each half and compare
        minimum (FindMin left) (FindMin right)
termination_by l.length decreasing_by all_goals grind

def Nat.MinOfList (a :ℕ ) (t: List ℕ) : Prop := ∀ y ∈ t, a ≤ y

-- You can use the following APIs.
-- # In this problem, prove that the FindMin algorithm correctly returns the minimum element for any non-empty input list of size n.
-- You may find the following theorems useful
theorem x_minlist_of_x_lt_minlist {x y: ℕ} {l: List ℕ } (h1: x ≤ y) (h2 : y.MinOfList l) : x.MinOfList l := by grind [Nat.MinOfList]
theorem min_list_of_left_right {x : ℕ} {l : List ℕ} (left right: List ℕ) (h_lr: left ++ right = l)
(h_min_left: x.MinOfList left)(h_min_right: x.MinOfList right): x.MinOfList (l) := by grind [Nat.MinOfList]

theorem Problem1 (l : List ℕ) (h_nonempty : l.length > 0) :
   let z := FindMin l
   z.MinOfList l := by
    fun_induction FindMin
    · tauto
    · simp [Nat.MinOfList];
    · simp
      apply min_list_of_left_right left right <;> simp_all
      · unfold left right; aesop
      · grind [Nat.MinOfList, minimum]
      · grind [Nat.MinOfList, minimum]

-- # Problem 2: Finding Min Sequentially
-- Define minimum property
def Option.MinOfList (result : Option ℕ) (l : List ℕ) : Prop :=
  match result with
  | none => l = []
  | some m => m ∈ l ∧ ∀ x ∈ l, m ≤ x

def List.minHelper (xs : List ℕ)(val_so_far : ℕ) : ℕ := match xs with
  | [] => val_so_far
  | x :: xs => xs.minHelper (min x val_so_far)

def List.FindMin : List ℕ → Option ℕ
  | [] => none
  | x :: xs => some (xs.minHelper x)

-- # In problem 2, prove that FindMIn function correctly compute the mininmum
lemma Problem2 (l : List ℕ) : l.FindMin.MinOfList l := by
  match l with
  | [] => simp!
  | x::xs => {
    rw [List.FindMin]
    generalize g0 : (xs.minHelper x) = n
    rw [Option.MinOfList]
    constructor
    · simp; revert x; induction' xs with x' xs' IH
      · simp!;
      · intro x H; simp
        rw [List.minHelper] at H; apply IH at H
        cases H
        · subst h; rw[←or_assoc]
          left; simp!
          omega
        · right;right;trivial
    · revert x; induction' xs with x' xs' IH
      · simp_all!
      · intro n' H
        rw [List.minHelper] at H; apply IH at H
        intro z H'; simp at H'
        obtain h|h|h := H'
        · subst h; specialize H (min x' z); simp at H; exact H.right
        · subst h; specialize H (min z n'); simp at H; exact H.left
        · specialize H z; simp [h] at H; trivial
  }



-- For problem 3 and 4, we will use the following version of Merge and Sorted
-- # Merge
def Merge: List ℕ → List ℕ → List ℕ
  | x, [] => x
  | [], x => x
  | x::xs, y::ys =>
    if x ≤ y then x :: Merge xs (y::ys)
    else y :: Merge (x :: xs) ys

-- # Sorted
inductive Sorted: List ℕ  → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ ) (t : List ℕ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a :ℕ) (t : List ℕ) : a.MinOfList t  → Sorted (t) →  Sorted (a :: t)

-- # Problem 3: Prove that y ∈ Merge xs (y :: ys)
-- You may find this List functions helpful
#check List.mem_cons_of_mem
#check List.mem_cons_self

theorem Problem3 (y : ℕ) (xs ys: List ℕ) : y ∈ Merge xs (y :: ys) := by
  revert y
  match xs,ys with
  | [], [] => simp[Merge]
  | x::xs, [] => {
    revert x; induction' xs with x' xs' IH
    · intro y;simp[Merge];aesop
    · intro x y;unfold Merge;split
      · simp;right;apply IH
      · simp
  }
  | [], y::ys =>{
    unfold Merge; simp
  }
  | x::xs, ys => {
    revert x ys; induction' xs with x' xs' IH
    · grind[Merge]
    · intro x0 xs0 y0; unfold Merge; split_ifs <;> try simp
      right;apply IH
  }


-- # Problem 4: Prove that Merge function is commutative on sorted inputs
-- `nth_rewrite` tactic can be useful to rewrite a specific occurence
-- You may find this function useful and you may find the API about merge and sorted helpful
#check Merge.eq_def

-- # API about Merge
-- In this homework, let's assume you have access to the following theorems.
-- Proving these theorems are optional.
theorem sorted_suffix {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) : Sorted xs := by
  induction' xs with x' xs' IH
  · tauto
  · grind[Sorted]
theorem sorted_min {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) :  x.MinOfList xs  := by
  induction' xs with x' xs' IH
  · tauto
  · grind[Sorted, Nat.MinOfList]
theorem merge_min_out (x : ℕ) (xs ys : List ℕ) (h_min_in_xs : ∀ y ∈ xs, x ≤ y) :
Merge (x :: ys) xs = x :: Merge ys xs := by
  fun_induction Merge
  · unfold Merge; trivial
  · unfold Merge; split <;> try grind[Merge]
  · grind[Merge]
  · grind[Merge]
theorem merge_min_out_sym(x : ℕ) (xs ys : List ℕ) (h_min_in_xs : ∀ y ∈ xs, x ≤ y) (h_min_in_ys : ∀ y ∈ ys, x ≤ y) :
Merge ys (x ::xs)  = x :: Merge ys xs := by
  rename' h_min_in_xs => hxs, h_min_in_ys => hys
  revert x ys
  induction' xs with x' xs' IH0
  · intro x ys; simp[Merge]; revert x
    induction' ys with y' ys' IH1
    · simp[Merge]
    · intro x h; simp[Merge]; intro le; simp at h; obtain ⟨h0,h1⟩ := h
      constructor
      · omega
      · apply (IH1 x) at h1
        rw [show y'=x from by omega]; trivial
  · simp; intro x ys le h0 h1
    induction' ys with y' ys' IH1
    · simp[Merge]
    · simp[Merge]; intro le1; simp at h1; obtain ⟨hl,hr⟩ := h1
      split_ifs with h
      · constructor
        · omega
        · simp_all; omega
      · simp_all; grind
theorem Problem4  (xs ys: List ℕ) (h1: Sorted xs) (h2: Sorted ys):
Merge xs ys = Merge ys xs := by
  fun_induction Merge xs ys
  · induction x <;> grind[Merge]
  · simp_all[Merge]
  · specialize ih1 (sorted_suffix h1) h2
    rw [ih1,←merge_min_out_sym]
    {rw[←Nat.MinOfList];apply sorted_min at h1;trivial}
    simp; constructor
    · trivial
    · apply sorted_min at h2; unfold Nat.MinOfList at h2; grw[←h] at h2
      trivial
  · specialize ih1 h1 (sorted_suffix h2)
    rw[ih1,←merge_min_out]
    simp_all; constructor
    · omega
    · apply sorted_min at h1; unfold Nat.MinOfList at h1; grw[<-h] at h1
      trivial

-- # Problem 5: Prove that the index returned by this contain_bs correctly corresponds to q
-- Consider the following SortedArrayFun and contain_bs function

structure SortedArrayFun (n :ℕ) where
  get : ℕ → ℕ
  size : ℕ := n
  sorted: Monotone get

def contains_bs {n :ℕ }(arr : SortedArrayFun n) (q : ℕ) : Option ℕ :=
  bs_aux 0 (n-1) (by omega)
  where bs_aux (a b :ℕ) (h: a ≤ b): Option ℕ  :=
  if h: a = b then
    if q = arr.get a then some a
    else none
  else
    let mid := (a+b)/(2 :ℕ )
    if      q < arr.get mid then bs_aux a mid  (by omega)
    else if  arr.get mid < q then bs_aux (mid+1) b (by omega)
    else some mid

lemma genP5 (n q a b:ℕ)(h: 0 < n)(h0: a ≤ b)(arr : SortedArrayFun n):
  ∀ i, contains_bs.bs_aux arr q a b h0 = some i → arr.get i = q := by
  fun_induction contains_bs.bs_aux arr q a b h0 <;> grind

theorem Problem5 (n q :ℕ)(h: 0 < n)(arr : SortedArrayFun n):
  ∀ i, contains_bs arr q = some i → arr.get i = q := by
  unfold contains_bs
  refine (genP5 n q 0 (n-1) h _ arr)
