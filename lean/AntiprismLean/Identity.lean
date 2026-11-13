import Mathlib

/-!
# The telescoping identity behind the antiprism interlacing theorem

Let `T` and `S` be additive maps on an additive commutative group and let
`f 0, …, f n` satisfy `T (f j) = S (f j)` for `j < n`, `T (f n) = P n` and
`f n = S (P n)`, where `P i = f 0 + ⋯ + f (i-1)`.  Then

  `H - T H = ∑_{i=1}^{n} (S (P i) - P i)`,  where `H = ∑_{j=0}^{n} (j+1) • f j`.

In the paper `T = rev_n`, `S = x · rev_{n-1}`, `f j = q_{n-1-j,j}`, `H = h_{n+1}`,
and the identity reads `(x-1) b_{n+1} = ∑ (x-1) a(P_i)` (Step 1 of the proof).
-/

open Finset

variable {V : Type*} [AddCommGroup V]

/-- Double sum of partial sums. -/
lemma sum_partial_sums (g : ℕ → V) (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range (i + 1), g j = ∑ j ∈ range n, (n - j) • g j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun j => (n + 1 - j) • g j)]
    have h1 : ∑ j ∈ range n, (n + 1 - j) • g j
        = ∑ j ∈ range n, (n - j) • g j + ∑ j ∈ range n, g j := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun j hj => ?_
      have : n + 1 - j = (n - j) + 1 := by
        have := mem_range.mp hj; omega
      rw [this, succ_nsmul]
    rw [h1, sum_range_succ]
    simp only [Nat.add_sub_cancel_left, one_smul]
    abel

theorem telescoping_identity (T S : V →+ V) (f : ℕ → V) (n : ℕ)
    (hlow : ∀ j < n, T (f j) = S (f j))
    (htop : T (f n) = ∑ j ∈ range n, f j)
    (hfn : f n = S (∑ j ∈ range n, f j)) :
    (∑ j ∈ range (n + 1), (j + 1) • f j) - T (∑ j ∈ range (n + 1), (j + 1) • f j)
      = ∑ i ∈ range n, (S (∑ j ∈ range (i + 1), f j) - ∑ j ∈ range (i + 1), f j) := by
  have hT : T (∑ j ∈ range (n + 1), (j + 1) • f j)
      = ∑ j ∈ range n, (j + 1) • S (f j) + (n + 1) • ∑ j ∈ range n, f j := by
    rw [map_sum, sum_range_succ]
    congr 1
    · refine sum_congr rfl fun j hj => ?_
      rw [map_nsmul, hlow j (mem_range.mp hj)]
    · rw [map_nsmul, htop]
  rw [hT, sum_sub_distrib]
  simp only [map_sum]
  rw [sum_partial_sums (fun j => S (f j)) n, sum_partial_sums f n, sum_range_succ, hfn,
    map_sum]
  -- now a linear identity in the finitely many vectors `f j`, `S (f j)`
  have key : ∀ j ∈ range n, (j + 1) • f j + (n + 1) • S (f j)
      = (j + 1) • S (f j) + (n + 1) • f j + ((n - j) • S (f j) - (n - j) • f j) := by
    intro j hj
    have hj' : j < n := mem_range.mp hj
    have e : n + 1 = (j + 1) + (n - j) := by omega
    rw [e]
    simp only [add_nsmul, one_nsmul]
    abel
  have := sum_congr rfl key
  simp only [sum_add_distrib, sum_sub_distrib, ← smul_sum] at this
  rw [sub_eq_sub_iff_add_eq_add]
  rw [← sub_eq_zero] at this ⊢
  rw [← this]
  abel

/-- In a polynomial ring the identity can be divided by `X - 1`. -/
theorem cancel_X_sub_one {K : Type*} [Field K] {b a : Polynomial K}
    (h : (Polynomial.X - 1) * b = (Polynomial.X - 1) * a) : b = a :=
  mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero 1) (by simpa using h)
