import Mathlib

/-!
# The sign step

Step 4 of the proof: at a negative root `β` of `h_n`, the values of `P_i` and of
`rev P_i` carry the sign `(-1)^(k-1)`, and the identity
`(β - 1) a(P)(β) = β · rev P(β) - P(β)` transfers this sign to `a(P)(β)`.
Also the reflection facts used to put the antiprism data into the shape of
`telescoping_identity`.
-/

open Polynomial

theorem sign_transfer (β p r a : ℝ) (k : ℕ) (hβ : β < 0)
    (hp : 0 ≤ (-1) ^ k * p) (hr : 0 ≤ (-1) ^ k * r)
    (ha : (β - 1) * a = β * r - p) : 0 ≤ (-1) ^ k * a := by
  have h1 : (β - 1) * ((-1) ^ k * a) = β * ((-1) ^ k * r) - (-1) ^ k * p := by
    linear_combination (-1) ^ k * ha
  have h2 : (β - 1) * ((-1) ^ k * a) ≤ 0 := by
    rw [h1]; nlinarith
  by_contra hneg
  have hneg' : (-1) ^ k * a < 0 := lt_of_not_ge hneg
  nlinarith

/-- Summing the sign condition (finite sums preserve it). -/
theorem sign_condition_sum {ι : Type*} (s : Finset ι) (c : ℝ) (v : ι → ℝ)
    (h : ∀ i ∈ s, 0 ≤ c * v i) : 0 ≤ c * ∑ i ∈ s, v i := by
  rw [Finset.mul_sum]; exact Finset.sum_nonneg h

/-- `x^n p(1/x) = x · x^(n-1) p(1/x)` when `deg p ≤ n - 1`. -/
theorem reflect_succ_of_natDegree_le {R : Type*} [CommRing R] (p : R[X]) (m : ℕ)
    (hp : p.natDegree ≤ m) : reflect (m + 1) p = X * reflect m p := by
  have h1 : reflect 1 (1 : R[X]) = X := by
    simp
  have := reflect_mul p (1 : R[X]) (F := m) (G := 1) hp (by simp)
  rw [mul_one, h1] at this
  rw [this, mul_comm]

/-- `x^(m+1) (x q)(1/x) = x^m q(1/x)`. -/
theorem reflect_X_mul {R : Type*} [CommRing R] (q : R[X]) (m : ℕ) (hq : q.natDegree ≤ m) :
    reflect (m + 1) (X * q) = reflect m q := by
  have := reflect_mul (X : R[X]) q (F := 1) (G := m) natDegree_X_le hq
  rw [add_comm 1 m, reflect_one_X, one_mul] at this
  exact this
