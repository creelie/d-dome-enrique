import AntiprismLean.Identity
import AntiprismLean.Signs

/-!
# Step 1 for polynomials

With `T = rev_n` and `S = x · rev_{n-1}` (where `rev_d p = x^d p(1/x)` is
`Polynomial.reflect d p`), the abstract telescoping identity becomes the
polynomial identity

  `H - rev_n H = ∑_{i=1}^{n} (x · rev_{n-1} P_i - P_i)`,  `H = ∑_{j=0}^{n} (j+1) f_j`,

valid whenever `deg f_j ≤ n-1` for `j < n`, `rev_n f_n = P_n` and `f_n = x · rev_{n-1} P_n`.
For the antiprism data `H = h_{n+1}` and `H - rev_n H = (x-1) b_{n+1}`, while
`x · rev_{n-1} P - P = (x-1) a(P)`; dividing by `x - 1` gives `b_{n+1} = ∑ a(P_i)`.
-/

open Polynomial Finset

variable {R : Type*} [CommRing R]

/-- `rev_d` as an additive map. -/
noncomputable def revHom (d : ℕ) : R[X] →+ R[X] :=
  AddMonoidHom.mk' (reflect d) (fun p q => reflect_add p q d)

/-- `x · rev_d` as an additive map. -/
noncomputable def xrevHom (d : ℕ) : R[X] →+ R[X] :=
  AddMonoidHom.mk' (fun p => X * reflect d p) (fun p q => by rw [reflect_add, mul_add])

theorem step_one (m : ℕ) (f : ℕ → R[X])
    (hdeg : ∀ j < m + 1, (f j).natDegree ≤ m)
    (htop : reflect (m + 1) (f (m + 1)) = ∑ j ∈ range (m + 1), f j)
    (hfn : f (m + 1) = X * reflect m (∑ j ∈ range (m + 1), f j)) :
    (∑ j ∈ range (m + 2), (j + 1) • f j) - reflect (m + 1) (∑ j ∈ range (m + 2), (j + 1) • f j)
      = ∑ i ∈ range (m + 1),
          (X * reflect m (∑ j ∈ range (i + 1), f j) - ∑ j ∈ range (i + 1), f j) := by
  have := telescoping_identity (revHom (m + 1)) (xrevHom m) f (m + 1)
    (fun j hj => reflect_succ_of_natDegree_le (f j) m (hdeg j hj)) htop hfn
  exact this

/-- `(x - 1) a(P) = x · rev_{n-1} P - P`, and `(x-1) b = H - rev H`, so `b = ∑ a(P_i)`. -/
theorem b_eq_sum_a {K : Type*} [Field K] (m : ℕ) (H b : K[X]) (P a : ℕ → K[X])
    (hb : (X - 1) * b = H - reflect (m + 1) H)
    (ha : ∀ i, (X - 1) * a i = X * reflect m (P i) - P i)
    (hid : H - reflect (m + 1) H = ∑ i ∈ range (m + 1), (X * reflect m (P i) - P i)) :
    b = ∑ i ∈ range (m + 1), a i := by
  apply cancel_X_sub_one
  rw [hb, hid, mul_sum]
  exact sum_congr rfl fun i _ => (ha i).symm
