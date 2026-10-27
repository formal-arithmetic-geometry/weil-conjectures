/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.AlgebraicGeometry.FormalHilbertStratumMinors

/-! # Formal low derivatives and coefficient derivatives -/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertCoefficient

open Classical in
/-- Low derivatives of an expanded formal family generate exactly the transverse
variables and the indicated tangential coefficient derivatives.

Source: BM 1997, Remark 9.5(1) and completion of Theorem 9.6, pp.277,282;
step 3 of the coefficient-order comparison
(blueprint: lem-trf-formal-low-derivative-coefficients).

Proof: If there are no vertices, essentiality forces n=0; both displayed spans
are empty. Otherwise take the largest vertex degree d. Every transverse variable
is essential at d. For the selected derivatives g_j, the equation alpha=beta+e_j
shows |beta|=|alpha|-1, hence g_j lies in the low-derivative ideal E. Their
membership in the transverse ideal allows factoring g=UZ: allocate each monomial
to its first transverse factor and remove that factor. The constant matrix U(0)
is the assumed transverse Jacobian. Its determinant is a unit in the power-series
ring, so the adjugate gives an inverse. Consequently (Z)=(g_j) is contained in E.
Modulo (Z), termwise differentiation of the given expansion gives
partial_W^delta partial_Z^gamma f_i = gamma! partial_W^delta c_i,gamma.
Mixed partials commute, and any exponent uniquely splits into its W and Z parts.
Its degree is the sum of their degrees. Thus the condition on the left is precisely
|gamma|<|alpha_i| and |delta|<|alpha_i|-|gamma| on the right. Every factorial
is a nonzero scalar, hence a unit in characteristic zero. The images of the two
ideals in the quotient by (Z) agree; since both contain (Z), the ideals agree.
For n=0 the same computation needs no Jacobian; degree-zero vertices contribute
no low derivatives and no coefficient tests. -/
theorem formal_lowDerivativeIdeal_eq_coefficients
    {L : Type u} [Field L] [CharZero L] {m n s : ℕ}
    (α : Fin s → Fin n →₀ ℕ)
    (hessential : ∀ l : Fin n, ∃ v : Fin s, 0 < α v l)
    (c : Fin s → (Fin n →₀ ℕ) → MvPowerSeries (Fin m) L)
    (f : Fin s → MvPowerSeries (Fin m ⊕ Fin n) L)
    (hexpansion : ∀ (l : Fin s) (d : (Fin m ⊕ Fin n) →₀ ℕ),
      MvPowerSeries.coeff d (f l) =
        MvPowerSeries.coeff (Finsupp.comapDomain.addMonoidHom Sum.inl_injective d)
          (c l (Finsupp.comapDomain.addMonoidHom Sum.inr_injective d)))
    (hblocks : ∀ d : ℕ, (∃ l : Fin s, (α l).degree = d) →
      ∃ (pick : {l : Fin n // essential α d l} → Fin s)
        (β : {l : Fin n // essential α d l} → Fin n →₀ ℕ),
        (∀ l, α (pick l) = β l + Finsupp.single l.val 1 ∧
          (α (pick l)).degree ≤ d ∧
          iteratedPartial (fullVertex m (β l)) (f (pick l)) ∈ transverseIdeal α d) ∧
        IsUnit (Matrix.det (fun l r : {l : Fin n // essential α d l} ↦
          MvPowerSeries.constantCoeff (MvPowerSeries.pderiv L (Sum.inr r.val)
            (iteratedPartial (fullVertex m (β l)) (f (pick l))))))) :
    lowDerivativeIdeal α f =
      Ideal.span (Set.range fun l : Fin n ↦
        (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin m ⊕ Fin n) L)) ⊔
      Ideal.span {g | ∃ (l : Fin s) (γ : Fin n →₀ ℕ) (δ : Fin m →₀ ℕ),
        γ.degree < (α l).degree ∧ δ.degree < (α l).degree - γ.degree ∧
          g = MvPowerSeries.rename Sum.inl (iteratedPartial δ (c l γ))} := by sorry

end AlgebraicGeometry.HilbertCoefficient
