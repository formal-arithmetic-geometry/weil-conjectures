/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralAffineCoefficientCounit.GeneralAffineCoefficientCounitNormalizationDefs

/-! The finite affine domain component of the general coefficient counit theorem.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-thm-smooth-purity/lem-pur-projection-purity-agreement.proof.md,
finite-coefficient realization (blueprint: lem-pur-affine-coefficient-counit-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.GeneralAffineCoefficientCounit
open AffineOrderedIntegrationGeneral FiniteCompactificationTranspose
variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The first conjunct of the general affine coefficient normalization.

Proof: choose a finite-Tor ordinary etale origin for the input, transport its Tor
window through coordinate pullback, finite Tate tensor, and shifts, and apply the
finite coefficient projection comparison to each coordinate compactification. The
ordered affine integration transpose supplies the unit dualizing comparison; the
ordinary and pro-etale projection equations then give the tensor normalization.
All these constructions are canonical and work for the zero ring and dimension zero.
-/
theorem general_affine_coefficient_domains
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) (hell : ell.Prime) (_hp : (ringChar k).Prime)
    (hne : ringChar k ≠ ell) (_hA : ∃ r : ℕ, ((ell ^ (r + 1) : ℕ) : A) = 0)
    {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : P A Y)
    (_hK : Etale.FiniteSmoothPurity.IsCtf A Y K) :
    letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
    letI : Fact ell.Prime := ⟨hell⟩
    AffineCoefficientCounit.FiniteAffineNormalization A ell Y
      (fun r ↦ baseUnit k ell hell hne (r + 1) aY) K := by
  sorry

end AlgebraicGeometry.ProEtale.GeneralAffineCoefficientCounit
