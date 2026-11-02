/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.ProEtaleClosedCechPresentation
import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedCechClosedExact

/-! # Exactness of the affine closed Cech presentation on the closed fibre

Source: the matching-relations calculation in Steps 1--3 of
`lem-sp-proetale-closed-affine-cech-presentation-exact`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

-- The affineness and covering hypotheses are not needed on the closed side.
set_option linter.unusedVariables false in
/-- The affine closed Cech presentation is exact after restriction to the closed fibre.

Source: Steps 1--3 of `lem-sp-proetale-closed-affine-cech-presentation-exact`.
(blueprint: lem-sp-proetale-closed-affine-cech-closed-exact).

Proof: a special case of `closedCech_closed_restriction_exact`; the affineness and covering
hypotheses are not used. -/
theorem closedAffineCech_closed_restriction_exact
    (A : Type u) [CommRing A] [Finite A] {B O : Scheme.{u}}
    (b : O ⟶ B) [IsOpenImmersion b] [QuasiCompact b]
    (P : B.ProEt) (V : P.left.ProEt) (hV : IsAffine V.left)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      IsAffine (Presheaf.cechNerveObj U y).left.left)
    (hcover : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
      ProEt.topology P.left V)
    (q : ℕ) (T : CochainCorepresentingShortComplex
      (closedCechCoefficientFunctor A b P V U) q) :
    (T.complex.map (ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) b.closedComplement)).Exact :=
  closedCech_closed_restriction_exact A b P V U q T

end AlgebraicGeometry.Scheme
