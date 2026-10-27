/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.Paper.ConstantAdicQuotientScalarComparison
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Core data for a single finite quotient étale origin

Source: Stacks Project, Tags 09AL and 09B1.
(blueprint: lem-weil-pbc-lisse-finite-quotient-etale-origin).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/-- The descended level and its local finiteness data, before conditional transport.

Source: Stacks Project, proetale.tex, Tags 09AL and 09B1
(blueprint: lem-weil-pbc-lisse-finite-quotient-etale-origin-core).
-/
structure LisseFiniteQuotientEtaleOriginCore
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (K : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (V : Y.Etale) where
  level : DerivedCategory (Sheaf V.left.smallEtaleTopology
    (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
  lisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor _ q).obj level)
  vanishing : ∀ q : ℤ,
    IsZero ((DerivedCategory.homologyFunctor _ q).obj K) →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj level)
  refinementLisse : ∀ (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj V) (q : ℤ),
    IsRelativelyFiniteLisseModule (W.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict ((adicTowerInverseImage (W.hom ≫ g)).map
        (pbcLevelConstantComparison X d n).hom)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((adicTowerPullback (W.hom ≫ g)
              ((pbcAdicRings X d).obj (op n))).obj K)))

/-- Descend the level, vanishing and finite lisse data of one quotient.

Proof: apply exact inverse image, constant coefficient comparison and the finite
coefficient derived-origin theorem to the bounded complex; transfer the resulting
origin to the completion quotient and pull its covering sieves back along every
pro-étale refinement. The finite quotient and completion identifications preserve
the displayed cohomology and local models. This is the part of the construction
before the conditional constant-model transport.

Source: Stacks Project, proetale.tex, Tags 09AL and 09B1
(blueprint: lem-weil-pbc-lisse-finite-quotient-etale-origin-core).
-/
theorem lisse_finite_quotient_etale_origin_core
    (X Y : Scheme.{u}) [IsNoetherian X] (g : Y ⟶ X) [IsImmersion g]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (K : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (hbounded : ∃ a b : ℤ, ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hlisse : ∀ q : ℤ,
      IsRelativelyFiniteLisseModule g (A ⧸ d.ideal ^ (n + 1))
        ((pbcRestrict ((adicTowerInverseImage g).map
          (pbcLevelConstantComparison X d n).hom)).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj K))))
    (V : Y.Etale) :
    Nonempty (LisseFiniteQuotientEtaleOriginCore X Y g d n K V) := by
  sorry

end AlgebraicGeometry.Scheme
