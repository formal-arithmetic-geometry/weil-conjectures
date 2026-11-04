/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction

/-!
# Agreement of published and specified finite compact-support site comparisons

Source documents: `literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-thm-pe-direct-image-comparison/prop-weil-pbc-comparison-direct-image.proof.md` and
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md` (blueprint:
lem-route-finite-compact-support-comparison-agreement).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale
open Scheme

set_option autoImplicit false


/-- Agreement of the published and specified compact-support comparisons.

Proof plan: (1) for each compactification, expand the published comparison through the
canonical open-extension comparison and the inverse of the canonical direct-image mate;
this is definitionally the fixed comparison, including all D⁺ inclusion and associator maps.
(2) Substitute these equalities into the definition of the published origin comparison and
cancel adjacent inverse isomorphisms to obtain the compactification-change equation.
(3) The normalized étale comparison and the origin comparison at an identical
compactification are identities by their identity clauses. (4) The remaining composite is
therefore the identity by the two-sided inverse laws. These are exactly the underived and
derived map steps of `literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-thm-pe-direct-image-comparison/prop-weil-pbc-comparison-direct-image.proof.md` and
Step 4 of `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md` (blueprint:
lem-route-finite-compact-support-comparison-agreement). -/
theorem finiteCompactSupportComparisonAgreement
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (c c₀ : Compactification f) :
    rightDerivedLowerShriekOfCompactificationComparisonIso (ModuleCat.{u + 1} A) c =
        fixedCompactSupportComparisonIso A c ∧
    rightDerivedLowerShriekOfCompactificationComparisonIso (ModuleCat.{u + 1} A) c₀ =
        fixedCompactSupportComparisonIso A c₀ ∧
    (∀ N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (fixedCompactSupportComparisonIso A c).hom.app N ≫
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
            ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c c₀).hom.app N) =
        (rightDerivedLowerShriekOfCompactificationOriginIso A c c₀).hom.app N ≫
          (rightDerivedLowerShriekOfCompactificationComparisonIso
            (ModuleCat.{u + 1} A) c₀).hom.app N) ∧
    Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c₀ c₀ = Iso.refl _ ∧
    rightDerivedLowerShriekOfCompactificationOriginIso A c₀ c₀ = Iso.refl _ ∧
    (∀ N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (rightDerivedLowerShriekOfCompactificationComparisonIso
          (ModuleCat.{u + 1} A) c₀).hom.app N ≫
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
            ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c₀ c₀).inv.app N) ≫
          (fixedCompactSupportComparisonIso A c₀).inv.app N =
        𝟙 ((DerivedCategory.Plus.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} A]) ⋙
          ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c₀).obj N)) := by
  have hcomparison (d : Compactification f) :
      rightDerivedLowerShriekOfCompactificationComparisonIso (ModuleCat.{u + 1} A) d =
        fixedCompactSupportComparisonIso A d := by
    have := d.isProper
    have hproper : rightDerivedLowerStarComparisonIso (ModuleCat.{u + 1} A) d.g =
        (fixedDirectImageComparisonIso A d.g).symm := by
      apply Iso.ext
      ext M
      simp [rightDerivedLowerStarComparisonIso, fixedDirectImageComparisonIso,
        fixedComparisonDirectImageMatePlus, rightDerivedLowerStarComparisonPlusIso,
        rightDerivedLowerStarComparisonPlusBaseChange]
    apply Iso.ext
    ext K
    simp [rightDerivedLowerShriekOfCompactificationComparisonIso,
      fixedCompactSupportComparisonIso, hproper]
  have hetale : Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c₀ c₀ =
      Iso.refl _ := by
    simp [Etale.rightDerivedLowerShriekOfCompactificationPlusιIso]
  refine ⟨hcomparison c, hcomparison c₀, ?_, hetale, ?_, ?_⟩
  · intro N
    rw [← hcomparison c]
    simp [rightDerivedLowerShriekOfCompactificationOriginIso]
  · apply Iso.ext
    ext K
    simp [rightDerivedLowerShriekOfCompactificationOriginIso, hetale]
  · intro N
    rw [hetale, hcomparison c₀]
    simp only [Iso.refl_inv, NatTrans.id_app]
    erw [CategoryTheory.Functor.map_id]
    simp

end AlgebraicGeometry.ProEtale
