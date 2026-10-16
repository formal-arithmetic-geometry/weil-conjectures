/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleExtensionByZeroAdjunction
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Comparison of extension by zero on the etale and pro-etale sites

Source: Stacks Project, Tag 09AF (`lemma-jshriek-comparison`); Weil conjectures
blueprint, `sec-smooth-purity/sk-prop-sf-cbc`
(blueprint: lem-cbc-proetale-extension-zero-comparison).

The comparison is the existing adjunction mate
`openImmersionLowerShriekComparisonUpperStarIso`, not a chosen isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Canonical composition of pro-etale extension by zero, oriented from composite
extension to iterated extension. It is the unique left-adjoint comparison for the
canonical composition of inverse images, exactly as on the etale site.
Source: Stacks Project, Tags 09AE and 03EH; blueprint proof, step 7
(blueprint: lem-cbc-proetale-extension-zero-comparison). -/
noncomputable def proEtaleOpenExtensionComp (Λ : Type (u + 1)) [CommRing Λ]
    {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (k ≫ j) ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j :=
  (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (k ≫ j)).leftAdjointUniq
    (((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k).comp
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)).ofNatIsoRight
        (upperStarComp (ModuleCat.{u + 1} Λ) k j).symm)

/-- The canonical comparison `ν_X^* j_! F ⟶ j_! ν_U^* F` is invertible and commutes
with composition and identity open immersions. Naturality in `F` is built into the
existing natural isomorphism `openImmersionLowerShriekComparisonUpperStarIso`.
Source: Stacks Project, Tag 09AF; Weil conjectures blueprint, order 1584
(blueprint: lem-cbc-proetale-extension-zero-comparison).

Proof plan (the node's eight steps):
1. The etale restriction formula and extension adjunction identify the right adjoint
   of `ν_X^* j_!` (lem-weil-pbc-etale-composition-cancellation,
   lem-weil-pbc-etale-inverse-image-restriction,
   lem-weil-pbc-extension-by-zero-adjunction). The identities respect scalar actions.
2. Pro-etale localization and extension adjunction give the other right adjoint
   (lem-weil-proetale-weakly-etale-localization,
   lem-weil-extension-by-zero-adjunction). No stalk conservativity is used.
3. Both right adjoints evaluate at `W → U` as `M(W → U → X)` with the same
   restriction and scalar maps (def-weil-pbc-site-comparison-morphism).
4. Compose the comparison and extension adjunction Hom bijections; insert this
   identity-on-sections right-adjoint comparison to obtain the natural bijection Ψ.
5. Evaluating Ψ and its inverse on identities gives mutually inverse maps β and α.
   The existing comparison is exactly α, the inverse mate of that section identity.
6. Naturality of the Hom bijections in their source gives naturality in `F`.
7. The two extension composition maps are the mates of composition of restrictions
   (lem-cbc-extension-zero-composition, def-pur-localized-ringed-site and the
   two extension adjunctions). Their transposes are the same section identities.
8. Pasting the two Ψ bijections cancels the intermediate comparison adjunction;
   transitivity of section identities gives Ψ for `k ≫ j`. Evaluate at identity
   and invert to obtain the displayed composition equation. For the identity
   immersion Ψ is the identity under the two unit identifications, giving the
   last equation. These arguments include the empty scheme and zero ring. -/
theorem openImmersionLowerShriekComparison_coherence
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso ((openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) j).hom.app F)) ∧
    (∀ {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
      [IsOpenImmersion k] [IsOpenImmersion j]
      (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).map
          ((Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) k j).hom.app F) ≫
        (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).obj F) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).map
          ((openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) k).hom.app F) ≫
        (proEtaleOpenExtensionComp Λ k j).inv.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).obj F) =
      (openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) (k ≫ j)).hom.app F) ∧
    (∀ (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) (𝟙 X)).hom.app F ≫
        (Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
          (upperStarId (ModuleCat.{u + 1} Λ) X)).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F) =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).map
        ((Adjunction.leftAdjointIdIso
          (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
          (Etale.upperStarId (ModuleCat.{u + 1} Λ) X)).hom.app F)) := by
  sorry

end AlgebraicGeometry.ProEtale
