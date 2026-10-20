/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic

/-!
# Global cohomology under the etale to pro-etale comparison

Source: blueprint, `sec-proper-base-change/sk-thm-properbasechange/`
`lem-weil-pbc-comparison-global-cohomology.md`, statement and both proof paragraphs
(blueprint: lem-weil-pbc-comparison-global-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The canonical map on ordinary derived global sections, induced by the bounded-below
comparison unit followed by the Leray isomorphism coming from evaluation at the terminal
objects. The compatibility of bounded-below and unbounded right derived functors transports
that unit into the unbounded derived category. This uses left modules over any finite ring;
no monoidal structure on the coefficient category is required.
Source: blueprint, comparison-global-cohomology, final proof sentence
(blueprint: lem-weil-pbc-comparison-global-cohomology). -/
noncomputable def comparisonGlobalSections (T : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ] :
    DerivedCategory.Plus.ι ⋙ Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus ⋙
        DerivedCategory.Plus.ι ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T :=
  let L := (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus
  let R := comparisonLowerStar (ModuleCat.{u + 1} Λ) T
  let Γ := Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T
  (Functor.leftUnitor (DerivedCategory.Plus.ι ⋙ Γ)).inv ≫
    Functor.whiskerRight (T.proEtaleSiteComparisonModules Λ).derivedPlus.unit
      (DerivedCategory.Plus.ι ⋙ Γ) ≫
    (Functor.associator L R.rightDerivedFunctorPlus (DerivedCategory.Plus.ι ⋙ Γ)).hom ≫
    Functor.whiskerLeft L
      ((Functor.associator R.rightDerivedFunctorPlus DerivedCategory.Plus.ι Γ).inv ≫
        Functor.whiskerRight R.rightDerivedFunctorPlusCompatibility.hom Γ ≫
        (Functor.associator DerivedCategory.Plus.ι R.rightDerivedFunctor Γ).hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι
          (comparisonLowerStarCompRightDerivedGlobalSectionsIso
            (ModuleCat.{u + 1} Λ) T).hom)

/-- The derived comparison unit induces a natural isomorphism of ordinary global sections.
Source: blueprint, comparison-global-cohomology, statement and proof
(blueprint: lem-weil-pbc-comparison-global-cohomology).

Proof: (1) Exactness of the comparison inverse image, supplied by
`prop-weil-pbc-site-comparison-finite-level`, implies that its right adjoint preserves
injectives. On a bounded-below pro-etale injective resolution, pushforward thus computes
its right derived functor and subsequent derived sections. Evaluation at the final object
identifies the two section complexes termwise. This is the canonical Leray comparison of
`lem-weil-pbc-derived-sections-pushforward`, represented here by
`comparisonLowerStarCompRightDerivedGlobalSectionsIso`.
(2) Apply this comparison to the inverse image of the given bounded-below etale complex.
The derived unit is invertible by `thm-weil-pbc-site-comparison`; applying ordinary etale
derived sections and composing with the Leray isomorphism proves the assertion. All
comparison maps are natural, so their composite is a natural isomorphism. -/
theorem isIso_comparisonGlobalSections (T : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ] :
    IsIso (comparisonGlobalSections T Λ) := by
  let adj := T.proEtaleSiteComparisonModules Λ
  obtain ⟨_, _, hunit, hacyclic⟩ := siteComparison_finiteLevel T Λ
  have : IsIso adj.derivedPlus.unit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact adj.isIso_derivedPlus_unit_app_of_rightAcyclic
      (fun I _ ↦ hunit I)
      (fun I _ n ↦ hacyclic I inferInstance (n + 1) (Nat.succ_pos n)) K
  unfold comparisonGlobalSections
  infer_instance

end AlgebraicGeometry.ProEtale
