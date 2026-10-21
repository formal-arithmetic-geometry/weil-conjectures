/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence

/-!
# Abelian comparison pullback on an etale slice

Source: Stacks Project, Sites, Tags 00Y0 and 03CE; Pro-etale Cohomology, Tag 09A5
(blueprint: lem-pe-comparison-etale-slice-abelian-pullback).

The restriction functors below are the existing sectionwise localization restrictions:
at `T → W` they evaluate the original sheaf at `T → W → X`, with its original maps.
The site equivalences retain these same schemes and arrows. Abelian groups and both
sites are placed in the common larger universe `u + 1`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Source: Stacks Project, Sites, Tags 00Y0 and 03CE; Pro-etale Cohomology, Tag 09A5
(blueprint: lem-pe-comparison-etale-slice-abelian-pullback).

Proof:
1. Compose etale objects over `W` with `W → X`. Etale composition and cancellation
   (`lem-weil-pbc-etale-composition-cancellation`) give an equivalence with `Over W`.
   It preserves and reflects covering families, since both are jointly surjective
   etale families. Restriction is precomposition with this composition functor, as
   in `def-pur-localized-ringed-site` and `def-weil-pbc-etale-site`.
2. The inclusion `Scheme.toProEt X` regards `W` as a weakly etale object.
   `lem-weil-proetale-weakly-etale-localization` identifies its pro-etale slice with
   the pro-etale site of `W`, retaining schemes, arrows and coverings.
3. `lem-weil-pbc-etale-inverse-image-restriction` identifies etale inverse image with
   sectionwise restriction, naturally in the abelian sheaf. The abelian clause of
   `lem-sfb-proetale-object-inverse-image-restriction` gives the pro-etale version.
   The etale isomorphism is `Etale.upperStarIsoLocalizationRestriction`; the pro-etale
   isomorphism is `C.sheafIso`, normalized by the distinguished Kan coprojections
   and sheafification unit in `Scheme.ProEtaleObjectRestrictionComparison`.
   Neither identification requires a monomorphism or finite coefficients.
4. Apply `lem-weil-pbc-comparison-pullback` to `W → X`. On `F`, compose the inverse
   pro-etale restriction identification, the inverse canonical comparison square,
   and the comparison pullback of the etale restriction identification. These are
   the three factors in the displayed component equation. Their domains agree;
   composing their naturality equations proves naturality in `F`. -/
theorem comparison_etaleSlice_abelian_pullback (X : Scheme.{u}) (W : X.Etale) :
    (∃ e : Over W ≌ W.left.Etale,
      e.inverse ⋙ Over.forget W = MorphismProperty.Over.map ⊤ W.prop ∧
      (∀ T : W.left.Etale, HEq (e.inverse.obj T).hom.left T.hom) ∧
      e.inverse.IsDenseSubsite W.left.smallEtaleTopology (X.smallEtaleTopology.over W)) ∧
    (Scheme.ProEt.sliceEquiv X ((Scheme.toProEt X).obj W)).inverse.IsDenseSubsite
      (Scheme.ProEt.topology W.left)
      ((Scheme.ProEt.topology X).over ((Scheme.toProEt X).obj W)) ∧
    ∃ (C : Scheme.ProEtaleObjectRestrictionComparison
        ((Scheme.toProEt X).obj W) AddCommGrpCat.{u + 1})
      (tau : comparisonUpperStar AddCommGrpCat.{u + 1} X ⋙
          localizationRestriction AddCommGrpCat.{u + 1} W.hom
            (inferInstance : WeaklyEtale W.hom) ≅
        Etale.localizationRestriction AddCommGrpCat.{u + 1} W.hom W.prop ⋙
          comparisonUpperStar AddCommGrpCat.{u + 1} W.left),
      ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
        tau.app F =
          (C.sheafIso.app ((comparisonUpperStar AddCommGrpCat.{u + 1} X).obj F)).symm ≪≫
          ((supportSiteComparisonCoefficientPullbackIso
            AddCommGrpCat.{u + 1} W.hom).app F).symm ≪≫
          (comparisonUpperStar AddCommGrpCat.{u + 1} W.left).mapIso
            ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
              W.hom W.prop).app F) := by
  classical
  refine ⟨⟨Scheme.Etale.overEquiv W, rfl, fun _ ↦ HEq.rfl, inferInstance⟩,
    Scheme.ProEt.sliceDense X ((Scheme.toProEt X).obj W), ?_⟩
  obtain ⟨C⟩ := (Scheme.proEtaleObjectInverseImageRestriction X
    ((Scheme.toProEt X).obj W) (ULift.{u} ℤ)).2.2.1
  refine ⟨C,
    Functor.isoWhiskerLeft (comparisonUpperStar AddCommGrpCat.{u + 1} X)
        C.sheafIso.symm ≪≫
      (supportSiteComparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} W.hom).symm ≪≫
      Functor.isoWhiskerRight
        (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} W.hom W.prop)
        (comparisonUpperStar AddCommGrpCat.{u + 1} W.left), ?_⟩
  intro F
  rfl

end AlgebraicGeometry.ProEtale
