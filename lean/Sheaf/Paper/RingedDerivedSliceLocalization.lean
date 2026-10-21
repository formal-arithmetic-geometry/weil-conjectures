/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.Paper.RingedDerivedSliceData
import Sheaf.Paper.RingedSliceLocalizationModel
import Sheaf.Paper.RingedSliceDerivedComparisons
import Sheaf.Paper.RingedSliceDerivedAdjunction
import all Sheaf.Paper.RingedLocalizationModels

/-!
# Derived slice comparisons and pullback of section localization

Source: Stacks Project, algebraization.tex, Tag 099J; Modules on Sites, Tag 04J0;
Cohomology on Sites, Tag 07A6
(blueprint: lem-weil-pbc-ringed-derived-slice-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 256

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J]
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
  (a : R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S)
  [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))]
  [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Instantiating the ordinary slice theorem elaborates its full dependent comparison package.
set_option backward.isDefEq.respectTransparency.types false in
-- The normalization includes both universal transformations and the adjunction equations.
/-- Canonical derived slice comparisons, their adjunction coherence, and the normalized
pullback of every section localization, for unbounded complexes and arbitrary ring maps.
Source: Stacks Tags 099J, 04J0 and 07A6
(blueprint: lem-weil-pbc-ringed-derived-slice-localization).

Proof:
1. Localize the ringed-site morphism by lem-weil-pbc-localize-ringed-site-morphism.
The two module restrictions are exact (lem-pur-site-restriction-module-adjunction-exact),
so they descend termwise to the unbounded derived categories.
2. Choose a flat-term K-flat resolution by lem-pc-kflat-resolution. Restriction is
pullback along a localization morphism of topoi (lem-weil-pbc-slice-site-localization),
hence remains flat K-flat by lem-weil-pbc-ringed-topos-kflat-pullback and the tensor unit.
The ordinary pullback square computes the two derived pullbacks on this resolution.
3. Descend its naturality through the localization of flat K-flat representatives
(lem-weil-pbc-site-derived-tensor-descent and the localization universal property).
4. Choose a K-injective resolution (prop-pur-kinjective-resolutions-exist); its
restriction is K-injective (lem-pur-kinjective-restrict-localized). The ordinary
identity on sections computes the two derived direct images and the displayed
right-derived normalization. Maps into K-injectives are homotopy classes, proving
naturality and independence (lem-weil-pbc-kinjective-hom-derived).
5. Ordinary inverse adjuncts commute with the square: on r tensor x both paths give
r times h(x). This respects restriction, tensor relations and sheafification.
6. Represent an arbitrary derived arrow by a fraction with flat K-flat denominator
and K-injective target. Apply lem-pc-pre-derived-adjoint-functors-general: on the
injective side the unique maps to the chosen resolution give an essentially constant
ind-diagram; on the flat side the invertible comparison at a flat K-flat stage,
cofilteredness and another flat resolution give an essentially constant pro-diagram.
7. Restrict that fraction; the same computation gives equality of inverse adjuncts
using the ordinary identity in step 5. Both sides are independent of the fraction.
8. Specialize to the identity and to the unit. The triangle identities give exactly
the counit and unit equations stated below (lem-weil-pbc-ringed-projection-mate-exact).
9. R[1/t] is the sheafification of colim(R --t--> R --t--> ...). The n-th stage
sends x to x/t^n; equality of fractions is equality at a later stage, also for zero
divisors (lem-weil-pbc-module-sheaves-colimits-forgetful).
10. Pullback preserves this colimit as a left adjoint; it takes R to S and t to its
structural image. The colimit identification therefore takes the localization unit
to the localization unit. This is the generator equation below.
11. Localization is flat sectionwise (lem-weil-pbc-localization-flat); exact module
sheafification and its tensor comparison imply flatness as a module sheaf. Its
single complex is K-flat (lem-pc-bounded-above-flat-kflat-site), so the ordinary
calculation computes the derived pullback. A section on V need not extend globally. -/
theorem ringedDerivedSliceLocalization
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)] (V : D)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (u.obj V)))] :
    ∃ _hc : (Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V)),
      ∃ (e : RingedSliceDerivedImage.{u, w} u a)
        (l : RingedSliceDerivedImage.{u, w} (Over.post (X := V) u)
          (localizedRingedSiteMap u a V)),
        ∃ d : RingedSliceAdjunctionSquare e.adjunction l.adjunction
            (ringedSliceRestriction.{u, w} R V)
            (ringedSliceRestriction.{u, w} S (u.obj V)),
          (∀ (I : CochainComplex (SheafOfModules.{u}
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ),
            (ringedSliceRestriction.{u, w} R V).map
                (X := DerivedCategory.Q.{w}.obj
                  (((ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ)).obj I))
                (Y := e.right.obj (DerivedCategory.Q.{w}.obj I)) (e.eta.app I) ≫
              d.beta.hom.app (DerivedCategory.Q.{w}.obj I) ≫
              l.right.map
                (X := (ringedSliceRestriction.{u, w} S (u.obj V)).obj (DerivedCategory.Q.{w}.obj I))
                (Y := DerivedCategory.Q.{w}.obj
                  ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj I))
                ((ringedSliceRestrictionFactors.{u, w} S (u.obj V)).hom.app I) =
            (ringedSliceRestrictionFactors.{u, w} R V).hom.app
              (((ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ)).obj I) ≫
              DerivedCategory.Q.{w}.map (ringedSlicePushforwardComplexIso u a V I).hom ≫
              l.eta.app
                ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj I)) ∧
          ∀ t : R.obj.obj (op V),
            ∃ loc : l.left.obj
                ((CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q.{w}).obj
                  (ringedSectionLocalization (R.over V) (ringedSliceSection R V t))) ≅
                (CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q.{w}).obj
                  (ringedSectionLocalization (S.over (u.obj V))
                    (ringedSliceSection S (u.obj V) (a.hom.app (op V) t))),
              l.left.map
                (X := (CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q.{w}).obj
                  (unit ((sheafCompose (K.over V) (forget₂ CommRingCat RingCat)).obj
                    (R.over V))))
                (Y := (CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q.{w}).obj
                  (ringedSectionLocalization (R.over V) (ringedSliceSection R V t)))
                ((CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q.{w}).map
                  (ringedSectionLocalizationUnit (R.over V) (ringedSliceSection R V t))) ≫
                  loc.hom =
                l.epsilon.app ((CochainComplex.singleFunctor _ 0).obj
                    (unit ((sheafCompose (K.over V) (forget₂ CommRingCat RingCat)).obj
                      (R.over V)))) ≫
                  DerivedCategory.Q.{w}.map
                    (ringedSliceLocalizationGenerator (Over.post (X := V) u)
                      (localizedRingedSiteMap u a V)
                      (ringedSliceSection S (u.obj V) (a.hom.app (op V) t))) := by
  obtain ⟨hc, hl, _⟩ := localize_ringed_site_morphism_general (K := K) (J := J) u a V
  obtain ⟨e, _⟩ := ringedSliceDerivedImage_exists.{u, w} u a
  obtain ⟨l, hlcomp⟩ := ringedSliceDerivedImage_exists.{u, w}
    (Over.post (X := V) u) (localizedRingedSiteMap u a V)
  obtain ⟨beta, hmate, hbeta⟩ := ringedSliceDerivedComparisons u a V e l
  let d := RingedSliceAdjunctionSquare.ofMate e.adjunction l.adjunction
    (ringedSliceRestriction.{u, w} R V) (ringedSliceRestriction.{u, w} S (u.obj V)) beta
  refine ⟨hc, e, l, d, hbeta, ?_⟩
  intro t
  obtain ⟨loc, hloc⟩ := ringedSliceLocalizationModel u a V t
  have heps : IsIso (l.epsilon.app ((CochainComplex.singleFunctor _ 0).obj
      (ringedSectionLocalization (R.over V) (ringedSliceSection R V t)))) :=
    hlcomp _ (localizationSliceCoefficient_kflat R V t) (by
    let := monoidalCategory (R.over V)
    intro n
    by_cases hn : n = 0
    · subst n
      exact (exactFunctor _ _).prop_of_iso
        ((MonoidalCategory.curriedTensor _).flip.mapIso
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (localizationSliceCoefficient R V t)).symm)
        (CategoryTheory.localization_isFlat (R.over V) (ringedSliceSection R V t))
    · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (localizationSliceCoefficient R V t) n hn
      let := Classical.choice (SheafOfModules.tensorClosed (R.over V)).1
      exact (ObjectProperty.flat_of_isZero hz).tensorRight)
  refine ⟨asIso (l.epsilon.app _) ≪≫ DerivedCategory.Q.{w}.mapIso loc, ?_⟩
  change l.left.map _ ≫ (l.epsilon.app _ ≫ DerivedCategory.Q.{w}.map loc.hom) = _
  erw [← Category.assoc, l.epsilon.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← DerivedCategory.Q.map_comp, hloc]

end SheafOfModules
