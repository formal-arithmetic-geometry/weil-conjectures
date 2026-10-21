/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import all Sheaf.CategoryTheory.RingedSitePerfectDuality

/-! # Perfect duality in a specified normalized presentation

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, lemma-dual-perfect-complex.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- The evaluation comparison of any specified normalized presentation is invertible
for a site-perfect source and every unbounded target.
Source: Stacks Project, Tag 08JJ, lemma-dual-perfect-complex
(blueprint: lem-fix-ringed-site-perfect-duality-for-model).

Proof: restrict the fixed presentation to each slice site using its normalized
restriction comparisons. A perfect source has a bounded finite-free-summand
representative on a covering family. On each such representative the canonical
ordinary tensor-dual evaluation is an isomorphism, and the K-flat tensor and
K-injective Hom comparisons identify it with the specified derived evaluation.
Exact slice restriction detects derived isomorphisms on a covering family.
Thus every component is invertible globally, and the specified natural
transformation is invertible. No global bound on the perfect source is needed.
-/
theorem ringedSitePerfectDualityForModel
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (P : DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
    (hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{c, v, r, w} R P)
    (M : RingedSiteDualityModel.{c, v, r, w} J R) :
    IsIso (ringedSiteDualEvaluationLeftNatTrans M.closed M.symmetric
      (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso P) := by
  classical
  let AU (U : C) := SheafOfModules.{max c v r} ((sheafCompose (J.over U)
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over U))
  obtain ⟨sliceDerived⟩ : Nonempty (∀ U : C, HasDerivedCategory.{max c v r + 1}
      (SheafOfModules.{max c v r} (((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U))) :=
    ⟨fun U ↦ HasDerivedCategory.standard _⟩
  let : ∀ U : C, HasDerivedCategory.{max c v r + 1}
      (SheafOfModules.{max c v r} (((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) := sliceDerived
  let (U : C) : HasDerivedCategory.{max c v r + 1} (AU U) := sliceDerived U
  obtain ⟨MU⟩ : Nonempty (∀ U : C,
      RingedSiteDualityModel.{max c v, v, r, max c v r + 1} (J.over U) (R.over U)) :=
    ⟨fun U ↦ (ringedSiteDualityMaps_exists.{max c v, v, r, max c v r + 1}
      (J.over U) (R.over U)).some⟩
  obtain ⟨d⟩ : Nonempty (∀ U : C,
      RestrictionData.{c, v, r, w, max c v r + 1} J R U M (MU U)) :=
    ⟨fun U ↦ (restrictionData_nonempty.{c, v, r, w, max c v r + 1}
      J R U M (MU U)).some⟩
  let F (U : C) := (d U).F
  have e (U : C) : DerivedCategory.Q ⋙ F U ≅
      (SheafOfModules.localizedSystemRestriction.{c, v, r} R U).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q :=
    (d U).e ≪≫ Functor.isoWhiskerRight
      (restrictionComplexIso.{c, v, r, w} J R U) DerivedCategory.Q
  have hmodels := (perfect_local_models.{c, v, r, w, max c v r + 1} J R F e P).mp hP
  let LP (U : C) : Prop := ∃ E : CochainComplex (AU U) ℤ,
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
    Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E) ∧
    Nonempty ((F U).obj P ≅ DerivedCategory.Q.obj E)
  let Y : { U : C // LP U } → C := Subtype.val
  have hY : J.CoversTop Y := by
    intro V
    obtain ⟨T, hT, hm⟩ := hmodels V
    apply J.superset_covering _ hT
    intro U f hf
    exact ⟨⟨U, hm U f hf⟩, ⟨𝟙 U⟩⟩
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro N
  have hi : IsIso (ringedSiteDualEvaluation M.closed
      (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso P N) := by
    apply derived_iso_local.{c, v, r, w, max c v r + 1} J R F e Y hY
    intro i
    let U := Y i
    obtain ⟨E, hE, ⟨pE⟩, ⟨p⟩⟩ := i.property
    have hlocal := evaluation_transport_source (MU U).closed
      (ringedSiteDualityUnit.{max c v, v, r, max c v r + 1} (J.over U) (R.over U))
        (MU U).unitIso p ((F U).obj N)
      (strict_evaluation.{max c v, v, r, max c v r + 1} (J.over U) (R.over U)
        (MU U) E hE pE ((F U).obj N))
    exact (d U).evaluation_isIso P N hlocal
  change IsIso (ringedSiteDualEvaluationLeft M.closed M.symmetric
    (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso P N)
  exact evaluation_left_isIso M.closed M.symmetric
    (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso P N hi

end CategoryTheory
