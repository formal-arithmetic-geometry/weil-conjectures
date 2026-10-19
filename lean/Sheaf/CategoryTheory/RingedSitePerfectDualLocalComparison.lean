/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedSitePerfectTermHomExact
import Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIsoOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-! # RingedSitePerfectDualLocalComparison

Source: Stacks Project, Tag 08JJ (blueprint: lem-sfb-perfect-dual-local-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace CategoryTheory

private theorem exists_quasiIso_of_iso_to_kInjective
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    (E I : CochainComplex A ℤ) [I.IsKInjective]
    (e : DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj I) :
    ∃ f : E ⟶ I, QuasiIso f := by
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let s := DerivedCategory.quotientCompQhIso A
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (q.obj E) I).surjective
    (s.hom.app E ≫ e.hom ≫ s.inv.app I)
  obtain ⟨f, hf⟩ := (q.map_surjective g)
  refine ⟨f, (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp ?_⟩
  have heq : DerivedCategory.Q.map f = e.hom := by
    rw [← hf] at hg
    have hh := congrArg (fun k ↦ s.inv.app E ≫ k ≫ s.hom.app I) hg
    change s.inv.app E ≫ DerivedCategory.Qh.map (q.map f) ≫ s.hom.app I = _ at hh
    rw [DerivedCategory.quotientCompQhIso_hom_naturality f] at hh
    dsimp only [s] at hh
    simpa only [Category.assoc,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id] using hh
  rw [heq]
  infer_instance

private theorem restrict_isKInjective
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r}) (U : C)
    (I : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((SheafOfModules.localizedSystemRestriction.{c, v, r} R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  have adj := SheafOfModules.localizedSystemAdjunction.{c, v, r} R U
  have : (SheafOfModules.localizedSystemExtension.{c, v, r} R U).IsLeftAdjoint :=
    adj.isLeftAdjoint
  have : (SheafOfModules.localizedSystemRestriction.{c, v, r} R U).PreservesKInjectiveComplexes :=
    adj.preservesKInjectiveComplexes
  exact Functor.PreservesKInjectiveComplexes.isKInjective_map I



set_option maxHeartbeats 800000 in
-- The composite derived comparison elaborates several independent universe interfaces.
/-- A specified ordinary local dual maps quasi-isomorphically to the restricted
fixed global dual representative. This asserts only the comparison map, not the
boundedness or finite-free splittings of its source.
Source: Stacks Project, Tags 08JJ (first two paragraphs), 08JB, 08FI and 070I.
Proof: take a K-injective resolution of the coefficient unit on the slice.
The degreewise finite-free splitting makes Hom(E^i,-) exact; the bounded Hom
lemma therefore identifies Hom(E,O[0]) with RHom(QE,O). Exact slice restriction
and its Hom comparison identify the latter with the restriction of RHom(QK,O),
using Qα and the comparison of the restricted unit. The fixed outer global
replacement represents this same derived object. Restriction preserves its
K-injectivity by the exact extension-by-zero adjunction. The K-injective Hom
comparison lifts the resulting derived isomorphism to an actual chain map β.
Localization sends β to that isomorphism, hence β is a quasi-isomorphism.
No global bound on K is used. Empty slices, rank zero and zero coefficients
use the same argument and the unique maps between zero derived objects.
(blueprint: lem-sfb-perfect-dual-local-comparison). -/
theorem ringedSitePerfectDual_localComparison
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (K : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (U : C)
    (E : CochainComplex (SheafOfModules.{max c v r} (((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E)
    (α : E ⟶ ((SheafOfModules.overFunctor _ U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) (hα : QuasiIso α) :
    ∃ β : homComplex (R := R.over U) E
        (ringedSiteDualityUnitComplex.{max c v, v, r} (J.over U) (R.over U)) ⟶
      ((SheafOfModules.overFunctor _ U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj
          (homComplex (R := R) K
            ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj
              (ringedSiteDualityUnitComplex.{c, v, r} J R)))), QuasiIso β := by
  classical
  let A := SheafOfModules.{max c v r} ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let AU := SheafOfModules.{max c v r} (((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)
  let : HasDerivedCategory AU := HasDerivedCategory.standard AU
  let : HasDerivedCategory (SheafOfModules.{max c v r} ((sheafCompose (J.over U)
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over U))) :=
    HasDerivedCategory.standard _
  let G := (SheafOfModules.overFunctor
    ((sheafCompose J (forget₂ CommRingCat.{max c v r}
      RingCat.{max c v r})).obj R) U).mapHomologicalComplex (ComplexShape.up ℤ)
  let O := ringedSiteDualityUnitComplex.{c, v, r} J R
  let OU := ringedSiteDualityUnitComplex.{max c v, v, r} (J.over U) (R.over U)
  let I := WeilConjectures.coefficientHomResolution.{r, c, v} J R
  let L := homComplex (R := R) K (I.obj O)
  let D := homComplex (R := R.over U) E OU
  have hGroth : IsGrothendieckAbelian.{max c v r} A :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
       J R).1
  have hGrothU : IsGrothendieckAbelian.{max c v r} AU :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{max c v, v, r}
       (J.over U) (R.over U)).1
  have : (I.obj L).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} A L
  have : CochainComplex.IsKInjective (G.obj (I.obj L)) :=
    restrict_isKInjective.{c, v, r} J R U (I.obj L)
  have hη : QuasiIso ((ringedSiteHomAugmentation.{c, v, r} J R).app L) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} A L).2
  have : IsIso (DerivedCategory.Q.map
      ((ringedSiteHomAugmentation.{c, v, r} J R).app L)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hη
  have hηU : QuasiIso
      ((ringedSiteHomAugmentation.{max c v, v, r} (J.over U) (R.over U)).app OU) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} AU OU).2
  have hHom : QuasiIso (ringedSiteHomComplexMap.{max c v, v, r}
      (J.over U) (R.over U) (𝟙 E)
        ((ringedSiteHomAugmentation.{max c v, v, r} (J.over U) (R.over U)).app OU)) := by
    simp only [ringedSiteHomComplexMap, op_id, Functor.map_id, NatTrans.id_app]
    apply quasiIso_homComplex_map_of_bounded_exact_termsOfUniverses.{max c v, v, r}
       (J.over U) (R.over U) E hbounded
    intro n S hS
    exact ringedSitePerfect_termHomExact.{max c v, v, r}
      (R.over U) (E.X n) (pkg.N n) (pkg.i n) (pkg.p n) (pkg.splitting n) S hS
  obtain ⟨M⟩ := ringedSiteDualityMaps_exists.{c, v, r, w} J R
  obtain ⟨MU⟩ := ringedSiteDualityMaps_exists.{max c v, v, r} (J.over U) (R.over U)
  obtain ⟨F, ⟨eF⟩, t, h, o, _heval, _hbidual, _hdual⟩ :=
    ringedSiteDualityMaps_restriction.{c, v, r, w} J R M U MU
  have : IsIso (DerivedCategory.Q.map α) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hα
  let eK : DerivedCategory.Q.obj E ≅ F.obj (DerivedCategory.Q.obj K) :=
    asIso (DerivedCategory.Q.map α) ≪≫ (eF.app K).symm
  let eU : DerivedCategory.Q.obj OU ≅
      F.obj (ringedSiteDualityUnit.{c, v, r, w} J R) := o.symm
  let HU := derivedInternalHomOfUniverses.{max c v, v, r} (J.over U) (R.over U)
  let e : DerivedCategory.Q.obj D ≅ DerivedCategory.Q.obj (G.obj (I.obj L)) :=
    ringedSiteOrdinaryHomIso.{max c v, v, r} (J.over U) (R.over U) E OU hHom ≪≫
      HU.mapIso (Iso.prod eK.symm.op eU) ≪≫
      h.symm.app (op (DerivedCategory.Q.obj K), ringedSiteDualityUnit.{c, v, r, w} J R) ≪≫
      F.mapIso (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R K O) ≪≫
      F.mapIso (asIso (DerivedCategory.Q.map
        ((ringedSiteHomAugmentation.{c, v, r} J R).app L))) ≪≫ eF.app (I.obj L)
  exact exists_quasiIso_of_iso_to_kInjective D (G.obj (I.obj L)) e


end CategoryTheory
