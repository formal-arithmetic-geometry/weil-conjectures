/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDualityMaps

import Sheaf.CategoryTheory.RingedSitePerfectOrdinaryDual
import Sheaf.CategoryTheory.RingedSiteOrdinaryPerfectEvaluation
import Sheaf.CategoryTheory.RingedSitePerfectTermHomExact
import Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIsoOfUniverses
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-! # Evaluation for a bounded finite-projective complex

Source: Stacks Project, Tag 08JJ (blueprint: lem-sfb-strict-perfect-evaluation).
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w u v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory

private theorem finite_unit_dualizable
    {M : Type*} [Category M] [Abelian M] [MonoidalCategory M]
    [MonoidalPreadditive M] [HasFiniteBiproducts M] (n : ℕ) :
    IsDualizable (∏ᶜ (fun _ : Fin n ↦ MonoidalCategoryStruct.tensorUnit M)) := by
  classical
  let : HasBinaryBiproducts M := HasBinaryBiproducts.of_hasBinaryProducts
  induction n with
  | zero =>
    apply IsZero.isDualizable
    apply (IsZero.iff_id_eq_zero _).2
    apply Pi.hom_ext
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    let e : (MonoidalCategoryStruct.tensorUnit M ⊞
        ∏ᶜ fun _ : Fin n ↦ MonoidalCategoryStruct.tensorUnit M) ≅
        (∏ᶜ fun _ : Fin (n + 1) ↦ MonoidalCategoryStruct.tensorUnit M) :=
      { hom := Pi.lift (Fin.cases biprod.fst (fun i ↦ biprod.snd ≫ Pi.π _ i))
        inv := biprod.lift (Pi.π _ 0) (Pi.lift (fun i ↦ Pi.π _ i.succ))
        hom_inv_id := by
          apply biprod.hom_ext
          · simp
          · apply Pi.hom_ext
            intro i
            simp
        inv_hom_id := by
          apply Pi.hom_ext
          intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp }
    exact (isDualizable_unit.biprod ih).of_iso e


/-- A bounded strict-perfect complex is K-flat on the ringed site.
Source: Stacks Project, Tag 08JJ. -/
private theorem strictPerfect_isKFlat
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ P) :
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P := by
  classical
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive.{c, v, max c v r} R
  let : IsGrothendieckAbelian.{max c v r}
      (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let : HasFiniteBiproducts
      (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    Abelian.hasFiniteBiproducts
  obtain ⟨a, b, hbound⟩ := hb
  have hdual (n : ℤ) : IsDualizable (P.X n) := by
    apply IsDualizable.of_retract ⟨pkg.i n, pkg.p n, pkg.splitting n⟩
    exact finite_unit_dualizable (pkg.N n)
  have hflat (n : ℤ) :
      SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (J := J) (R := R) (P.X n) := by
    obtain ⟨_⟩ := hdual n
    have := (tensorLeftAdjunction (P.X n) (P.X n)ᘁ).rightAdjoint_preservesLimits
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R (P.X n)
    have hl : exactFunctor _ _ (tensorLeft (P.X n)) :=
      (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩
    have hr := (exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (P.X n)) hl
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X n)).symm hr
  have : P.IsStrictlyLE b :=
    (P.isStrictlyLE_iff b).2 (fun n hn ↦ hbound n (Or.inr hn))
  exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R P b hflat



/-- Canonical evaluation for a bounded complex of finite-free retracts.
Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, final paragraph.
Proof: put D=Hom(E,O[0]). Its terms are duals of the terms of E in opposite degrees,
so the finite-free splittings dualize to finite-free splittings of D, with reflected
bounds. Thus D is K-flat. Choose a flat-term K-flat representative F of N. Exactness
of Hom(E^i,-), together with boundedness of E, identifies ordinary Hom(E,F) and
Hom(E,O[0]) with the corresponding derived Hom objects. The normalization equation
for the specified evaluation map identifies it with the localization of ordinary
unsigned evaluation Tot(F tensor D) to Hom(E,F). In degree n the finite interval
supporting E indexes both sides. The termwise evaluation map is an isomorphism for
a finite free module by its finite dual basis and remains an isomorphism for a
retract. Its inverse sends h to sum_j h(t_j) tensor lambda_j. The total evaluation
is consequently degreewise invertible, including empty intervals and rank zero.
It is already a chain map by its defining formula. The normalization equation and
naturality in N therefore make the specified derived evaluation invertible.
(blueprint: lem-sfb-strict-perfect-evaluation). -/
theorem ringedSiteStrictPerfectEvaluation
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (K : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n))
    (pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ K)
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (N : DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
    : IsIso (ringedSiteDualEvaluation M.closed
      (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso (DerivedCategory.Q.obj K) N) := by
  classical
  let A := SheafOfModules.{max c v r} ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let O := ringedSiteDualityUnitComplex.{c, v, r} J R
  let D := homComplex (R := R) K O
  obtain ⟨hbD, ⟨pkgD⟩⟩ := ringedSitePerfect_ordinaryDual.{c, v, r}
    R K hbounded pkg
  have hD : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
      (J := J) (R := R) D := strictPerfect_isKFlat.{c, v, r} J R D hbD pkgD
  have : IsGrothendieckAbelian.{max c v r} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  have hHom (F : CochainComplex A ℤ) : QuasiIso
      (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 K)
        ((ringedSiteHomAugmentation.{c, v, r} J R).app F)) := by
    have hη : QuasiIso ((ringedSiteHomAugmentation.{c, v, r} J R).app F) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} A F).2
    simp only [ringedSiteHomComplexMap, op_id, Functor.map_id, NatTrans.id_app]
    apply quasiIso_homComplex_map_of_bounded_exact_termsOfUniverses.{c, v, r}
      J R K hbounded
    intro n S hS
    exact ringedSitePerfect_termHomExact.{c, v, r} R (K.X n) (pkg.N n)
      (pkg.i n) (pkg.p n) (pkg.splitting n) S hS
  let F₀ := DerivedCategory.Q.objPreimage N
  obtain ⟨F, f, hF, _hflat, hf, _hepi⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{max c v r, c, v}
      (R := R) F₀
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hf
  let eN : DerivedCategory.Q.obj F ≅ N :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso N
  have hE := hHom O
  have hEF := hHom F
  have ho := ringedSiteOrdinaryEvaluation_isIso.{c, v, r} J R K hbounded pkg F
  let d := ringedSiteOrdinaryHomIso.{c, v, r, w} J R K O hE
  have ht : IsIso (M.closed.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj F)) d.hom)) :=
    (M.closed.tensor.mapIso (Iso.prod (Iso.refl _) d)).isIso_hom
  have hn := ringedSiteDualEvaluation_normalization.{c, v, r, w} J R M K F hF hD hE hEF
  have hm : IsIso ((M.models.iso J R M.closed F D hF hD).hom ≫
      M.closed.tensor.map (Prod.mkHom (𝟙 _) d.hom) ≫
      ringedSiteDualEvaluation M.closed (ringedSiteDualityUnit.{c, v, r, w} J R)
        M.unitIso (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj F)) := by
    rw [hn]
    infer_instance
  have : IsIso (M.closed.tensor.map (Prod.mkHom (𝟙 _) d.hom) ≫
      ringedSiteDualEvaluation M.closed (ringedSiteDualityUnit.{c, v, r, w} J R)
        M.unitIso (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj F)) :=
    IsIso.of_isIso_comp_left (M.models.iso J R M.closed F D hF hD).hom _
  have hcomponent : IsIso (ringedSiteDualEvaluation M.closed
      (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso
      (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj F)) :=
    IsIso.of_isIso_comp_left
      (M.closed.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj F)) d.hom)) _
  exact (NatTrans.isIso_app_iff_of_iso
    (ringedSiteDualEvaluationNatTrans M.closed
      (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso
      (DerivedCategory.Q.obj K)) eN).mp hcomponent


end CategoryTheory
