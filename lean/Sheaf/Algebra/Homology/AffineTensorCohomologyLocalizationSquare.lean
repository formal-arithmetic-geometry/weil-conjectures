/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

import Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology
import Sheaf.Algebra.Homology.AffineTensorLocalizationFlat

import Sheaf.Algebra.Homology.PrescribedTensorCohomologyModelRealization
import Sheaf.Algebra.Homology.KFlatModuleBaseChange
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # Global-to-local tensor cohomology component isomorphisms

Source: Stacks Project, Tags 0DJ8, 00DL and 00CS.
(blueprint: lem-pc-affine-tensor-cohomology-localization-square). -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

private theorem kFlat_extend
    (A Aq : Type u) [CommRing A] [CommRing Aq] [Algebra A Aq]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} Aq) (.up ℤ)).kFlat
      ((extend A Aq).obj P) := by
  have hacyclic (L : CochainComplex (ModuleCat.{u} A) ℤ) (hL : L.Acyclic) :
      (CochainComplex.mapBifunctor L P (curriedTensor _)).Acyclic := by
    have hk := (HomotopyCategory.kFlat_quotient_obj_iff P).2 hP
    have h := (HomotopyCategory.kFlat_iff_preserves_acyclic _).1 hk
      ((HomotopyCategory.quotient _ _).obj L)
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic L).2 hL)
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 h.2
  have hbase := CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat
    (algebraMap A Aq) P hacyclic
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2
    (hbase N hN)
  refine ⟨?_, hr⟩
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr

private noncomputable def coefficientExtensionIso
    (A Aq D : Type u) [CommRing A] [CommRing Aq] [CommRing D]
    (rho : A →+* Aq) (f0 : A →+* D) (f1 : Aq →+* D) (h : f1.comp rho = f0) :
    (ModuleCat.extendScalars f0).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars rho).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.extendScalars f1).mapHomologicalComplex (.up ℤ) :=
  (Functor.mapHomologicalComplexCompIso
    ((ModuleCat.extendScalarsComp rho f1).symm ≪≫
      eqToIso (congrArg (fun f : A →+* D ↦ ModuleCat.extendScalars.{u} f) h)) (.up ℤ)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientExtensionIso_tmul
    (A Aq D : Type u) [CommRing A] [CommRing Aq] [CommRing D]
    (rho : A →+* Aq) (f0 : A →+* D) (f1 : Aq →+* D) (h : f1.comp rho = f0)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ) (d : D) (x : P.X j) :
    ((coefficientExtensionIso A Aq D rho f0 f1 h).hom.app P).f j (d ⊗ₜ[A,f0] x) =
      d ⊗ₜ[Aq,f1] ((1 : Aq) ⊗ₜ[A,rho] x) := by
  subst f0
  change (ModuleCat.extendScalarsComp rho f1).hom.app (P.X j)
    (d ⊗ₜ[A,f1.comp rho] x) = _
  have hx : d ⊗ₜ[A,f1.comp rho] x = d • ((1 : D) ⊗ₜ[A,f1.comp rho] x) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [hx, map_smul, ModuleCat.extendScalarsComp_hom_app_one_tmul]
  erw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- The global-to-local cohomology square for prescribed tensor-algebra lifts.
Source: Stacks Project, perfect.tex, Tag 0DJ8, affine displayed localization identity.
(blueprint: lem-pc-affine-tensor-cohomology-localization-square)

Proof: choose balanced derived cohomology models L on the functorial A-K-flat
resolution P and K on its localization J(P). Extension of scalars preserves K-flatness,
and exact localization preserves the resolution augmentation's quasi-isomorphism.
Use prescribedTensorCohomology_model_realization with U=id,Q=P globally and
U=J,Q=P followed by J locally. This supplies sigma and sigmal identifying the source
lifts with model cohomology, and gamma and gammal identifying the extended target
lifts with ordinary D-cohomology of the respective resolutions. Their comparison
equations identify the prescribed comparisons with the models' localized comparisons.
The coefficient maps are flat, globally by localization and locally by
affineTensorLocalization_flat. Apply derivedTensor_localization_cohomology to L,K.
Tensor associativity gives tau:D tensor_A P isomorphic to D tensor_Aq J(P);
the scalar towers identify the two A-to-D maps. Its pure-tensor equation follows
from extendScalarsComp_hom_app_one_tmul and D-linearity. Define alpha by composing
extension of sigma, the derived localization isomorphism, and inverse extension
of sigmal. Define beta by composing gamma, cohomology of tau, and inverse gammal.
The model-map equations from realization let us apply derived localization
naturality to the conjugates of S.map and Sl.map, giving alpha naturality after
cancellation. Gamma naturality, tau naturality and gammal naturality give beta
naturality. Finally cancel gammal on the right of the comparison square and apply
the global realization equation, the derived localization comparison equation,
and the local realization equation. No local target cohomology identification
beyond the common localized resolution is assumed.
Zero complexes and identity localizations use the same maps; if no prime exists,
there is no instance of the assertion to check. -/
theorem affineTensorCohomology_localization_square
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ)
    (S T : CochainComplex (ModuleCat.{u} A) ℤ ⥤ ModuleCat.{u} (A ⊗[R] B))
      (eS : S ⋙ ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
        source R A B i)
      (eT : T ⋙ ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
        target R A B i)
      (c : S ⟶ T)
    (hS : (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) (x : S.obj M),
        eS.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
          (source R A B i).map (a • 𝟙 M) (eS.hom.app M x)))
    (hT : (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) (x : T.obj M),
        eT.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
          (target R A B i).map (a • 𝟙 M) (eT.hom.app M x)))
    (hc : Functor.whiskerRight c
          (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom) ≫ eT.hom =
        eS.hom ≫ comparison R A B i)
    (q' : PrimeSpectrum (A ⊗[R] B))
        (Rp Aq Bp D : Type u) [CommRing Rp] [CommRing Aq] [CommRing Bp] [CommRing D]
        [Algebra R Rp] [Algebra A Aq] [Algebra B Bp] [Algebra (A ⊗[R] B) D]
        [IsLocalization.AtPrime Rp (q'.asIdeal.comap (algebraMap R (A ⊗[R] B)))]
        [IsLocalization.AtPrime Aq (q'.asIdeal.comap (algebraMap A (A ⊗[R] B)))]
        [IsLocalization.AtPrime Bp (q'.asIdeal.comap
          Algebra.TensorProduct.includeRight.toRingHom)]
        [IsLocalization.AtPrime D q'.asIdeal]
        [Algebra R Aq] [Algebra R Bp] [Algebra Rp Aq] [Algebra Rp Bp]
        [IsScalarTower R A Aq] [IsScalarTower R B Bp]
        [IsScalarTower R Rp Aq] [IsScalarTower R Rp Bp]
        [Algebra A D] [Algebra B D] [Algebra Aq D] [Algebra Bp D]
        [IsScalarTower A (A ⊗[R] B) D]
        [IsScalarTower A Aq D]
        (_hB : ∀ b : B, algebraMap B D b =
          algebraMap (A ⊗[R] B) D (Algebra.TensorProduct.includeRight b))
        [IsScalarTower B Bp D]
        (f : (Aq ⊗[Rp] Bp) →+* D)
        (_hfA : ∀ a : Aq,
          f (Algebra.TensorProduct.includeLeft (S := Rp) a : Aq ⊗[Rp] Bp) = algebraMap Aq D a)
        (_hfB : ∀ b : Bp, f (Algebra.TensorProduct.includeRight b) = algebraMap Bp D b)
    (Sl Tl : CochainComplex (ModuleCat.{u} Aq) ℤ ⥤
            ModuleCat.{u} (Aq ⊗[Rp] Bp))
          (eSl : Sl ⋙
            ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
            source Rp Aq Bp i)
          (eTl : Tl ⋙
            ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
            target Rp Aq Bp i)
          (cl : Sl ⟶ Tl)
    (hSl : (∀ (M : CochainComplex (ModuleCat.{u} Aq) ℤ) (a : Aq) (x : Sl.obj M),
            eSl.hom.app M ((Algebra.TensorProduct.includeLeft (S := Rp) a : Aq ⊗[Rp] Bp) • x) =
              (source Rp Aq Bp i).map (a • 𝟙 M) (eSl.hom.app M x)))
    (hTl : (∀ (M : CochainComplex (ModuleCat.{u} Aq) ℤ) (a : Aq) (x : Tl.obj M),
            eTl.hom.app M ((Algebra.TensorProduct.includeLeft (S := Rp) a : Aq ⊗[Rp] Bp) • x) =
              (target Rp Aq Bp i).map (a • 𝟙 M) (eTl.hom.app M x)))
    (hcl : Functor.whiskerRight cl
              (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom) ≫
              eTl.hom = eSl.hom ≫ comparison Rp Aq Bp i)
    :
    ∃ (alpha : ∀ M : CochainComplex (ModuleCat.{u} A) ℤ,
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (S.obj M) ≅
          (ModuleCat.extendScalars f).obj (Sl.obj ((extend A Aq).obj M)))
      (beta : ∀ M : CochainComplex (ModuleCat.{u} A) ℤ,
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (T.obj M) ≅
          (ModuleCat.extendScalars f).obj (Tl.obj ((extend A Aq).obj M))),
      (∀ (M N : CochainComplex (ModuleCat.{u} A) ℤ) (g : M ⟶ N),
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map (S.map g) ≫
            (alpha N).hom =
          (alpha M).hom ≫ (ModuleCat.extendScalars f).map
            (Sl.map ((extend A Aq).map g))) ∧
      (∀ (M N : CochainComplex (ModuleCat.{u} A) ℤ) (g : M ⟶ N),
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map (T.map g) ≫
            (beta N).hom =
          (beta M).hom ≫ (ModuleCat.extendScalars f).map
            (Tl.map ((extend A Aq).map g))) ∧
      (∀ M : CochainComplex (ModuleCat.{u} A) ℤ,
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map (c.app M) ≫
            (beta M).hom =
          (alpha M).hom ≫ (ModuleCat.extendScalars f).map
            (cl.app ((extend A Aq).obj M))) := by
  classical
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let := HasDerivedCategory.standard (ModuleCat.{u} B)
  let := HasDerivedCategory.standard (ModuleCat.{u} Rp)
  let := HasDerivedCategory.standard (ModuleCat.{u} Bp)
  let : Algebra (Aq ⊗[Rp] Bp) D := f.toAlgebra
  let : IsScalarTower Aq (Aq ⊗[Rp] Bp) D :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact (_hfA a).symm)
  let : IsScalarTower Bp (Aq ⊗[Rp] Bp) D :=
    IsScalarTower.of_algebraMap_eq' (by ext b; exact (_hfB b).symm)
  let : IsScalarTower B (A ⊗[R] B) D :=
    IsScalarTower.of_algebraMap_eq' (by ext b; exact _hB b)
  let P := resolution A
  let J := extend A Aq
  let L := fun M ↦ ModuleCat.baseDerivedTensorCohomologyModel R A B (P.obj M) D
  let K := fun M ↦ ModuleCat.baseDerivedTensorCohomologyModel Rp Aq Bp (J.obj (P.obj M)) D
  have hP (M : CochainComplex (ModuleCat.{u} A) ℤ) :
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat (P.obj M) :=
    (flatResolution A).kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le M
  have hpi (M : CochainComplex (ModuleCat.{u} A) ℤ) :
      QuasiIso ((augmentation A).app M) := by
    dsimp [augmentation]
    infer_instance
  have hfglobal : (algebraMap (A ⊗[R] B) D).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat D q'.asIdeal.primeCompl)
  have hflocal : (algebraMap (Aq ⊗[Rp] Bp) D).Flat :=
    affineTensorLocalization_flat R A B q' Rp Aq Bp D _hB f _hfA _hfB
  obtain ⟨sigma, gamma, ngamma, nsigma, cgamma⟩ :=
    prescribedTensorCohomology_model_realization R A B D _ (𝟭 _) P
      (augmentation A) hpi hP i S T eS eT c hS hT hc hfglobal L
  let eSl' : (J ⋙ Sl) ⋙
      ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
        J ⋙ source Rp Aq Bp i :=
    NatIso.ofComponents (fun M ↦ eSl.app (J.obj M)) (fun g ↦ eSl.hom.naturality (J.map g))
  let eTl' : (J ⋙ Tl) ⋙
      ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
        J ⋙ target Rp Aq Bp i :=
    NatIso.ofComponents (fun M ↦ eTl.app (J.obj M)) (fun g ↦ eTl.hom.naturality (J.map g))
  have hc' : Functor.whiskerRight (Functor.whiskerLeft J cl)
      (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom) ≫ eTl'.hom =
        eSl'.hom ≫ Functor.whiskerLeft J (comparison Rp Aq Bp i) := by
    apply NatTrans.ext
    funext M
    exact congrArg (fun t ↦ t.app (J.obj M)) hcl
  have hpilocal (M : CochainComplex (ModuleCat.{u} A) ℤ) :
      QuasiIso ((Functor.whiskerRight (augmentation A) J).app M) := by
    have := hpi M
    have : (algebraMap A Aq).Flat :=
      RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat Aq (q'.asIdeal.comap (algebraMap A (A ⊗[R] B))).primeCompl)
    let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat this
    change QuasiIso (J.map ((augmentation A).app M))
    infer_instance
  obtain ⟨sigmal, gammal, ngammal, nsigmal, cgammal⟩ :=
    prescribedTensorCohomology_model_realization Rp Aq Bp D _ J (P ⋙ J)
      (Functor.whiskerRight (augmentation A) J) hpilocal
      (fun M ↦ kFlat_extend A Aq (P.obj M) (hP M)) i (J ⋙ Sl) (J ⋙ Tl) eSl' eTl'
      (Functor.whiskerLeft J cl) (fun M ↦ hSl (J.obj M)) (fun M ↦ hTl (J.obj M))
      hc' hflocal K
  let q := q'.asIdeal.comap (algebraMap A (A ⊗[R] B))
  let p' := q'.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom
  let p := q'.asIdeal.comap (algebraMap R (A ⊗[R] B))
  have hp : p = q.comap (algebraMap R A) := by
    dsimp [p, q]
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R A (A ⊗[R] B)]
  obtain ⟨e, ce, ne⟩ := derivedTensor_localization_cohomology R A B Rp Aq Bp D
    q'.asIdeal q p' p rfl rfl hp i
  let f0 := (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B))
  let f1 := (algebraMap (Aq ⊗[Rp] Bp) D).comp (algebraMap Aq (Aq ⊗[Rp] Bp))
  have hcoeff : f1.comp (algebraMap A Aq) = f0 := by
    dsimp [f0, f1]
    rw [← IsScalarTower.algebraMap_eq Aq (Aq ⊗[Rp] Bp) D,
      ← IsScalarTower.algebraMap_eq A Aq D,
      ← IsScalarTower.algebraMap_eq A (A ⊗[R] B) D]
  let tau := coefficientExtensionIso A Aq D (algebraMap A Aq) f0 f1 hcoeff
  let EL := ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)
  let ER := ModuleCat.extendScalars f
  let alpha := fun M ↦ EL.mapIso (sigma M) ≪≫ e M (L M) (K M) ≪≫
    ER.mapIso (sigmal M).symm
  let beta := fun M ↦ gamma M ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.up ℤ) i).mapIso
      (tau.app (P.obj M)) ≪≫ (gammal M).symm
  refine ⟨alpha, beta, ?_, ?_, ?_⟩
  · intro M N g
    obtain ⟨delta, hdelta, hsigma⟩ := nsigma M N g
    obtain ⟨epsilon, hepsilon, hsigmal⟩ := nsigmal M N g
    have hn := ne M N g (L M) (K M) (L N) (K N) delta epsilon
      ((sigma M).inv ≫ S.map g ≫ (sigma N).hom)
      ((sigmal M).inv ≫ Sl.map (J.map g) ≫ (sigmal N).hom)
      hdelta hepsilon hsigma hsigmal
    change EL.map ((sigma M).inv ≫ S.map g ≫ (sigma N).hom) ≫
        (e N (L N) (K N)).hom =
      (e M (L M) (K M)).hom ≫
        ER.map ((sigmal M).inv ≫ Sl.map (J.map g) ≫ (sigmal N).hom) at hn
    have ht := congrArg
      (fun t ↦ EL.map (sigma M).hom ≫ t ≫ ER.map (sigmal N).inv) hn
    simpa [alpha, EL, ER, Functor.map_comp, Category.assoc] using ht
  · intro M N g
    let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.up ℤ) i
    have hg : EL.map (T.map g) ≫ (gamma N).hom =
        (gamma M).hom ≫ H.map
          (((ModuleCat.extendScalars f0).mapHomologicalComplex (.up ℤ)).map (P.map g)) :=
      ngamma M N g
    have hgl : ER.map (Tl.map (J.map g)) ≫ (gammal N).hom =
        (gammal M).hom ≫ H.map
          ((((ModuleCat.extendScalars (algebraMap A Aq)).mapHomologicalComplex (.up ℤ)) ⋙
            ((ModuleCat.extendScalars f1).mapHomologicalComplex (.up ℤ))).map (P.map g)) :=
      ngammal M N g
    have htau := congrArg H.map (tau.hom.naturality (P.map g))
    simp only [Functor.map_comp] at htau
    have hgl' : H.map
        ((((ModuleCat.extendScalars (algebraMap A Aq)).mapHomologicalComplex (.up ℤ)) ⋙
          ((ModuleCat.extendScalars f1).mapHomologicalComplex (.up ℤ))).map (P.map g)) =
        (gammal M).inv ≫ ER.map (Tl.map (J.map g)) ≫ (gammal N).hom := by
      apply (cancel_epi (gammal M).hom).1
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hgl.symm
    apply (cancel_mono (gammal N).hom).1
    change EL.map (T.map g) ≫
        ((gamma N).hom ≫ H.map (tau.hom.app (P.obj N)) ≫ (gammal N).inv) ≫
          (gammal N).hom =
      ((gamma M).hom ≫ H.map (tau.hom.app (P.obj M)) ≫ (gammal M).inv) ≫
        ER.map (Tl.map (J.map g)) ≫ (gammal N).hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, hg, Category.assoc, htau, hgl']
  · intro M
    apply (cancel_mono (gammal M).hom).1
    have hce := ce M (L M) (K M) (tau.app (P.obj M))
      (coefficientExtensionIso_tmul A Aq D (algebraMap A Aq) f0 f1 hcoeff (P.obj M))
    dsimp [alpha, beta]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, cgamma M, Category.assoc]
    change EL.map (sigma M).hom ≫ (L M).localizedComparison i ≫
      HomologicalComplex.homologyMap (tau.app (P.obj M)).hom i = _
    rw [hce]
    have hl : ER.map (sigmal M).inv ≫ ER.map (cl.app (J.obj M)) ≫ (gammal M).hom =
        (K M).localizedComparison i := by
      change ER.map (sigmal M).inv ≫
        (ModuleCat.extendScalars (algebraMap (Aq ⊗[Rp] Bp) D)).map
          ((Functor.whiskerLeft J cl).app M) ≫ (gammal M).hom = _
      rw [cgammal M]
      change ER.map (sigmal M).inv ≫ ER.map (sigmal M).hom ≫
        (K M).localizedComparison i = _
      rw [← Category.assoc, ← ER.map_comp, Iso.inv_hom_id, ER.map_id,
        Category.id_comp]
    rw [hl]

end RingTensorCohomology
