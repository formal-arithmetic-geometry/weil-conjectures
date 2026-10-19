/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.Algebra.Homology.DerivedTensor
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Homotopy

import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.Algebra.Homology.BifunctorFlip
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# Resolution independence of the pro-etale derived tensor product

Source: Weil blueprint, sec-smooth-purity/sk-lem-sf-mate, order 1870;
Stacks Project, Cohomology on Sites, Tags 06YT and 06YU
(blueprint: lem-weil-derived-tensor-resolution-independent).

The comparison family is quantified over all K-flat resolutions of the fixed first factor.
Its characterization by chain maps is imposed for every homotopy lift. No direct lift is
assumed to exist, and no K-flat resolution of the second factor is required.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{w}) (A : Type w) [CommRing A]

/-- The total tensor complex, specialized to the constant ring sheaf on the pro-etale site.
This is precisely `CochainComplex.mapBifunctor` with the sheaf tensor, as in `derivedTensor`.
Source: Stacks Tag 06YU (blueprint: lem-weil-derived-tensor-resolution-independent). -/
def resolutionTensor (K₂ P : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ) :
    CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ :=
  letI := SheafOfModules.monoidalCategory
    ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
      (CommRingCat.of (ULift.{w + 1, w} A)))
  CochainComplex.mapBifunctor P K₂ (curriedTensor _)

/-- The ordinary map `α ⊗ 1`, formed by the recorded total tensor construction.
Source: Stacks Tag 06YT (blueprint: lem-weil-derived-tensor-resolution-independent). -/
def resolutionTensorMap (K₂ : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ)
    {P P' : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ} (α : P ⟶ P') :
    resolutionTensor Y A K₂ P ⟶ resolutionTensor Y A K₂ P' :=
  letI := SheafOfModules.monoidalCategory
    ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
      (CommRingCat.of (ULift.{w + 1, w} A)))
  HomologicalComplex.mapBifunctorMap α (𝟙 K₂) (curriedTensor _) (ComplexShape.up ℤ)

/-- The localization of `α ⊗ 1` between the chosen-resolution models `derivedTensor`.
The localization is exactly `HasDerivedCategory.standard`, as in `proEtaleDerivedCategory`.
Source: Stacks Tag 06YU (blueprint: lem-weil-derived-tensor-resolution-independent). -/
def resolutionTensorMapQ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ)
    {P P' : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ}
    (q : P ⟶ K₁) (q' : P' ⟶ K₁) (hq : QuasiIso q) (hq' : QuasiIso q')
    (hP : P.IsAcyclicTensorKFlat) (hP' : P'.IsAcyclicTensorKFlat) (α : P ⟶ P') :
    derivedTensor Y A K₁ K₂ P q hq hP ⟶ derivedTensor Y A K₁ K₂ P' q' hq' hP' :=
  letI := HasDerivedCategory.standard
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A)))))
  DerivedCategory.Q.map (resolutionTensorMap Y A K₂ α)

set_option hygiene false in
local notation "𝓡" =>
  (constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
    (CommRingCat.of (ULift.{w + 1, w} A))
set_option hygiene false in
local notation "𝓜" => SheafOfModules.{w + 1}
  ((sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj 𝓡)

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
private theorem tensor_right_quasiIso
    {E E' K : CochainComplex 𝓜 ℤ} (α : E ⟶ E')
    (hα : QuasiIso α) (hK : K.IsAcyclicTensorKFlat) :
    QuasiIso (resolutionTensorMap Y A K α) := by
  let := SheafOfModules.monoidalCategory 𝓡
  have := SheafOfModules.tensorPreadditive 𝓡
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso
    (CochainComplex.mapBifunctorMappingCone₁Iso α K (curriedTensor _))

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
private theorem tensor_left_quasiIso
    {E E' K : CochainComplex 𝓜 ℤ} (α : E ⟶ E')
    (hα : QuasiIso α) (hK : K.IsAcyclicTensorKFlat) :
    let := SheafOfModules.monoidalCategory 𝓡
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) α (curriedTensor _) (.up ℤ)) := by
  let := SheafOfModules.monoidalCategory 𝓡
  let := SheafOfModules.symmetricCategory 𝓡
  have := SheafOfModules.tensorPreadditive 𝓡
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  let F := curriedTensor 𝓜
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ ((CochainComplex.mappingCone α).X p) (K.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right
            ((CochainComplex.mappingCone α).X p) (K.d q q')).symm)) (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left
          ((CochainComplex.mappingCone α).d p p') (K.X q)).symm)
  have ht' : (CochainComplex.mapBifunctor K (CochainComplex.mappingCone α) F).Acyclic := by
    intro i
    exact (ht i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso K (CochainComplex.mappingCone α) F (.up ℤ))
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht' i).of_iso (CochainComplex.mapBifunctorMappingCone₂Iso K α F)

private theorem common_refinement
    (K P P' : CochainComplex 𝓜 ℤ) (q : P ⟶ K) (q' : P' ⟶ K)
    (hq : QuasiIso q) (hq' : QuasiIso q') :
    ∃ (S : CochainComplex 𝓜 ℤ) (a : S ⟶ P) (b : S ⟶ P'),
      S.IsAcyclicTensorKFlat ∧ QuasiIso a ∧ QuasiIso b ∧
        Nonempty (Homotopy (a ≫ q) (b ≫ q')) := by
  let := HasDerivedCategory.standard 𝓜
  let H := HomotopyCategory.quotient 𝓜 (.up ℤ)
  let W := HomotopyCategory.quasiIso 𝓜 (.up ℤ)
  let φ : W.LeftFraction (H.obj P) (H.obj P') :=
    MorphismProperty.LeftFraction.mk (H.map q) (H.map q')
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff q').2 hq')
  obtain ⟨ψ, hψ⟩ := φ.exists_rightFraction
  obtain ⟨M, s, hs, f, rfl⟩ := ψ.cases
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨s, rfl⟩ := H.map_surjective s
  obtain ⟨f, rfl⟩ := H.map_surjective f
  have hs' : QuasiIso s := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs
  have h : Homotopy (s ≫ q) (f ≫ q') :=
    HomotopyCategory.homotopyOfEq _ _ (by simpa [φ, H] using hψ)
  have hfcomp : QuasiIso (f ≫ q') := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap, ← h.homologyMap_eq]
    infer_instance
  have hf : QuasiIso f := quasiIso_of_comp_right f q'
  obtain ⟨S, r, hS, _, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients M
  refine ⟨S, r ≫ s, r ≫ f, hS, inferInstance, inferInstance, ⟨?_⟩⟩
  exact (Homotopy.ofEq (Category.assoc _ _ _)).trans
    ((h.compLeft r).trans (Homotopy.ofEq (Category.assoc _ _ _).symm))

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
-- Large sheaf tensor instances occur repeatedly in the comparison-family proof.
/-- Resolution independence, including the canonical comparison and all its normalizations.
Source: Stacks Tags 06YT and 06YU and the preceding independence paragraph
(blueprint: lem-weil-derived-tensor-resolution-independent).

Proof:
1. Tensoring a quasi-isomorphism with a K-flat second factor preserves quasi-isomorphisms:
   its cone tensors to an acyclic complex, and the tensor/cone isomorphism applies.
   The braiding of sheaf modules, the total-complex flip, and the second-variable
   tensor/cone isomorphism give the corresponding assertion for a K-flat first factor.
2. Choose a K-flat resolution r : R → K₂. For every q : P → K₁ under consideration,
   the two maps P ⊗ R → P ⊗ K₂ and P ⊗ R → K₁ ⊗ R are quasi-isomorphisms.
   Their localized zigzag gives an isomorphism e(P,q) to the common model Q(K₁ ⊗ R).
   Define c(P,P') as e(P,q) followed by the inverse of e(P',q').
3. Tensor functoriality and tensor homotopy invariance prove that each supplied
   homotopy lift commutes with these zigzags. Cancellation gives agreement with its
   localized tensor map. Cancellation also proves identity and cocycle.
4. Such a lift is a quasi-isomorphism by homology and two-out-of-three. Applying the
   naturality square for r and the two assertions of Step 1 proves its tensor map
   is a quasi-isomorphism, even though K₂ itself need not be K-flat.
5. The right-calculus Ore axiom supplies a common roof over q and q' in the homotopy
   category. Represent its legs by chain maps and resolve its middle complex by a
   K-flat complex S. Two-out-of-three makes both legs quasi-isomorphisms. Agreement
   fixes every comparison from S to P and P'; the cocycle and cancellation therefore
   fix the comparison from P to P', proving uniqueness. -/
theorem derivedTensor_resolution_independent
    (K₁ K₂ : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ) :
    (∀ (P P' : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ)
      (q : P ⟶ K₁) (q' : P' ⟶ K₁),
      QuasiIso q → QuasiIso q' → P.IsAcyclicTensorKFlat → P'.IsAcyclicTensorKFlat →
      ∀ (α : P ⟶ P'), Homotopy (α ≫ q') q →
        QuasiIso (resolutionTensorMap Y A K₂ α)) ∧
    ∃! c : ∀ (P P' : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ)
      (q : P ⟶ K₁) (q' : P' ⟶ K₁)
      (hq : QuasiIso q) (hq' : QuasiIso q')
        (hP : P.IsAcyclicTensorKFlat) (hP' : P'.IsAcyclicTensorKFlat),
      (derivedTensor Y A K₁ K₂ P q hq hP ≅ derivedTensor Y A K₁ K₂ P' q' hq' hP'),
      (∀ (P P' : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ)
        (q : P ⟶ K₁) (q' : P' ⟶ K₁)
        (hq : QuasiIso q) (hq' : QuasiIso q')
        (hP : P.IsAcyclicTensorKFlat) (hP' : P'.IsAcyclicTensorKFlat)
        (α : P ⟶ P'), Homotopy (α ≫ q') q →
        (c P P' q q' hq hq' hP hP').hom =
          resolutionTensorMapQ Y A K₁ K₂ q q' hq hq' hP hP' α) ∧
      (∀ (P : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ)
        (q : P ⟶ K₁) (hq : QuasiIso q) (hP : P.IsAcyclicTensorKFlat),
        c P P q q hq hq hP hP = Iso.refl _) ∧
      (∀ (P P' P'' : CochainComplex
      (SheafOfModules.{w + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
              (CommRingCat.of (ULift.{w + 1, w} A))))) ℤ)
        (q : P ⟶ K₁) (q' : P' ⟶ K₁) (q'' : P'' ⟶ K₁)
        (hq : QuasiIso q) (hq' : QuasiIso q') (hq'' : QuasiIso q'')
        (hP : P.IsAcyclicTensorKFlat) (hP' : P'.IsAcyclicTensorKFlat)
        (hP'' : P''.IsAcyclicTensorKFlat),
        c P P' q q' hq hq' hP hP' ≪≫ c P' P'' q' q'' hq' hq'' hP' hP'' =
          c P P'' q q'' hq hq'' hP hP'') := by
  let := SheafOfModules.monoidalCategory 𝓡
  have := SheafOfModules.tensorPreadditive 𝓡
  obtain ⟨R, r, hR, _, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K₂
  have hR' : R.IsAcyclicTensorKFlat := hR
  let T := (curriedTensor 𝓜).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
  have hright {E E' : CochainComplex 𝓜 ℤ} (f : E ⟶ E') (hf : QuasiIso f) :
      QuasiIso ((T.map f).app R) := by
    simpa [T, resolutionTensorMap] using tensor_right_quasiIso Y A f hf hR'
  have hleft (P : CochainComplex 𝓜 ℤ) (hP : P.IsAcyclicTensorKFlat) :
      QuasiIso ((T.obj P).map r) := by
    simpa [T] using tensor_left_quasiIso Y A r hr hP
  constructor
  · intro P P' q q' hq hq' hP hP' α hα
    have hqα : QuasiIso (α ≫ q') := by
      rw [quasiIso_iff]
      intro i
      rw [quasiIsoAt_iff_isIso_homologyMap, hα.homologyMap_eq]
      infer_instance
    have hα' : QuasiIso α := quasiIso_of_comp_right α q'
    have hv := hleft P hP
    have hv' := hleft P' hP'
    have hh := hright α hα'
    have heq := (T.map α).naturality r
    have hcomp : QuasiIso ((T.obj P).map r ≫ (T.map α).app K₂) := by
      rw [heq]
      infer_instance
    simpa only [T, resolutionTensorMap, resolutionTensor,
      Functor.map₂HomologicalComplex_map_app] using
      quasiIso_of_comp_left ((T.obj P).map r) ((T.map α).app K₂)
  · let := HasDerivedCategory.standard 𝓜
    let Q := DerivedCategory.Q (C := 𝓜)
    let e (P : CochainComplex 𝓜 ℤ) (q : P ⟶ K₁)
        (hq : QuasiIso q) (hP : P.IsAcyclicTensorKFlat) :
        derivedTensor Y A K₁ K₂ P q hq hP ≅ Q.obj ((T.obj K₁).obj R) :=
      by
        have := hleft P hP
        have := hright q hq
        exact (asIso (Q.map ((T.obj P).map r))).symm ≪≫
          asIso (Q.map ((T.map q).app R))
    have he (P P' : CochainComplex 𝓜 ℤ) (q : P ⟶ K₁) (q' : P' ⟶ K₁)
        (hq : QuasiIso q) (hq' : QuasiIso q')
        (hP : P.IsAcyclicTensorKFlat) (hP' : P'.IsAcyclicTensorKFlat)
        (α : P ⟶ P') (hα : Homotopy (α ≫ q') q) :
        Q.map ((T.map α).app K₂) ≫ (e P' q' hq' hP').hom = (e P q hq hP).hom := by
      have hqeq : Q.map ((T.map α).app R ≫ (T.map q').app R) =
          Q.map ((T.map q).app R) := by
        rw [← NatTrans.comp_app, ← T.map_comp]
        have h := DerivedCategory.Q_map_eq_of_homotopy 𝓜
          (HomologicalComplex.mapBifunctorMapHomotopy₁ hα (𝟙 R)
            (curriedTensor 𝓜) (.up ℤ))
        simpa only [T, Q, Functor.map₂HomologicalComplex_map_app] using h
      have := hleft P hP
      have := hleft P' hP'
      apply (cancel_epi (Q.map ((T.obj P).map r))).1
      dsimp only [e, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
      rw [← Category.assoc, ← Q.map_comp, (T.map α).naturality r, Q.map_comp]
      simpa only [Category.assoc, IsIso.hom_inv_id_assoc, Q.map_comp] using hqeq
    let c := fun P P' q q' hq hq' hP hP' ↦
      e P q hq hP ≪≫ (e P' q' hq' hP').symm
    have hc (P P' : CochainComplex 𝓜 ℤ) (q : P ⟶ K₁) (q' : P' ⟶ K₁)
        (hq : QuasiIso q) (hq' : QuasiIso q')
        (hP : P.IsAcyclicTensorKFlat) (hP' : P'.IsAcyclicTensorKFlat)
        (α : P ⟶ P') (hα : Homotopy (α ≫ q') q) :
        (c P P' q q' hq hq' hP hP').hom =
          resolutionTensorMapQ Y A K₁ K₂ q q' hq hq' hP hP' α := by
      apply (cancel_mono (e P' q' hq' hP').hom).1
      simpa only [c, Iso.trans_hom, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, resolutionTensorMapQ, resolutionTensorMap,
        resolutionTensor, T, Q,
        Functor.map₂HomologicalComplex_map_app]
        using (he P P' q q' hq hq' hP hP' α hα).symm
    have hid (P : CochainComplex 𝓜 ℤ) (q : P ⟶ K₁)
        (hq : QuasiIso q) (hP : P.IsAcyclicTensorKFlat) :
        c P P q q hq hq hP hP = Iso.refl _ := by
      ext
      simp [c]
    have hcomp (P P' P'' : CochainComplex 𝓜 ℤ)
        (q : P ⟶ K₁) (q' : P' ⟶ K₁) (q'' : P'' ⟶ K₁)
        (hq : QuasiIso q) (hq' : QuasiIso q') (hq'' : QuasiIso q'')
        (hP : P.IsAcyclicTensorKFlat) (hP' : P'.IsAcyclicTensorKFlat)
        (hP'' : P''.IsAcyclicTensorKFlat) :
        c P P' q q' hq hq' hP hP' ≪≫ c P' P'' q' q'' hq' hq'' hP' hP'' =
          c P P'' q q'' hq hq'' hP hP'' := by
      ext
      simp [c]
    refine ⟨c, ⟨hc, hid, hcomp⟩, ?_⟩
    rintro d ⟨hd, _, hdcomp⟩
    funext P P' q q' hq hq' hP hP'
    obtain ⟨S, a, b, hS, ha, hb, ⟨h⟩⟩ := common_refinement Y A K₁ P P' q q' hq hq'
    let s := a ≫ q
    have hs : QuasiIso s := inferInstance
    have heqa : d S P s q hs hq hS hP = c S P s q hs hq hS hP := by
      apply Iso.ext
      exact (hd S P s q hs hq hS hP a (Homotopy.refl _)).trans
        (hc S P s q hs hq hS hP a (Homotopy.refl _)).symm
    have heqb : d S P' s q' hs hq' hS hP' = c S P' s q' hs hq' hS hP' := by
      apply Iso.ext
      exact (hd S P' s q' hs hq' hS hP' b h.symm).trans
        (hc S P' s q' hs hq' hS hP' b h.symm).symm
    have heqc : c S P s q hs hq hS hP ≪≫ d P P' q q' hq hq' hP hP' =
        c S P s q hs hq hS hP ≪≫ c P P' q q' hq hq' hP hP' := by
      calc
        _ = d S P' s q' hs hq' hS hP' := by rw [← heqa, hdcomp]
        _ = c S P' s q' hs hq' hS hP' := heqb
        _ = _ := (hcomp S P P' s q q' hs hq hq' hS hP hP').symm
    apply Iso.ext
    exact (cancel_epi (c S P s q hs hq hS hP).hom).1 (congrArg Iso.hom heqc)

end AlgebraicGeometry.Scheme
