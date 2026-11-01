/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
import WeilConjectures.SixFunctors.AdicQbarRealization.AdicCochainTensorReindexing
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Tensor reindexing on the ambient K-flat models

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] WeilConjectures.LocallyFiniteAdicRealization.ringSheaf
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme CategoryTheory.Functor
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

private theorem modulePull_isEquivalence {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y} (B : RingReindex l X g R S) :
    (modulePull l X g B).IsEquivalence := by
  let RY := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l Y S)
  let RX := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l X R)
  let ci : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj RY ≅ RX :=
    (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso B.iso
  let c := ci.hom
  let F := proEtaleIsoPostcompose g
  let G := proEtaleIsoPostcompose (inv g)
  let e := proEtaleIsoPostcompose_equivalence g
  let E : X.ProEt ≌ Y.ProEt :=
    CategoryTheory.Equivalence.mk F G e.2.1.some.symm e.2.2.1.some
  have : E.functor.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    proEtaleIsoPostcompose_isContinuous g
  have : E.inverse.IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
    proEtaleIsoPostcompose_isContinuous (inv g)
  let adj := E.toAdjunction
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
    (ProEt.topology X) (ProEt.topology Y)
  let φ := inv c
  let ψ : RY ⟶ (G.sheafPushforwardContinuous RingCat _ _).obj RX :=
    shAdj.unit.app RY ≫ (G.sheafPushforwardContinuous _ _ _).map c
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit) RY.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext U : 2
    simp [ψ, φ, shAdj, adj]
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit) RX.obj = 𝟙 RX.obj := by
    have hh : φ ≫ (E.functor.sheafPushforwardContinuous RingCat _ _).map ψ ≫
        shAdj.counit.app RX = 𝟙 RX := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [shAdj.counit.naturality c]
      have ht := shAdj.left_triangle_components RY
      calc
        _ = φ ≫ ((E.functor.sheafPushforwardContinuous RingCat _ _).map
            (shAdj.unit.app RY) ≫ shAdj.counit.app
              ((E.functor.sheafPushforwardContinuous RingCat _ _).obj RY)) ≫ c := by
          simp only [Category.assoc, Functor.id_map]
          rfl
        _ = φ ≫ 𝟙 _ ≫ c := congrArg (fun h ↦ φ ≫ h ≫ c) ht
        _ = _ := by simp [φ]
    exact congrArg (fun f ↦ f.hom) hh
  let EM := SheafOfModules.pushforwardPushforwardEquivalence E φ ψ H₁ H₂
  exact EM.isEquivalence_functor

/-- Scheme-isomorphism reindexing carries the specified ambient tensor models to each other.
Source: BS Remark 6.8.15; Stacks 07A4; the K-flat part of lem-sf-adic-reindexing-core
(blueprint: lem-sf-adic-tensor-reindexing-models).

Proof: The sectionwise site equivalence and the coefficient isomorphism B give an exact
monoidal equivalence of ordinary module categories. Its tensor comparison sends a pure
tensor of sections to the same tensor at the reindexed object. Extend this comparison
by the coproduct injections in each total degree; additivity preserves the differential,
including its Koszul sign. The inverse sectionwise comparison gives the inverse total
map. The exact monoidal equivalence preserves acyclic complexes and all tensor tests
for K-flatness. Thus the total comparison descends through the two supplied K-flat model
presentations A.models and C.models. The descended comparison satisfies precisely their
representative equation, by naturality of the exact-derived factorization. Finally the
coefficient isomorphism gives the map of degree-zero coefficient-unit complexes, and its
section formula is the B formula. This argument concerns the ambient module categories
and does not use or assert compatibility with common-stage realization. -/
theorem exists_tensor_reindexing_models {X Y : Scheme.{u}} (g : X ≅ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : At l X R) (C : At l Y S) (B : RingReindex l X g.hom R S) :
    Nonempty (ReindexTensor l X g.hom A C B) := by
  classical
  obtain ⟨chain, hpure⟩ := exists_cochain_tensor_reindexing l g R S B
  have hE := modulePull_isEquivalence l g.hom B
  let F := (modulePull l X g.hom B).mapHomologicalComplex (.up ℤ)
  have : F.IsEquivalence :=
    ((modulePull l X g.hom B).asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  let PY : ObjectProperty (CochainComplex (modules l Y S) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology Y) (R := ring l Y S)
  let PX : ObjectProperty (CochainComplex (modules l X R) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
  have hkflat : ∀ P, PY P → PX (F.obj P) := by
    intro P hP N hN
    let N' := F.objPreimage N
    let e := F.objObjPreimageIso N
    have hN' : N'.Acyclic := by
      intro n
      apply ((N'.sc n).exact_map_iff_of_faithful (modulePull l X g.hom B)).1
      change (F.obj N').ExactAt n
      exact (hN n).of_iso e.symm
    have hNP := hP N' hN'
    have hmap : (F.obj ((coefficientTotalTensor.{u + 1, u + 1, u}
        (ProEt.topology Y) (ring l Y S)).obj (N', P))).Acyclic := by
      intro n
      exact ((((coefficientTotalTensor.{u + 1, u + 1, u}
        (ProEt.topology Y) (ring l Y S)).obj (N', P)).sc n).exact_map_iff_of_faithful
          (modulePull l X g.hom B)).2 (hNP n)
    let tX := coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
    let i := chain.app (N', P) ≪≫ tX.mapIso (Iso.prod e (Iso.refl (F.obj P)))
    intro n
    exact (hmap n).of_iso i
  let H : ObjectProperty (HomotopyCategory (modules l Y S) (.up ℤ)) := fun K ↦ PY K.as
  have hres : ∀ K : HomotopyCategory (modules l Y S) (.up ℤ),
      ∃ (L : H.FullSubcategory) (f : L.obj ⟶ K),
        HomotopyCategory.quasiIso (modules l Y S) (.up ℤ) f := by
    intro K
    obtain ⟨P, f, hp, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients K.as
    refine ⟨⟨(HomotopyCategory.quotient _ (.up ℤ)).obj P, hp⟩,
      (HomotopyCategory.quotient _ (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex (modules l Y S) ℤ)
    (H := HomotopyCategory (modules l Y S) (.up ℤ))
    (D := DerivedCategory (modules l Y S)) (DerivedCategory (modules l X R))
    (HomotopyCategory.quotient _ (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso _ (.up ℤ)) DerivedCategory.Qh PY H (fun _ ↦ Iff.rfl) hres
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory (modules l X R))).mapIso
    (NatIso.prod (isoWhiskerLeft PY.ι (DerivedCategory.quotientCompQhIso _))
      (isoWhiskerLeft PY.ι (DerivedCategory.quotientCompQhIso _))))
  obtain ⟨tensor, htensor, _⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q F (derivedPull l X g.hom B)
    (modulePull l X g.hom B).mapDerivedCategoryFactors.hom PY PX hkflat ff'
    (coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S))
    (coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R))
    C.closed.tensor A.closed.tensor C.models.comparison A.models.comparison chain
    (fun _ _ ↦ inferInstance) (fun _ _ _ _ ↦ inferInstance)
  have hunit : ∃ unitCochain, reindexUnitSections l X g.hom B unitCochain := by
    let W := sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    let ci : (isoSectionwiseInverseImage g.hom RingCat.{u + 1}).obj
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l Y S)) ≅
        W.obj (ring l X R) := W.mapIso B.iso
    let m : SheafOfModules.unit (W.obj (ring l X R)) ⟶
        (modulePull l X g.hom B).obj (SheafOfModules.unit
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l Y S))) :=
      SheafOfModules.unitToPushforwardObjUnit (F := proEtaleIsoPostcompose g.hom) (inv ci.hom)
    let G := SheafOfModules.toSheaf (W.obj (ring l X R)) ⋙
      sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}
    have hm : IsIso (G.map m) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro U
      rw [ConcreteCategory.isIso_iff_bijective]
      change Function.Bijective ((inv ci.hom).hom.app U)
      exact ConcreteCategory.bijective_of_isIso _
    have : IsIso m := isIso_of_reflects_iso m G
    let e := (asIso m).symm
    let j := (HomologicalComplex.singleMapHomologicalComplex
      (modulePull l X g.hom B) (.up ℤ) 0).app _ ≪≫
        (HomologicalComplex.single (modules l X R) (.up ℤ) 0).mapIso e
    refine ⟨j, ?_⟩
    intro U a
    have he : e.hom.val.app U a = B.iso.hom.hom.app U a := by
      have hc : m.val.app U (B.iso.hom.hom.app U a) = a := by
        change (inv ci.hom).hom.app U (ci.hom.hom.app U a) = a
        exact congrArg (fun f ↦ f.hom.app U a) (IsIso.hom_inv_id ci.hom)
      have hi := congrArg (fun f ↦ f.val.app U (B.iso.hom.hom.app U a))
        (asIso m).hom_inv_id
      change e.hom.val.app U (m.val.app U (B.iso.hom.hom.app U a)) = _ at hi
      rw [hc] at hi
      exact hi
    let sy := HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l Y S)))
    let sx := HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit (W.obj (ring l X R)))
    have hj : j.hom.f 0 = (modulePull l X g.hom B).map sy.hom ≫ e.hom ≫ sx.inv := by
      dsimp only [j, Iso.trans_hom, HomologicalComplex.comp_f, Functor.mapIso_hom]
      simp only [Iso.app_hom]
      rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        HomologicalComplex.single_map_f_self]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rfl
    change (j.hom.f 0).val.app U
      (sy.inv.val.app ((proEtaleIsoPostcompose g.hom).op.obj U) a) =
      sx.inv.val.app U (B.iso.hom.hom.app U a)
    rw [hj]
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    have hy := congrArg (fun h ↦ h.val.app
      ((proEtaleIsoPostcompose g.hom).op.obj U) a) sy.inv_hom_id
    change sy.hom.val.app _ (sy.inv.val.app _ a) = a at hy
    change sx.inv.val.app U (e.hom.val.app U
      (sy.hom.val.app _ (sy.inv.val.app _ a))) = _
    rw [hy, he]
  obtain ⟨unitCochain, hunit⟩ := hunit
  exact ⟨{ cochain := chain
           pure := hpure
           kflat := hkflat
           tensor := tensor
           representative := htensor
           unitCochain := unitCochain
           unit_sections := hunit }⟩

end WeilConjectures.AdicQbarRealization
