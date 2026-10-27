/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.Paper.ConcreteProjectionReductionData
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteCoefficientTensorCtf
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.ConcreteProperScalarTensorSquare
import Sheaf.Paper.ConcreteOpenScalarTensorSquare
import Sheaf.Paper.ConcreteSupportScalarIsomorphism
import Sheaf.Paper.ConcreteProjectionCoefficientCoherence

/-! # Concrete finite-reduction square for compactification projection

Source: current Weil blueprint, fix-prop-projection-formula, proof sentence 2;
Stacks Tags 0GL6, 0GL1, 0E48 and 07A4
(blueprint: lem-sf-concrete-projection-reduction-square).

The helpers give names to the actual objects and ordered composites in the square.
The representative presentations retain their normalized tensor and scalar adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.ConcreteProjectionReduction
open AlgebraicGeometry.ProEtale.OpenScalarTensor


variable (m : Models.{u}) (choices : Choices m)
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SheafOfModules.monoidalCategory
  derivedInternalHomOfUniverses CoefficientClosedStructure.tensor

private theorem tor_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude T A K a b) :
    HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem constructible_of_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    {K L : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n)} (e : K ≅ L)
    (h : intrinsicFiniteTorsionConstructible l E n hn T K) :
    intrinsicFiniteTorsionConstructible l E n hn T L := by
  let A := Padic.coefficientExtensionRing l E n
  have : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  refine ⟨h.1.subset ?_, ?_⟩
  · intro i hi hz
    exact hi (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)
  · intro i
    apply (proEtaleModuleRestriction_constructible_iff T A _).mpr
    exact isConstructible_of_iso
      ((proEtaleModuleRestriction T A).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e))
      ((proEtaleModuleRestriction_constructible_iff T A _).mp (h.2 i))

private theorem finiteTor_of_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    {K L : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E n)} (e : K ≅ L)
    (h : finiteTorConstructible l E n hn T K) :
    finiteTorConstructible l E n hn T L := by
  obtain ⟨hc, a, b, ht⟩ := h
  exact ⟨constructible_of_iso l E n hn T e hc, a, b, tor_of_iso T _ e a b ht⟩

private theorem tensor_tor
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (K L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing C.l E n))
    (hK : finiteTorConstructible C.l E n hn X K)
    (hL : finiteTorConstructible C.l E n hn X L)
    (a b c d : ℤ)
    (hKa : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing C.l E n) K a b)
    (hLc : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing C.l E n) L c d) :
    finiteTorConstructible C.l E n hn X ((tensor m _ X).obj (K, L)) ∧
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing C.l E n)
        ((tensor m _ X).obj (K, L)) (a + c) (b + d) := by
  classical
  let A := Padic.coefficientExtensionRing C.l E n
  let R := proEtaleConstantRing X A
  let K₀ := DerivedCategory.Q.objPreimage K
  let L₀ := DerivedCategory.Q.objPreimage L
  obtain ⟨P, p, hp, _, hqp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) K₀
  obtain ⟨Q, q, hq, _, hqq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) L₀
  have : QuasiIso p := hqp
  have : QuasiIso q := hqq
  let eP : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let eQ : DerivedCategory.Q.obj Q ≅ L :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso L
  have hp' : CochainComplex.IsAcyclicTensorKFlat (R := R) P :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hp
  have hid : QuasiIso (𝟙 P) := inferInstance
  have ht := (finiteCoefficient_tensor_ctf D C.l C.different E n hn X P Q P
    (𝟙 P) hid hp' a b (finiteTor_of_iso C.l E n hn X eP.symm hK)
    (tor_of_iso X A eP.symm a b hKa)
    (constructible_of_iso C.l E n hn X eQ.symm hL.1)).2 c d
      (finiteTor_of_iso C.l E n hn X eQ.symm hL) (tor_of_iso X A eQ.symm c d hLc)
  let e : derivedTensor X A P Q P (𝟙 P) hid hp' ≅
      (tensor m A X).obj (K, L) :=
    CoefficientTensorModels.iso _ R ((m X).closed R) ((m X).model R) P Q hp hq ≪≫
      (tensor m A X).mapIso (eP.prod eQ)
  exact ⟨finiteTor_of_iso C.l E n hn X e ht.1,
    tor_of_iso X A e (a + c) (b + d) ht.2⟩

private def supportComparisonNat {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    support A c ⋙ scalar m φ Y ⟶ scalar m φ X ⋙ support B c :=
  { app := supportComparison m φ c
    naturality := by
      intro K L a
      let h := Functor.whiskerLeft (support A c) (scalarIso m φ Y).hom ≫
        PurCompactSupport.comparison (coefficientChange φ) c ≫
        Functor.whiskerRight (scalarIso m φ X).inv (support B c)
      simpa only [supportComparison_eq, h, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app] using h.naturality a }

private def sourceComparisonNat {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    sourceFunctor m A c ⋙ scalar m φ Y ⟶
      (scalar m φ X).prod (scalar m φ Y) ⋙ sourceFunctor m B c :=
  Functor.whiskerLeft ((support A c).prod (𝟭 _)) (choices.scalarTensor φ Y).iso.hom ≫
    Functor.whiskerRight
      (NatTrans.prod (supportComparisonNat m φ c) (𝟙 (scalar m φ Y))) (tensor m B Y)

private def inputComparisonNat {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (𝟭 _).prod (constantPullback (A := A) f) ⋙ tensor m A X ⋙ scalar m φ X ⟶
      (scalar m φ X).prod (scalar m φ Y) ⋙
        (𝟭 _).prod (constantPullback (A := B) f) ⋙ tensor m B X :=
  Functor.whiskerLeft ((𝟭 _).prod (constantPullback (A := A) f))
      (choices.scalarTensor φ X).iso.hom ≫
    Functor.whiskerRight (NatTrans.prod (𝟙 (scalar m φ X)) (lambda m φ f).inv)
      (tensor m B X)

private def targetComparisonNat {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    targetFunctor m A c ⋙ scalar m φ Y ⟶
      (scalar m φ X).prod (scalar m φ Y) ⋙ targetFunctor m B c :=
  Functor.whiskerLeft ((𝟭 _).prod (constantPullback (A := A) f) ⋙ tensor m A X)
      (supportComparisonNat m φ c) ≫
    Functor.whiskerRight (inputComparisonNat m choices φ f) (support B c)

private theorem comparison_naturality {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Naturality m choices φ c := by
  intro K K' L L' a b
  refine ⟨?_, ?_, ?_⟩
  · exact (sourceComparisonNat m choices φ c).naturality (Prod.mkHom a b)
  · simpa only [targetComparisonNat, inputComparisonNat, supportComparisonNat,
      targetComparison, supportComparison_eq, inputComparison, Iso.trans_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.prod, NatTrans.id_app, Functor.mapIso_hom, Iso.prod_hom,
      Iso.refl_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Category.assoc,
      Functor.comp_obj, Functor.prod_obj, Functor.id_obj, input, Functor.comp_map,
      Functor.prod_map] using
      (targetComparisonNat m choices φ c).naturality (Prod.mkHom a b)
  · let p := PurCompactSupport.projectionMap (coefficients A) c
      (tensorModel m A X) (tensorModel m A c.Z) (tensorModel m A Y)
      (proEtaleConstantRingCompositeCoefficients_eq c.i c.g A).symm
    let q := Functor.uncurry.map p
    have h := q.naturality (Prod.mkHom a b)
    dsimp only [q, p, Functor.uncurry, Functor.curry, Functor.curryObj,
      PurCompactSupport.tensorCurried, Functor.comp_map, Functor.comp_obj,
      Functor.postcompose₂, Functor.whiskeringLeft₂, Functor.whiskeringLeft,
      Functor.whiskeringRight, tensorModel, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.id_map, Functor.id_obj] at h
    dsimp only [PurCompactSupport.image, Functor.comp_map, PurCompactSupport.pull,
      coefficients, tensorModel] at h
    with_unfolding_all simpa only [sourceFunctor, targetFunctor, projection, tensorModel,
      support, PurCompactSupport.image,
      PurCompactSupport.pull, coefficients, Functor.comp_map, Functor.prod_map,
      Functor.id_map, ← Functor.map_comp, ← Category.assoc,
      CategoryTheory.prod_comp, Category.comp_id, Category.id_comp] using h



private theorem source_composition_of
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : proEtaleDerivedCategory X A)
    (L : proEtaleDerivedCategory Y A)
    (ht : (scalar m ψ Y).map
        ((choices.scalarTensor φ Y).iso.hom.app ((support A c).obj K, L)) ≫
      (choices.scalarTensor ψ Y).iso.hom.app
        ((scalar m φ Y).obj ((support A c).obj K), (scalar m φ Y).obj L) ≫
      (tensor m C Y).map (Prod.mkHom
        ((scalarComp m φ ψ Y).hom.app ((support A c).obj K))
        ((scalarComp m φ ψ Y).hom.app L)) =
      (scalarComp m φ ψ Y).hom.app (source m A c K L) ≫
        (choices.scalarTensor (ψ.comp φ) Y).iso.hom.app ((support A c).obj K, L))
    (hc : (scalar m ψ Y).map (supportComparison m φ c K) ≫
      supportComparison m ψ c ((scalar m φ X).obj K) ≫
      (support C c).map ((scalarComp m φ ψ X).hom.app K) =
      (scalarComp m φ ψ Y).hom.app ((support A c).obj K) ≫
        supportComparison m (ψ.comp φ) c K) :
    (scalar m ψ Y).map (sourceComparison m choices φ c K L) ≫
      sourceComparison m choices ψ c ((scalar m φ X).obj K) ((scalar m φ Y).obj L) ≫
      (sourceFunctor m C c).map (Prod.mkHom ((scalarComp m φ ψ X).hom.app K)
        ((scalarComp m φ ψ Y).hom.app L)) =
    (scalarComp m φ ψ Y).hom.app (source m A c K L) ≫
      sourceComparison m choices (ψ.comp φ) c K L := by
  have hn := (choices.scalarTensor ψ Y).iso.hom.naturality
    (Prod.mkHom (supportComparison m φ c K) (𝟙 ((scalar m φ Y).obj L)))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj] at hn
  simp only [sourceComparison, sourceFunctor, Functor.map_comp,
    Functor.comp_map, Functor.prod_map, Functor.id_map, Category.assoc]
  rw [reassoc_of% hn]
  simp only [Functor.map_id, ← Functor.map_comp, CategoryTheory.prod_comp,
    Category.id_comp, Category.comp_id, Category.assoc]
  rw [hc]
  erw [(scalar m ψ Y).map_id]
  simp only [Category.id_comp]
  have hpair : Prod.mkHom
      ((scalarComp m φ ψ Y).hom.app ((support A c).obj K) ≫
        supportComparison m (ψ.comp φ) c K) ((scalarComp m φ ψ Y).hom.app L) =
      Prod.mkHom ((scalarComp m φ ψ Y).hom.app ((support A c).obj K))
        ((scalarComp m φ ψ Y).hom.app L) ≫
      Prod.mkHom (supportComparison m (ψ.comp φ) c K) (𝟙 _) := by simp
  rw [hpair, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% ht]

private theorem target_composition_of
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : proEtaleDerivedCategory X A)
    (L : proEtaleDerivedCategory Y A)
    (hi : (scalar m ψ X).map (inputComparison m choices φ f K L).hom ≫
      (inputComparison m choices ψ f ((scalar m φ X).obj K)
        ((scalar m φ Y).obj L)).hom ≫
      (tensor m C X).map (Prod.mkHom ((scalarComp m φ ψ X).hom.app K)
        ((constantPullback (A := C) f).map ((scalarComp m φ ψ Y).hom.app L))) =
      (scalarComp m φ ψ X).hom.app (input m A f K L) ≫
        (inputComparison m choices (ψ.comp φ) f K L).hom)
    (hc : (scalar m ψ Y).map (supportComparison m φ c (input m A f K L)) ≫
      supportComparison m ψ c ((scalar m φ X).obj (input m A f K L)) ≫
      (support C c).map ((scalarComp m φ ψ X).hom.app (input m A f K L)) =
      (scalarComp m φ ψ Y).hom.app (target m A c K L) ≫
        supportComparison m (ψ.comp φ) c (input m A f K L)) :
    (scalar m ψ Y).map (targetComparison m choices φ c K L) ≫
      targetComparison m choices ψ c ((scalar m φ X).obj K) ((scalar m φ Y).obj L) ≫
      (targetFunctor m C c).map (Prod.mkHom ((scalarComp m φ ψ X).hom.app K)
        ((scalarComp m φ ψ Y).hom.app L)) =
    (scalarComp m φ ψ Y).hom.app (target m A c K L) ≫
      targetComparison m choices (ψ.comp φ) c K L := by
  have hn := (supportComparisonNat m ψ c).naturality
    (inputComparison m choices φ f K L).hom
  change (scalar m ψ Y).map ((support B c).map
      (inputComparison m choices φ f K L).hom) ≫
      supportComparison m ψ c (input m B f ((scalar m φ X).obj K)
        ((scalar m φ Y).obj L)) =
    supportComparison m ψ c ((scalar m φ X).obj (input m A f K L)) ≫
      (support C c).map ((scalar m ψ X).map
        (inputComparison m choices φ f K L).hom) at hn
  simp only [targetComparison, targetFunctor, Functor.map_comp,
    Functor.comp_map, Functor.prod_map, Functor.id_map, Category.assoc]
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp, Category.assoc]
  rw [hi]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hc]

private theorem source_identity_of
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : proEtaleDerivedCategory X A)
    (L : proEtaleDerivedCategory Y A)
    (ht : (choices.scalarTensor (RingHom.id A) Y).iso.hom.app ((support A c).obj K, L) ≫
      (tensor m A Y).map (Prod.mkHom ((scalarId m A Y).hom.app ((support A c).obj K))
        ((scalarId m A Y).hom.app L)) =
      (scalarId m A Y).hom.app (source m A c K L))
    (hc : supportComparison m (RingHom.id A) c K ≫
      (support A c).map ((scalarId m A X).hom.app K) =
      (scalarId m A Y).hom.app ((support A c).obj K)) :
    sourceComparison m choices (RingHom.id A) c K L ≫
      (sourceFunctor m A c).map (Prod.mkHom ((scalarId m A X).hom.app K)
        ((scalarId m A Y).hom.app L)) =
      (scalarId m A Y).hom.app (source m A c K L) := by
  simpa only [sourceComparison, sourceFunctor, Functor.comp_map, Functor.prod_map,
    Functor.id_map, ← Functor.map_comp, CategoryTheory.prod_comp,
    Category.assoc, Category.id_comp, hc] using ht

private theorem target_identity_of
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : proEtaleDerivedCategory X A)
    (L : proEtaleDerivedCategory Y A)
    (hi : (inputComparison m choices (RingHom.id A) f K L).hom ≫
      (tensor m A X).map (Prod.mkHom ((scalarId m A X).hom.app K)
        ((constantPullback (A := A) f).map ((scalarId m A Y).hom.app L))) =
      (scalarId m A X).hom.app (input m A f K L))
    (hc : supportComparison m (RingHom.id A) c (input m A f K L) ≫
      (support A c).map ((scalarId m A X).hom.app (input m A f K L)) =
      (scalarId m A Y).hom.app (target m A c K L)) :
    targetComparison m choices (RingHom.id A) c K L ≫
      (targetFunctor m A c).map (Prod.mkHom ((scalarId m A X).hom.app K)
        ((scalarId m A Y).hom.app L)) =
      (scalarId m A Y).hom.app (target m A c K L) := by
  simpa only [targetComparison, targetFunctor, Functor.comp_map, Functor.prod_map,
    Functor.id_map, Category.assoc, ← Functor.map_comp, hi] using hc

private theorem support_factorization
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) :
    supportComparison m φ c K =
      (properScalar m φ c.g).app ((openImage A c.i).obj K) ≫
        (properImage B c.g).map ((openScalar m φ c.i).app K) := by
  simp only [supportComparison_eq, properScalar, openScalar, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp,
    PurCompactSupport.comparison_factorization, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc,
    Functor.map_id, Category.id_comp]
  simp only [support, PurCompactSupport.image, properImage, openImage, Functor.comp_map]
  rfl

private theorem projection_factorization
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : proEtaleDerivedCategory X A)
    (L : proEtaleDerivedCategory Y A) :
    projection m A c K L =
      properProjection m A c.g ((openImage A c.i).obj K) L ≫
        (properImage A c.g).map (openFactor m A c K L).hom := by
  let data := (PurCompactSupport.projectionComparisons_existsUnique (coefficients A) c
    (tensorModel m A X) (tensorModel m A c.Z) (tensorModel m A Y)
    (proEtaleConstantRingCompositeCoefficients_eq c.i c.g A).symm).exists.choose
  change _ ≫ (properImage A c.g).map ((data.openProjection.hom.app K).app L) = _
  rw [data.openProjection_eq]
  change (proEtaleRingDerivedAdjunction c.g (proEtaleConstantRing Y A)
      (proEtaleConstantRing c.Z A) (proEtaleConstantRingComparison c.g A)).homEquiv _ _
      ((data.tensorPullback.hom.app ((support A c).obj K)).app L ≫ _) ≫ _ = _
  rw [data.tensorPullback_eq]
  rfl

private theorem proper_projection_naturality
    (A : Type u) [CommRing A] {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    {M M' : proEtaleDerivedCategory Z A} (v : M ⟶ M')
    (L : proEtaleDerivedCategory Y A) :
    (tensor m A Y).map (Prod.mkHom ((properImage A g).map v) (𝟙 L)) ≫
      properProjection m A g M' L =
    properProjection m A g M L ≫
      (properImage A g).map ((tensor m A Z).map (Prod.mkHom v (𝟙 _))) := by
  have h := tensor_projection_naturality
    (proEtaleRingDerivedAdjunction g (proEtaleConstantRing Y A)
      (proEtaleConstantRing Z A) (proEtaleConstantRingComparison g A))
    (tensor m A Y) (tensor m A Z) (restrictionTensor m A g).hom v (𝟙 L)
  with_unfolding_all simpa only [CategoryTheory.Functor.map_id, Functor.id_obj,
    properProjection, properImage,
    PurCompactSupport.push, coefficients, input] using h


private theorem paste_factor_squares
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (G : C ⥤ D) (R : A ⥤ C) (S : B ⥤ D)
    {a₀ a₁ : A} {b : B} {c₀ c₁ c₂ : C} {d₀ d₁ d₂ : D}
    (pA : b ⟶ F.obj a₀) (gA : a₀ ⟶ a₁)
    (χ₀ : S.obj (F.obj a₀) ⟶ G.obj (R.obj a₀))
    (χ₁ : S.obj (F.obj a₁) ⟶ G.obj (R.obj a₁))
    (t : S.obj b ⟶ d₀) (q : d₀ ⟶ d₁) (v : d₁ ⟶ d₂)
    (pB : d₁ ⟶ G.obj c₀) (pB' : d₂ ⟶ G.obj c₁)
    (i₀ : R.obj a₀ ⟶ c₀) (i₁ : R.obj a₁ ⟶ c₂)
    (u : c₀ ⟶ c₁) (gB : c₁ ⟶ c₂)
    (hn : S.map (F.map gA) ≫ χ₁ = χ₀ ≫ G.map (R.map gA))
    (hp : S.map pA ≫ χ₀ ≫ G.map i₀ = t ≫ q ≫ pB)
    (ho : R.map gA ≫ i₁ = i₀ ≫ u ≫ gB)
    (hb : v ≫ pB' = pB ≫ G.map u) :
    S.map (pA ≫ F.map gA) ≫ χ₁ ≫ G.map i₁ =
      t ≫ q ≫ v ≫ pB' ≫ G.map gB := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← G.map_comp, ho]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hp, ← reassoc_of% hb]

private theorem projection_scalar_square
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) (L : proEtaleDerivedCategory Y A) :
    (scalar m φ Y).map (projection m A c K L) ≫
        targetComparison m choices φ c K L =
      sourceComparison m choices φ c K L ≫
        projection m B c ((scalar m φ X).obj K) ((scalar m φ Y).obj L) := by
  have h := paste_factor_squares
    (properImage A c.g) (properImage B c.g) (scalar m φ c.Z) (scalar m φ Y)
    (properProjection m A c.g ((openImage A c.i).obj K) L)
    (openFactor m A c K L).hom
    ((properScalar m φ c.g).app (input m A c.g ((openImage A c.i).obj K) L))
    ((properScalar m φ c.g).app ((openImage A c.i).obj (input m A f K L)))
    ((choices.scalarTensor φ Y).iso.hom.app ((support A c).obj K, L))
    ((tensor m B Y).map (Prod.mkHom
      ((properScalar m φ c.g).app ((openImage A c.i).obj K)) (𝟙 _)))
    ((tensor m B Y).map (Prod.mkHom
      ((properImage B c.g).map ((openScalar m φ c.i).app K)) (𝟙 _)))
    (properProjection m B c.g ((scalar m φ c.Z).obj ((openImage A c.i).obj K))
      ((scalar m φ Y).obj L))
    (properProjection m B c.g ((openImage B c.i).obj ((scalar m φ X).obj K))
      ((scalar m φ Y).obj L))
    (inputComparison m choices φ c.g ((openImage A c.i).obj K) L).hom
    ((openScalar m φ c.i).app (input m A f K L) ≫
      (openImage B c.i).map (inputComparison m choices φ f K L).hom)
    ((tensor m B c.Z).map (Prod.mkHom ((openScalar m φ c.i).app K) (𝟙 _)))
    (openFactor m B c ((scalar m φ X).obj K) ((scalar m φ Y).obj L)).hom
    ((properScalar m φ c.g).naturality (openFactor m A c K L).hom)
    (proper_scalar_tensor_square m choices φ c.g ((openImage A c.i).obj K) L)
    (open_scalar_tensor_square m choices φ c K L)
    (proper_projection_naturality m B c.g ((openScalar m φ c.i).app K)
      ((scalar m φ Y).obj L))
  simp only [← Functor.map_comp, ← Functor.map_comp_assoc, CategoryTheory.prod_comp,
    Category.id_comp,
    Category.comp_id] at h
  with_unfolding_all
    simpa only [projection_factorization, targetComparison, sourceComparison,
      support_factorization, support, PurCompactSupport.image, Functor.comp_map,
      ← Functor.map_comp, ← Functor.map_comp_assoc, Category.assoc,
      CategoryTheory.prod_comp, Category.comp_id,
      Category.id_comp] using h

/-- Concrete finite-reduction projection square, natural in both inputs, with the
identity and successive-reduction cocycle. The schemes' structure maps need not
be separated, and the operation datum assumes no projection invertibility.

Source: current blueprint, fix-prop-projection-formula, proof sentence 2;
Stacks 0GL6, 0GL1, 0E48, 07A4 and 0D6D
(blueprint: lem-sf-concrete-projection-reduction-square).

Proof plan:
1. lem-sf-pullback-tor-amplitude preserves the interval [c,d]. Clause (ii) of
   lem-sf-tensor-ctf gives bounded constructibility and interval [a+c,b+d] for H.
   Thus lem-fix-compact-support-coefficient-change applies to both K and H.
2. Form u by tensor comparison then c_K, and v by c_H then the tensor/pullback
   comparison. Their invertibility follows from step 1 and the canonical K-flat
   tensor/pullback comparisons, without assuming coefficient flatness.
3. Specialize lem-weil-pbc-ringed-exchange-tensor-coherence to the coefficient
   square for the proper factor. lem-fix-proetale-scalar-mate-normalization
   identifies its exchange with the counit-defined scalar mate chi.
4. lem-fix-open-scalar-tensor-normalization gives the forward open tensor square.
   The scalar/pullback composition normalization identifies its geometric factor.
   The canonical compact-support comparison is Rp_*(beta) chi: transpose under
   the scalar adjunction and use lem-sf-compact-support-restriction-of-scalars
   and def-coef-compact-support-tensor-comparison to identify the scalar units.
5. Expand v rho(PF), use naturality of chi at gamma, then substitute the open
   square and the proper square. Naturality of the proper projection at beta_K
   yields PF_B u, with exactly the ordered proper-counit/open-tensor composite.
6. All factors are natural. The proper cocycle is
   lem-pur-ringed-coefficient-projection-cocycle, the open cocycle is the open
   normalization, and balanced associativity is
   lem-sfb-successive-derived-quotient-normalization. On flat K-flat tensors,
   successive and direct tensor/pullback comparisons send each pure tensor to
   the same tensor, with identical total-complex signs. This proves both endpoint
   cocycles and identity unitors, hence pasting gives the direct square. The
   compactification was arbitrary throughout; no projection map is inverted. -/
theorem concreteProjectionReductionSquare
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (hn : 1 ≤ n) (_operations : SixFunctorOperationDatum D C E n hn) :
    ∀ (m₀ : Models.{u}) (choices₀ : Choices m₀)
      (X Y : Over (Spec (CommRingCat.of D.k)))
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
      (cpt : Compactification f.left)
      (K : proEtaleDerivedCategory X.left (Padic.coefficientExtensionRing C.l E n))
      (L : proEtaleDerivedCategory Y.left (Padic.coefficientExtensionRing C.l E n)),
      finiteTorConstructible C.l E n hn X.left K →
      finiteTorConstructible C.l E n hn Y.left L →
      (∀ a b c d : ℤ,
        HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing C.l E n) K a b →
        HasProEtaleTorAmplitude Y.left (Padic.coefficientExtensionRing C.l E n) L c d →
        finiteTorConstructible C.l E n hn X.left
          (input m₀ (Padic.coefficientExtensionRing C.l E n) f.left K L) ∧
        HasProEtaleTorAmplitude X.left (Padic.coefficientExtensionRing C.l E n)
          (input m₀ (Padic.coefficientExtensionRing C.l E n) f.left K L) (a + c) (b + d)) ∧
      (∀ (m : ℕ) (_hm : 1 ≤ m) (hmn : m ≤ n),
        Square m₀ choices₀ (quotient C.l E hmn) cpt K L ∧
        Naturality m₀ choices₀ (quotient C.l E hmn) cpt ∧
        ∀ (r : ℕ) (_hr : 1 ≤ r) (hrm : r ≤ m),
          Composition m₀ choices₀ (quotient C.l E hmn) (quotient C.l E hrm) cpt K L) ∧
      Identity m₀ choices₀ (Padic.coefficientExtensionRing C.l E n) cpt K L := by
  intro m₀ choices₀ X Y hXft hXqc hYft hYqc f hfsep hfft hfqc cpt K L hK hL
  letI : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  letI : Y.left.Over (Spec (.of D.k)) := ⟨Y.hom⟩
  haveI : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := hXft
  haveI : QuasiCompact (X.left ↘ Spec (.of D.k)) := hXqc
  haveI : LocallyOfFiniteType (Y.left ↘ Spec (.of D.k)) := hYft
  haveI : QuasiCompact (Y.left ↘ Spec (.of D.k)) := hYqc
  haveI : Finite (Padic.coefficientExtensionRing C.l E n) :=
    Padic.finite_coefficientExtensionRing C.l E n hn
  have hinput : finiteTorConstructible C.l E n hn X.left
      (input m₀ (Padic.coefficientExtensionRing C.l E n) f.left K L) := by
    obtain ⟨a, b, hKa⟩ := hK.2
    obtain ⟨c, d, hLc⟩ := hL.2
    have hPL := sf_pullback_torAmplitude D C.l C.different E n hn X Y f L hL.1 c d hLc
    have hPL' := sf_pullback_finiteTorConstructible D C.l C.different E n hn X Y f L hL
    exact (tensor_tor m₀ D C E n hn X.left K _ hK hPL' a b c d hKa hPL.2).1
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d hKa hLc
    have hPL := sf_pullback_torAmplitude D C.l C.different E n hn X Y f L hL.1 c d hLc
    have hPL' := sf_pullback_finiteTorConstructible D C.l C.different E n hn X Y f L hL
    exact tensor_tor m₀ D C E n hn X.left K _ hK hPL' a b c d hKa hPL.2
  · intro k hk hkn
    refine ⟨?_, comparison_naturality m₀ choices₀ (quotient C.l E hkn) cpt, ?_⟩
    · haveI : Finite (Padic.coefficientExtensionRing C.l E k) :=
        Padic.finite_coefficientExtensionRing C.l E k hk
      haveI := supportComparison_quotient_isIso m₀ D C E n hn k hk hkn X Y f cpt K hK
      haveI := supportComparison_quotient_isIso m₀ D C E n hn k hk hkn X Y f cpt
        (input m₀ (Padic.coefficientExtensionRing C.l E n) f.left K L) hinput
      refine ⟨?_, ?_, projection_scalar_square m₀ choices₀ (quotient C.l E hkn) cpt K L⟩
      · unfold sourceComparison
        haveI : IsIso (Prod.mkHom
            (supportComparison m₀ (quotient C.l E hkn) cpt K)
            (𝟙 ((scalar m₀ (quotient C.l E hkn) Y.left).obj L))) := by
          exact inferInstanceAs (IsIso ((asIso
            (supportComparison m₀ (quotient C.l E hkn) cpt K)).prod
              (Iso.refl ((scalar m₀ (quotient C.l E hkn) Y.left).obj L))).hom)
        infer_instance
      · unfold targetComparison
        infer_instance
    · intro r hr hrk
      haveI : Finite (Padic.coefficientExtensionRing C.l E k) :=
        Padic.finite_coefficientExtensionRing C.l E k hk
      haveI : Finite (Padic.coefficientExtensionRing C.l E r) :=
        Padic.finite_coefficientExtensionRing C.l E r hr
      exact ⟨source_composition_of m₀ choices₀ _ _ cpt K L
          (tensor_comp m₀ choices₀ _ _ Y.left _ L) (support_comp m₀ _ _ cpt K),
        target_composition_of m₀ choices₀ _ _ cpt K L
          (input_comp m₀ choices₀ _ _ f.left K L) (support_comp m₀ _ _ cpt _)⟩
  · exact ⟨source_identity_of m₀ choices₀ _ cpt K L
        (tensor_id m₀ choices₀ _ Y.left _ L) (support_id m₀ _ cpt K),
      target_identity_of m₀ choices₀ _ cpt K L
        (input_id m₀ choices₀ _ f.left K L) (support_id m₀ _ cpt _)⟩

end WeilConjectures.ConcreteProjectionReduction
