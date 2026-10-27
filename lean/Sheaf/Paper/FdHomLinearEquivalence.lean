/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.PbcQbarCategory
public import Sheaf.Paper.IntrinsicQbarCategory
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Paper.FiniteStagePairCategory
import Sheaf.NumberTheory.Padics.FiniteCoefficientFields

/-! # Hom transport and linear equivalence of literal coefficient pair categories

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence, extracted common-stage argument
(blueprint: lem-fd-hom-linear-equivalence).

The scalar comparison j is the inverse of the published stage morphism's beta.
All representatives, transport maps and inclusions are those of the two existing
coefficient systems. The target is the PBC system reexported by IntrinsicQbarCategory.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.StageSystem.Morphism.functor
set_option allowUnsafeReducibility true in
attribute [local irreducible] CategoryTheory.ScalarLocalization.category
  CategoryTheory.ScalarLocalization.preadditive

open CategoryTheory

private noncomputable def stageHomEquiv
    {I : Type*} [Preorder I] {C D : I → Type*}
    [∀ i, Category (C i)] [∀ i, Category (D i)]
    {S : StageSystem C} {R : StageSystem D} (F : S.Morphism R)
    [∀ i, (F.Φ i).Full] [∀ i, (F.Φ i).Faithful]
    {i j n : I} (hi : i ≤ n) (hj : j ≤ n) (x : C i) (y : C j) :
    ((S.T hi).obj x ⟶ (S.T hj).obj y) ≃
      ((R.T hi).obj ((F.Φ i).obj x) ⟶ (R.T hj).obj ((F.Φ j).obj y)) where
  toFun := F.mapAt
  invFun v := (F.Φ n).preimage ((F.β hi).inv.app x ≫ v ≫ (F.β hj).hom.app y)
  left_inv u := by
    apply (F.Φ n).map_injective
    simp [StageSystem.Morphism.mapAt]
  right_inv v := by simp [StageSystem.Morphism.mapAt]

private noncomputable def stageAddEquiv
    {I : Type*} [Preorder I] {C D : I → Type*}
    [∀ i, Category (C i)] [∀ i, Category (D i)]
    [∀ i, Preadditive (C i)] [∀ i, Preadditive (D i)]
    {S : StageSystem C} {R : StageSystem D} (F : S.Morphism R)
    [∀ i, (F.Φ i).Full] [∀ i, (F.Φ i).Faithful] [∀ i, (F.Φ i).Additive]
    {i j n : I} (hi : i ≤ n) (hj : j ≤ n) (x : C i) (y : C j) :
    ((S.T hi).obj x ⟶ (S.T hj).obj y) ≃+
      ((R.T hi).obj ((F.Φ i).obj x) ⟶ (R.T hj).obj ((F.Φ j).obj y)) := {
  stageHomEquiv F hi hj x y with
  map_add' := fun f g ↦ by
    simp [stageHomEquiv, StageSystem.Morphism.mapAt, Functor.map_add,
      Preadditive.comp_add, Preadditive.add_comp] }

private theorem pairFullyFaithful
    {I : Type*} [Preorder I] [IsDirectedOrder I] {C D : I → Type*}
    [∀ i, Category (C i)] [∀ i, Category (D i)]
    {S : StageSystem C} {R : StageSystem D} (F : S.Morphism R)
    [∀ i, (F.Φ i).Full] [∀ i, (F.Φ i).Faithful] :
    F.functor.Full ∧ F.functor.Faithful := by
  open StageSystem.PairCategory in
  constructor
  · constructor
    intro X Y f
    induction f using hom_induction with
    | h n hX hY v =>
      refine ⟨mkHom n hX hY ((stageHomEquiv F hX hY X.obj Y.obj).symm v), ?_⟩
      change mkHom n hX hY (F.mapAt _) = _
      exact congrArg (mkHom n hX hY) ((stageHomEquiv F hX hY X.obj Y.obj).apply_symm_apply v)
  · constructor
    intro X Y f g e
    induction f using hom_induction with
    | h n hX hY u =>
      induction g using hom_induction with
      | h m hX' hY' v =>
        rw [F.functor_map_mkHom, F.functor_map_mkHom] at e
        obtain ⟨p, hn, hm, ep⟩ := (mkHom_eq_mkHom_iff' _ _).mp e
        apply (mkHom_eq_mkHom_iff' _ _).mpr
        refine ⟨p, hn, hm, ?_⟩
        erw [F.tr_mapAt, F.tr_mapAt] at ep
        exact (stageHomEquiv F (hX.trans hn) (hY.trans hn) X.obj Y.obj).injective ep

private noncomputable def equivalenceWithPreimages
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) [F.Full] [F.Faithful]
    (K : D → C) (ε : ∀ A, F.obj (K A) ≅ A) : C ≌ D := by
  let G : D ⥤ C := {
    obj := K
    map := fun {A B} f ↦ F.preimage ((ε A).hom ≫ f ≫ (ε B).inv)
    map_id := fun A ↦ F.map_injective (by simp)
    map_comp := fun f g ↦ F.map_injective (by simp) }
  let η : 𝟭 C ≅ F ⋙ G := NatIso.ofComponents
    (fun X ↦ (F.preimageIso (ε (F.obj X))).symm)
    (fun f ↦ F.map_injective (by simp [G]))
  let ε' : G ⋙ F ≅ 𝟭 D := NatIso.ofComponents ε (by simp [G])
  exact {
    functor := F
    inverse := G
    unitIso := η
    counitIso := ε'
    functor_unitIso_comp := fun X ↦ by simp [η, ε'] }

private theorem mapScalarHom
    (l : ℕ) [Fact l.Prime] (Ω : Type*) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω]
    {C D : Padic.FiniteCoefficientFields l Ω → Type*}
    [∀ E, Category (C E)] [∀ E, Category (D E)]
    [∀ E, Preadditive (C E)] [∀ E, Preadditive (D E)]
    [∀ E, Linear E.val (C E)] [∀ E, Linear E.val (D E)]
    {S : StageSystem C} {R : StageSystem D} (F : S.Morphism R)
    [∀ E, (F.Φ E).Linear E.val]
    (hS : StageSystem.QbarScalarCompatible l Ω S)
    (hR : StageSystem.QbarScalarCompatible l Ω R)
    {X Y : S.PairCategory} (a : Ω) (f : X ⟶ Y) :
    F.functor.map (StageSystem.qbarScalarHom l Ω S hS a f) =
      StageSystem.qbarScalarHom l Ω R hR a (F.functor.map f) := by
  open StageSystem StageSystem.PairCategory in
  induction f using hom_induction with
  | h M hX hY u =>
    let N := Padic.finiteCoefficientCompositum l Ω M (qbarScalarField l Ω a)
    let h : M ≤ N := ((Padic.finiteCoefficientFields_properties l Ω).1 _ _).1
    let ha : a ∈ N.val := ((Padic.finiteCoefficientFields_properties l Ω).1 _ _).2
      (qbarScalarField_mem l Ω a)
    change mkHom (X := F.functor.obj X) (Y := F.functor.obj Y)
      N (hX.trans h) (hY.trans h)
      (F.mapAt ((⟨a, ha⟩ : N.val) • S.tr h u)) =
      mkHom (X := F.functor.obj X) (Y := F.functor.obj Y)
        N (hX.trans h) (hY.trans h) ((⟨a, ha⟩ : N.val) • R.tr h (F.mapAt u))
    apply congrArg (mkHom (X := F.functor.obj X) (Y := F.functor.obj Y)
      N (hX.trans h) (hY.trans h))
    rw [F.tr_mapAt]
    simp [Morphism.mapAt, Functor.map_smul, Linear.comp_smul, Linear.smul_comp]

private noncomputable def homLinearEquiv
    (R : Type*) [Semiring R] {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive] [F.Linear R] (X Y : C) :
    (X ⟶ Y) ≃ₗ[R] (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  invFun := F.preimage
  left_inv := F.preimage_map
  right_inv := F.map_preimage
  map_add' := fun _ _ ↦ F.map_add
  map_smul' := fun a f ↦ F.map_smul a f

private theorem linearEquivalenceWithPreimages
    (R : Type*) [Semiring R] {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive] [F.Linear R]
    (K : D → C) (ε : ∀ A, F.obj (K A) ≅ A) :
    ∃ e : C ≌ D, e.functor = F ∧ e.functor.Additive ∧ e.functor.Linear R ∧
      e.inverse.Additive ∧ e.inverse.Linear R ∧ (∀ A, e.inverse.obj A = K A) ∧
      (∀ A B (f : A ⟶ B), HEq (e.inverse.map f)
        ((homLinearEquiv R F (K A) (K B)).symm ((ε A).hom ≫ f ≫ (ε B).inv))) ∧
      (∀ A, HEq (e.counitIso.hom.app A) (ε A).hom) := by
  let e := equivalenceWithPreimages F K ε
  have he : e.functor = F := rfl
  let : e.functor.Additive := by simpa [he] using (inferInstance : F.Additive)
  let : e.functor.Linear R := by simpa [he] using (inferInstance : F.Linear R)
  exact ⟨e, he, inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ ↦ rfl, fun _ _ _ ↦ HEq.rfl, fun _ ↦ HEq.rfl⟩

private theorem equivalenceAdditive
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [CategoryTheory.Limits.HasBinaryProducts C] (F : C ⥤ D) [F.IsEquivalence] :
    F.Additive := Functor.additive_of_preserves_binary_products F

private theorem pretriangulatedBinaryProducts
    (C : Type*) [Category C] [Preadditive C] [Limits.HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] :
    Limits.HasBinaryProducts C := by
  let : Limits.HasBinaryBiproducts C := Pretriangulated.instHasBinaryBiproducts
  exact Limits.hasBinaryProducts_of_hasBinaryBiproducts

private theorem pairHomLinearEquivalence
    (l : ℕ) [Fact l.Prime] (Ω : Type*) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω]
    {C D : Padic.FiniteCoefficientFields l Ω → Type*}
    [∀ E, Category (C E)] [∀ E, Category (D E)]
    [∀ E, Preadditive (C E)] [∀ E, Preadditive (D E)]
    [∀ E, Linear E.val (C E)] [∀ E, Linear E.val (D E)]
    {S : StageSystem C} {P : StageSystem D}
    [Preadditive S.PairCategory] [Preadditive P.PairCategory]
    [Linear Ω S.PairCategory] [Linear Ω P.PairCategory]
    [CategoryTheory.Limits.HasBinaryProducts S.PairCategory]
    (J : S.Morphism P) [∀ E, (J.Φ E).IsEquivalence]
    (_hadd : ∀ E, (J.Φ E).Additive) (_hlinear : ∀ E, (J.Φ E).Linear E.val)
    (hS : StageSystem.QbarScalarCompatible l Ω S)
    (hP : StageSystem.QbarScalarCompatible l Ω P)
    (hsmulS : ∀ (A B : S.PairCategory) (a : Ω) (f : A ⟶ B),
      a • f = StageSystem.qbarScalarHom l Ω S hS a f)
    (hsmulP : ∀ (A B : P.PairCategory) (a : Ω) (f : A ⟶ B),
      a • f = StageSystem.qbarScalarHom l Ω P hP a f) :
  ∃ (stage : ∀ (A B : S.PairCategory)
    (M : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M),
    (A.toStage hA ⟶ B.toStage hB) ≃+
      ((J.functor.obj A).toStage hA ⟶ (J.functor.obj B).toStage hB)),
  (∀ (A B : S.PairCategory)
    (M : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M)
    (f : A.toStage hA ⟶ B.toStage hB),
    stage A B M hA hB f = J.mapAt f) ∧
  (∀ (A B : S.PairCategory)
    (M : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M)
    (v : (J.functor.obj A).toStage hA ⟶ (J.functor.obj B).toStage hB),
    (stage A B M hA hB).symm v =
      (J.Φ M).preimage (X := A.toStage hA) (Y := B.toStage hB)
        ((J.β hA).inv.app A.obj ≫ v ≫ (J.β hB).hom.app B.obj)) ∧
  (∀ (A B : S.PairCategory)
    (M N : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M)
    (h : M ≤ N)
    (f : A.toStage hA ⟶ B.toStage hB),
    stage A B N (hA.trans h) (hB.trans h)
        (S.tr h f) =
      P.tr h (stage A B M hA hB f)) ∧
  (∀ (A B : S.PairCategory)
    (M N : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M)
    (h : M ≤ N)
    (v : (J.functor.obj A).toStage hA ⟶ (J.functor.obj B).toStage hB),
    (stage A B N (hA.trans h) (hB.trans h)).symm
        (P.tr h v) =
      S.tr h
        ((stage A B M hA hB).symm v)) ∧
  ∃ (hom : ∀ A B : S.PairCategory,
    (A ⟶ B) ≃ₗ[Ω] (J.functor.obj A ⟶ J.functor.obj B)),
  (∀ A B (f : A ⟶ B), hom A B f = J.functor.map f) ∧
  (∀ (A B : S.PairCategory)
    (M : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M)
    (f : A.toStage hA ⟶ B.toStage hB),
    hom A B (StageSystem.PairCategory.mkHom (X := A) (Y := B) M hA hB f) =
      StageSystem.PairCategory.mkHom (X := J.functor.obj A) (Y := J.functor.obj B)
        M hA hB (stage A B M hA hB f)) ∧
  (∀ (A B : S.PairCategory)
    (M : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M)
    (v : (J.functor.obj A).toStage hA ⟶ (J.functor.obj B).toStage hB),
    (hom A B).symm (StageSystem.PairCategory.mkHom
        (X := J.functor.obj A) (Y := J.functor.obj B) M hA hB v) =
      StageSystem.PairCategory.mkHom (X := A) (Y := B)
        M hA hB ((stage A B M hA hB).symm v)) ∧
  (J.functor.Additive) ∧
  (J.functor.Linear Ω) ∧
  (∀ A, J.functor.obj A = ⟨A.stage, (J.Φ A.stage).obj A.obj⟩) ∧
  (∀ E (A : D E),
    ∃ K : C E,
      Nonempty ((J.Φ E).obj K ≅ A)) ∧
  (∀ (K : ∀ A : P.PairCategory,
        C A.stage)
      (ε : ∀ A : P.PairCategory, (J.Φ A.stage).obj (K A) ≅ A.obj),
    ∃ e : S.PairCategory ≌ P.PairCategory,
      e.functor = J.functor ∧ e.functor.Additive ∧ e.functor.Linear Ω ∧
      e.inverse.Additive ∧ e.inverse.Linear Ω ∧
      (∀ A, e.inverse.obj A = ⟨A.stage, K A⟩) ∧
      (∀ A B (f : A ⟶ B), HEq (e.inverse.map f)
        ((hom ⟨A.stage, K A⟩ ⟨B.stage, K B⟩).symm
          ((P.ι A.stage).map (ε A).hom ≫ f ≫
            (P.ι B.stage).map (ε B).inv))) ∧
      (∀ A, HEq (e.counitIso.hom.app A)
        ((P.ι A.stage).map (ε A).hom))) ∧
  (∀ E (K : C E),
    J.functor.obj (S.ι E |>.obj K) =
      (P.ι E).obj ((J.Φ E).obj K)) ∧
  (∀ E (K H : C E)
    (f : K ⟶ H),
    J.functor.map ((S.ι E).map f) =
      (P.ι E).map ((J.Φ E).map f))
 := by
  classical
  let : ∀ E, (J.Φ E).Additive := _hadd
  let : ∀ E, (J.Φ E).Linear E.val := _hlinear
  let stage (A B : S.PairCategory)
      (M : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M) :
      (A.toStage hA ⟶ B.toStage hB) ≃+
        ((J.functor.obj A).toStage hA ⟶ (J.functor.obj B).toStage hB) :=
    stageAddEquiv J hA hB A.obj B.obj
  have ff := pairFullyFaithful J
  let : J.functor.Full := ff.1
  let : J.functor.Faithful := ff.2
  let : J.functor.EssSurj := {
    mem_essImage := fun A ↦ ⟨⟨A.stage, (J.Φ A.stage).objPreimage A.obj⟩,
      ⟨(P.ι A.stage).mapIso ((J.Φ A.stage).objObjPreimageIso A.obj)⟩⟩ }
  let : J.functor.IsEquivalence := {}
  have haddfun : J.functor.Additive := equivalenceAdditive J.functor
  let : J.functor.Additive := haddfun
  have hlinfun : J.functor.Linear Ω := {
    map_smul := fun {A B} f a ↦ by
      rw [hsmulS, hsmulP]
      exact mapScalarHom l Ω J hS
        hP a f }
  let : J.functor.Linear Ω := hlinfun
  let hom (A B : S.PairCategory) :
      (A ⟶ B) ≃ₗ[Ω] (J.functor.obj A ⟶ J.functor.obj B) :=
    homLinearEquiv Ω J.functor A B
  refine ⟨stage, ?_, ?_, ?_, ?_, hom, ?_, ?_, ?_, haddfun,
    hlinfun, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B M hA hB f
    rfl
  · intro A B M hA hB v
    rfl
  · intro A B M N hA hB h f
    exact (J.tr_mapAt h f).symm
  · intro A B M N hA hB h v
    apply (stage A B N (hA.trans h) (hB.trans h)).injective
    change (stage A B N (hA.trans h) (hB.trans h)) _ = J.mapAt _
    rw [AddEquiv.apply_symm_apply]
    exact ((J.tr_mapAt h _).symm.trans
      (congrArg (P.tr h) ((stage A B M hA hB).apply_symm_apply v))).symm
  · intro A B f
    rfl
  · intro A B M hA hB f
    exact J.functor_map_mkHom hA hB f
  · intro A B M hA hB v
    apply (hom A B).injective
    rw [LinearEquiv.apply_symm_apply]
    change StageSystem.PairCategory.mkHom (X := J.functor.obj A)
      (Y := J.functor.obj B) M hA hB v = J.functor.map
        (StageSystem.PairCategory.mkHom M hA hB ((stage A B M hA hB).symm v))
    rw [J.functor_map_mkHom]
    exact congrArg (StageSystem.PairCategory.mkHom (X := J.functor.obj A)
      (Y := J.functor.obj B) M hA hB)
      ((stage A B M hA hB).apply_symm_apply v).symm
  · exact J.functor_obj
  · intro E A
    exact ⟨(J.Φ E).objPreimage A, ⟨(J.Φ E).objObjPreimageIso A⟩⟩
  · intro K ε
    let K' (A : P.PairCategory) :
        S.PairCategory := ⟨A.stage, K A⟩
    let ε' (A : P.PairCategory) : J.functor.obj (K' A) ≅ A :=
      (P.ι A.stage).mapIso (ε A)
    exact linearEquivalenceWithPreimages Ω J.functor K' ε'
  · intro E K
    rfl
  · intro E K H f
    exact J.functor_map_ι f



universe d u w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  (J : StageSystem.Morphism
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out))
  [∀ E, (J.Φ E).IsEquivalence]

/-- The complete conclusion of common-stage Hom transport, packaged without choosing
any new category or quotient. Source: trace-definition final sentence, auxiliary
common-stage argument (blueprint: lem-fd-hom-linear-equivalence).

The stage maps are phi and their inverses are psi. The quotient Hom maps are Phi
and Psi. The quasi-inverse field applies to every choice of finite object preimages,
and specifies both its arrow formula and counit, retaining the target field label. -/
def FdHomLinearEquivalence : Prop :=
  ∃ (stage : ∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω T)
    (M : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M),
    (A.toStage hA ⟶ B.toStage hB) ≃+
      ((J.functor.obj A).toStage hA ⟶ (J.functor.obj B).toStage hB)),
  (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω T)
    (M : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M)
    (f : A.toStage hA ⟶ B.toStage hB),
    stage A B M hA hB f = J.mapAt f) ∧
  (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω T)
    (M : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M)
    (v : (J.functor.obj A).toStage hA ⟶ (J.functor.obj B).toStage hB),
    (stage A B M hA hB).symm v =
      (J.Φ M).preimage (X := A.toStage hA) (Y := B.toStage hB)
        ((J.β hA).inv.app A.obj ≫ v ≫ (J.β hB).hom.app B.obj)) ∧
  (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω T)
    (M N : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M)
    (h : M ≤ N)
    (f : A.toStage hA ⟶ B.toStage hB),
    stage A B N (hA.trans h) (hB.trans h)
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).tr h f) =
      (pbcScalarSystem l Ω T dT.out iT.out).tr h (stage A B M hA hB f)) ∧
  (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω T)
    (M N : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M)
    (h : M ≤ N)
    (v : (J.functor.obj A).toStage hA ⟶ (J.functor.obj B).toStage hB),
    (stage A B N (hA.trans h) (hB.trans h)).symm
        ((pbcScalarSystem l Ω T dT.out iT.out).tr h v) =
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).tr h
        ((stage A B M hA hB).symm v)) ∧
  ∃ (hom : ∀ A B : generalAlgebraicallyClosedConstructibleCategory l Ω T,
    (A ⟶ B) ≃ₗ[Ω] (J.functor.obj A ⟶ J.functor.obj B)),
  (∀ A B (f : A ⟶ B), hom A B f = J.functor.map f) ∧
  (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω T)
    (M : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M)
    (f : A.toStage hA ⟶ B.toStage hB),
    hom A B (StageSystem.PairCategory.mkHom (X := A) (Y := B) M hA hB f) =
      StageSystem.PairCategory.mkHom (X := J.functor.obj A) (Y := J.functor.obj B)
        M hA hB (stage A B M hA hB f)) ∧
  (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω T)
    (M : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M)
    (v : (J.functor.obj A).toStage hA ⟶ (J.functor.obj B).toStage hB),
    (hom A B).symm (StageSystem.PairCategory.mkHom
        (X := J.functor.obj A) (Y := J.functor.obj B) M hA hB v) =
      StageSystem.PairCategory.mkHom (X := A) (Y := B)
        M hA hB ((stage A B M hA hB).symm v)) ∧
  (J.functor.Additive) ∧
  (J.functor.Linear Ω) ∧
  (∀ A, J.functor.obj A = ⟨A.stage, (J.Φ A.stage).obj A.obj⟩) ∧
  (∀ E (A : pbcStageCategory l Ω T E),
    ∃ K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E,
      Nonempty ((J.Φ E).obj K ≅ A)) ∧
  (∀ (K : ∀ A : pbcQbarCategory l Ω T,
        GeneralAlgebraicallyClosedCoefficients.Stage l Ω T A.stage)
      (ε : ∀ A : pbcQbarCategory l Ω T, (J.Φ A.stage).obj (K A) ≅ A.obj),
    ∃ e : generalAlgebraicallyClosedConstructibleCategory l Ω T ≌ pbcQbarCategory l Ω T,
      e.functor = J.functor ∧ e.functor.Additive ∧ e.functor.Linear Ω ∧
      e.inverse.Additive ∧ e.inverse.Linear Ω ∧
      (∀ A, e.inverse.obj A = ⟨A.stage, K A⟩) ∧
      (∀ A B (f : A ⟶ B), HEq (e.inverse.map f)
        ((hom ⟨A.stage, K A⟩ ⟨B.stage, K B⟩).symm
          (((pbcScalarSystem l Ω T dT.out iT.out).ι A.stage).map (ε A).hom ≫ f ≫
            ((pbcScalarSystem l Ω T dT.out iT.out).ι B.stage).map (ε B).inv))) ∧
      (∀ A, HEq (e.counitIso.hom.app A)
        (((pbcScalarSystem l Ω T dT.out iT.out).ι A.stage).map (ε A).hom))) ∧
  (∀ E (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    J.functor.obj ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).ι E |>.obj K) =
      ((pbcScalarSystem l Ω T dT.out iT.out).ι E).obj ((J.Φ E).obj K)) ∧
  (∀ E (K H : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E)
    (f : K ⟶ H),
    J.functor.map (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).ι E).map f) =
      ((pbcScalarSystem l Ω T dT.out iT.out).ι E).map ((J.Φ E).map f))

/-- Exact linear coherent finite comparisons induce the specified Hom equivalences
and linear equivalence of the literal pair categories.
Source: trace-definition final sentence, extracted auxiliary argument, steps 1--11
(blueprint: lem-fd-hom-linear-equivalence).

Proof: 1. Full faithfulness of each J_M gives a Hom bijection; composing with
invertible beta components gives phi, and its inverse is preimage after conjugation.
Additivity and finite-field linearity follow from those of J_M and composition.
2. Expand transport with the actual two associators. The scalar cocycle J.coh at
both endpoints and naturality of beta cancel the middle components and give
phi_N(u_N) = phi_M(u)_N. 3. Apply this to psi_M(v). Injectivity of phi_N gives
the inverse transport equation, without faithfulness of a transition functor.
4. Both maps respect eventual equality and descend to inverse additive quotient
Hom maps with the displayed representative formulas. 5. Common-stage composition
cancels the middle beta, and the unit comparison gives identities. These are the
object and arrow formulas of J.functor. 6. Choose a finite-stage preimage of A_E
under J_E; the inclusion sends its isomorphism to an isomorphism of literal pairs.
7. For any such choices, lift epsilon_A followed by f followed by epsilon_B inverse
through the inverse Hom map. Injectivity proves identity and composition laws.
8. These epsilon classes are a natural counit. Lift their inverses to the unit;
apply the forward Hom bijection to check naturality and both triangle identities.
9. Enlarge a representative field to contain lambda. Finite-stage linearity there
and transport compatibility give Omega-linearity of both quotient Hom maps.
10. Bilinearity of composition makes the specified quasi-inverse Omega-linear too.
11. Inclusion objects are literal pairs; naturality of beta gives the displayed
inclusion arrow equality. Every construction uses the existing raw pair categories,
so no idempotents are adjoined. -/
theorem fdHomLinearEquivalence
    (_D : FiniteFieldDatum.{d}) (_hl : l ≠ _D.p)
    [∀ E, (J.Φ E).CommShift ℤ]
    (_hadd : ∀ E, (J.Φ E).Additive)
    (_hlinear : ∀ E, (J.Φ E).Linear E.val)
    (_hexact : ∀ E, (J.Φ E).IsTriangulated)
    (_hshift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      NatTrans.CommShift (J.β h).hom ℤ)
    (_hunit : ∀ E (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
      HEq ((J.β (le_refl E)).hom.app K)
        ((J.Φ E).map ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω T E).inv.app K))) :
    FdHomLinearEquivalence l Ω T J := by
  unfold FdHomLinearEquivalence
  let : Limits.HasBinaryProducts
      (GeneralAlgebraicallyClosedCoefficients.Pair l Ω T) :=
    @pretriangulatedBinaryProducts _
      (GeneralAlgebraicallyClosedCoefficients.pairCategory l Ω T)
      (GeneralAlgebraicallyClosedCoefficients.preadditive (l := l) (Ω := Ω) (Y := T))
      (GeneralAlgebraicallyClosedCoefficients.zero_exists (l := l) (Ω := Ω) (Y := T))
      (GeneralAlgebraicallyClosedCoefficients.hasShift (l := l) (Ω := Ω) (Y := T))
      (GeneralAlgebraicallyClosedCoefficients.shiftAdditive (l := l) (Ω := Ω) (Y := T))
      (GeneralAlgebraicallyClosedCoefficients.pretriangulated (l := l) (Ω := Ω) (Y := T))
  simpa only [FdHomLinearEquivalence] using
    (@pairHomLinearEquivalence l _ Ω _ _ _
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
      (fun E ↦ pbcStageCategory l Ω T E)
      (fun E ↦ inferInstance) (fun E ↦ inferInstance)
      (fun E ↦ inferInstance) (fun E ↦ inferInstance)
      (fun E ↦ inferInstance) (fun E ↦ inferInstance)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
      (pbcScalarSystem l Ω T dT.out iT.out)
      (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)
      (by infer_instance)
      J (fun E ↦ inferInstance)
      _hadd _hlinear (intrinsicQbarScalarCompatible l Ω T)
      (pbcQbarScalarCompatible l Ω T)
      ((intrinsicQbarLinear_existsUnique l Ω T).exists.choose_spec)
      (fun _ _ _ _ ↦ rfl))

end WeilConjectures
