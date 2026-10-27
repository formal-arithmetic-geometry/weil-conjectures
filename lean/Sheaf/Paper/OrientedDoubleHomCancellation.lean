/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Sheaf.Paper.CoefficientEvaluationNaturality
public import Sheaf.Paper.DlLocallyConstructibleAdicHeart

/-! # Cancellation of a shifted Tate line in the canonical double Hom

Source: blueprint main-20261015, sk-thm-sf-dual-perfect.proof.md, sentence 4;
Stacks Project, Categories, Tags 0GWJ and 0FFM
(blueprint: lem-sf-oriented-double-hom-cancellation).

The helper definitions spell out the maps in the existing closed presentations.
The theorem applies them to the four actual coefficient categories of the datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
namespace WeilConjectures

section Maps
variable {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
  (T : CoefficientClosedStructure H) (s : @SymmetricCategory B _ T.monoidal)

/-- The simultaneous-tensor transpose s of the cancellation dependency, expressed
in the supplied right-tensor adjunction. Source: Stacks 0GWJ, 0FFM
(blueprint: lem-sf-oriented-double-hom-cancellation). -/
def orientedHomTensorBoth (U Y L : B) :
    H.obj (op U, Y) ⟶ H.obj (op (T.tensor.obj (U, L)), T.tensor.obj (Y, L)) :=
  T.transpose _ _ _
    ((T.monoidal.associator (H.obj (op U, Y)) U L).inv ≫
      T.tensor.map (Prod.mkHom (T.evaluation U Y) (𝟙 L)))

/-- q inverse is simultaneous tensoring followed by the left unitor on its target.
Source: blueprint sk-thm-sf-dual-perfect, proof sentence 4; Stacks 0GWJ
(blueprint: lem-sf-oriented-double-hom-cancellation). -/
def orientedHomCancellationInverse (L U : B) :
    H.obj (op U, T.monoidal.tensorUnit) ⟶ H.obj (op (T.tensor.obj (U, L)), L) :=
  orientedHomTensorBoth T U T.monoidal.tensorUnit L ≫
    H.map (Prod.mkHom (𝟙 _) (T.monoidal.leftUnitor L).hom)

/-- The inverse of theta is the canonical evaluation comparison followed by H(P,gamma).
Source: blueprint sk-thm-sf-dual-perfect, proof sentence 4
(blueprint: lem-sf-oriented-double-hom-cancellation). -/
def orientedHomThetaInverse (P L W : B) (gamma : L ≅ W)
    [IsIso (ringedSiteDualEvaluationLeft T s T.monoidal.tensorUnit (Iso.refl _) P L)] :
    T.tensor.obj (H.obj (op P, T.monoidal.tensorUnit), L) ≅ H.obj (op P, W) :=
  asIso (ringedSiteDualEvaluationLeft T s T.monoidal.tensorUnit (Iso.refl _) P L) ≪≫
    H.mapIso (Iso.prod (Iso.refl (op P)) gamma)

/-- The specified internal-Hom isomorphism t=H(theta inverse,gamma inverse).
Source: blueprint sk-thm-sf-dual-perfect, proof sentence 4
(blueprint: lem-sf-oriented-double-hom-cancellation). -/
def orientedHomDoubleIso (P L W : B) (gamma : L ≅ W)
    [IsIso (ringedSiteDualEvaluationLeft T s T.monoidal.tensorUnit (Iso.refl _) P L)] :
    H.obj (op (H.obj (op P, W)), W) ≅
      H.obj (op (T.tensor.obj (H.obj (op P, T.monoidal.tensorUnit), L)), L) :=
  H.mapIso (Iso.prod (orientedHomThetaInverse T s P L W gamma).op gamma.symm)

/-- The full conclusion in a fixed coefficient category. The inverse equations fix q
canonically. Its naturality and its action on every test-object Hom set are included,
as is the signed evaluation-transpose identity q t delta = j for perfect P.
The two inverse-line identifications are given data with no compatibility imposed.
Source: blueprint sk-thm-sf-dual-perfect, proof sentence 4; Stacks 0GWJ, 0FFM
(blueprint: lem-sf-oriented-double-hom-cancellation). -/
def OrientedDoubleHomCancellation (L I : B) : Prop :=
  ∀ (_a : T.tensor.obj (L, I) ≅ T.monoidal.tensorUnit)
    (_b : T.tensor.obj (I, L) ≅ T.monoidal.tensorUnit),
  ∃ q : ∀ U : B,
      H.obj (op (T.tensor.obj (U, L)), L) ≅ H.obj (op U, T.monoidal.tensorUnit),
    (∀ U : B, (q U).inv = orientedHomCancellationInverse T L U) ∧
    (∀ (U U' : B) (f : U' ⟶ U),
      H.map (Prod.mkHom (T.tensor.map (Prod.mkHom f (𝟙 L))).op (𝟙 L)) ≫ (q U').hom =
        (q U).hom ≫ H.map (Prod.mkHom f.op (𝟙 T.monoidal.tensorUnit))) ∧
    (∀ (U V : B) (v : T.tensor.obj (V, U) ⟶ T.monoidal.tensorUnit),
      (T.transpose V (T.tensor.obj (U, L)) L).symm
          (T.transpose V U T.monoidal.tensorUnit v ≫ (q U).inv) =
        (T.monoidal.associator V U L).inv ≫
          T.tensor.map (Prod.mkHom v (𝟙 L)) ≫ (T.monoidal.leftUnitor L).hom) ∧
    (∀ U V : B, Function.Bijective
      (fun v : T.tensor.obj (V, U) ⟶ T.monoidal.tensorUnit ↦
        (T.monoidal.associator V U L).inv ≫
          T.tensor.map (Prod.mkHom v (𝟙 L)) ≫ (T.monoidal.leftUnitor L).hom)) ∧
    (∀ (W : B) (gamma : L ≅ W) (P : B), @IsDualizable B _ T.monoidal P →
      ∀ [IsIso (ringedSiteDualEvaluationLeft T s T.monoidal.tensorUnit (Iso.refl _) P L)],
      ringedSiteBidual T s W P ≫ (orientedHomDoubleIso T s P L W gamma).hom ≫
          (q (H.obj (op P, T.monoidal.tensorUnit))).hom =
        ringedSiteBidual T s T.monoidal.tensorUnit P)

private theorem oriented_uncurry_eq {V U Y : B} (g : V ⟶ H.obj (op U, Y)) :
    (T.transpose V U Y).symm g =
      T.tensor.map (Prod.mkHom g (𝟙 U)) ≫ T.evaluation U Y := by
  change (@tensorRight B _ T.monoidal U).map g ≫ T.evaluation U Y = _
  let _ := T.monoidal
  simp [CoefficientClosedStructure.tensor]

private theorem oriented_uncurry_id (U Y : B) :
    (T.transpose _ U Y).symm (𝟙 _) = T.evaluation U Y := by
  rw [oriented_uncurry_eq]
  simp [CoefficientClosedStructure.tensor]

private theorem oriented_uncurry_comp {V V' U Y : B} (f : V' ⟶ V)
    (g : V ⟶ H.obj (op U, Y)) :
    (T.transpose V' U Y).symm (f ≫ g) =
      T.tensor.map (Prod.mkHom f (𝟙 U)) ≫ (T.transpose V U Y).symm g := by
  let _ := T.monoidal
  dsimp only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor]
  simp only [tensor_map, tensorHom_id]
  exact (T.adjunction U).homEquiv_naturality_left_symm f g

private theorem oriented_uncurry_map {V U U' Y Y' : B}
    (g : V ⟶ H.obj (op U, Y)) (f : U' ⟶ U) (h : Y ⟶ Y') :
    (T.transpose V U' Y').symm (g ≫ H.map (Prod.mkHom f.op h)) =
      T.tensor.map (Prod.mkHom (𝟙 V) f) ≫ (T.transpose V U Y).symm g ≫ h := by
  let _ := T.monoidal
  have hm : H.map (Prod.mkHom f.op h) =
      H.map (Prod.mkHom f.op (𝟙 Y)) ≫ H.map (Prod.mkHom (𝟙 (op U')) h) := by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hm, ← Category.assoc]
  rw [show (T.transpose V U' Y').symm
      ((g ≫ H.map (Prod.mkHom f.op (𝟙 Y))) ≫
        H.map (Prod.mkHom (𝟙 (op U')) h)) =
      (T.transpose V U' Y).symm (g ≫ H.map (Prod.mkHom f.op (𝟙 Y))) ≫ h from
    (T.adjunction U').homEquiv_naturality_right_symm _ h]
  rw [← Category.assoc]
  apply congrArg (fun k : T.tensor.obj (V, U') ⟶ Y ↦ k ≫ h)
  change (tensorRight U').map (g ≫ H.map (Prod.mkHom f.op (𝟙 Y))) ≫
    T.evaluation U' Y = _
  rw [Functor.map_comp, Category.assoc]
  change g ▷ U' ≫ (H.map (Prod.mkHom f.op (𝟙 Y)) ▷ U') ≫ T.evaluation U' Y = _
  rw [show (H.map (Prod.mkHom f.op (𝟙 Y)) ▷ U') ≫ T.evaluation U' Y =
      (H.obj (op U, Y) ◁ f) ≫ T.evaluation U Y from T.evaluation_naturality U U' Y f]
  dsimp only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.transpose]
  simp only [tensor_map, id_tensorHom]
  erw [Adjunction.homEquiv_counit]
  change _ = V ◁ f ≫ (g ▷ U ≫ T.evaluation U Y)
  rw [← whisker_exchange_assoc]

private theorem oriented_uncurry_inverse (L U V : B)
    (g : V ⟶ H.obj (op U, T.monoidal.tensorUnit)) :
    (T.transpose V (T.tensor.obj (U, L)) L).symm
        (g ≫ orientedHomCancellationInverse T L U) =
      (T.monoidal.associator V U L).inv ≫
        T.tensor.map (Prod.mkHom ((T.transpose V U T.monoidal.tensorUnit).symm g)
          (𝟙 L)) ≫ (T.monoidal.leftUnitor L).hom := by
  let _ := T.monoidal
  unfold orientedHomCancellationInverse orientedHomTensorBoth
  erw [← Category.assoc, oriented_uncurry_map T _ (𝟙 (U ⊗ L)) (λ_ L).hom]
  simp only [CoefficientClosedStructure.tensor, tensor_map, id_tensorHom,
    MonoidalCategory.whiskerLeft_id]
  erw [oriented_uncurry_comp T, Equiv.symm_apply_apply]
  simp only [CoefficientClosedStructure.tensor, tensor_map, tensorHom_id]
  erw [oriented_uncurry_eq T g]
  dsimp only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation]
  simp only [tensor_map, tensorHom_id]
  erw [Category.id_comp]
  change (g ▷ (U ⊗ L) ≫ (α_ _ U L).inv ≫ T.evaluation U (𝟙_ B) ▷ L) ≫ _ =
    (α_ V U L).inv ≫ ((g ▷ U ≫ T.evaluation U (𝟙_ B)) ▷ L) ≫ _
  rw [associator_inv_naturality_left_assoc, comp_whiskerRight]
  simp only [Category.assoc]

private theorem oriented_inverse_isIso (L I : B)
    (a : T.tensor.obj (L, I) ≅ T.monoidal.tensorUnit)
    (b : T.tensor.obj (I, L) ≅ T.monoidal.tensorUnit) (U : B) :
    IsIso (orientedHomCancellationInverse T L U) := by
  let _ := T.monoidal
  -- Tensoring by L is fully faithful for arbitrary choices of a and b.
  let E := tensorRightEquivalenceOfTensorIso a b
  refine isIso_of_yoneda_map_bijective _ (fun V ↦ ⟨?_, ?_⟩)
  · intro f g h
    apply (T.transpose V U (𝟙_ B)).symm.injective
    apply E.functor.map_injective
    change ((T.transpose V U (𝟙_ B)).symm f) ▷ L =
      ((T.transpose V U (𝟙_ B)).symm g) ▷ L
    apply (cancel_mono (λ_ L).hom).1
    apply (cancel_epi (α_ V U L).inv).1
    have hh := congrArg (T.transpose V (T.tensor.obj (U, L)) L).symm h
    rw [oriented_uncurry_inverse T L U V, oriented_uncurry_inverse T L U V] at hh
    simpa only [CoefficientClosedStructure.tensor, tensor_map, tensorHom_id] using hh
  · intro g
    let d : V ⊗ U ⟶ 𝟙_ B := E.functor.preimage
      ((α_ V U L).hom ≫ (T.transpose V (U ⊗ L) L).symm g ≫ (λ_ L).inv)
    refine ⟨T.transpose V U (𝟙_ B) d, (T.transpose V (U ⊗ L) L).symm.injective ?_⟩
    dsimp only
    erw [oriented_uncurry_inverse T L U V, Equiv.symm_apply_apply]
    have hd : d ▷ L =
        (α_ V U L).hom ≫ (T.transpose V (U ⊗ L) L).symm g ≫ (λ_ L).inv :=
      E.functor.map_preimage _
    simp only [CoefficientClosedStructure.tensor, tensor_map, tensorHom_id]
    rw [hd]
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl

private theorem oriented_uncurry_inverse_id (L U : B) :
    (T.transpose _ (T.tensor.obj (U, L)) L).symm
        (orientedHomCancellationInverse T L U) =
      (T.monoidal.associator _ U L).inv ≫
        T.tensor.map (Prod.mkHom (T.evaluation U T.monoidal.tensorUnit) (𝟙 L)) ≫
          (T.monoidal.leftUnitor L).hom := by
  have hh := oriented_uncurry_inverse T L U _ (𝟙 _)
  rw [Category.id_comp, oriented_uncurry_id] at hh
  exact hh

private theorem oriented_inverse_natural (L U U' : B) (f : U' ⟶ U) :
    orientedHomCancellationInverse T L U ≫
        H.map (Prod.mkHom (T.tensor.map (Prod.mkHom f (𝟙 L))).op (𝟙 L)) =
      H.map (Prod.mkHom f.op (𝟙 T.monoidal.tensorUnit)) ≫
        orientedHomCancellationInverse T L U' := by
  let _ := T.monoidal
  apply (T.transpose _ (T.tensor.obj (U', L)) L).symm.injective
  rw [oriented_uncurry_map T, oriented_uncurry_inverse_id T,
    oriented_uncurry_inverse T]
  have he := oriented_uncurry_map T (𝟙 (H.obj (op U, 𝟙_ B))) f (𝟙 (𝟙_ B))
  rw [Category.id_comp, oriented_uncurry_id] at he
  erw [he]
  simp only [Category.comp_id, CoefficientClosedStructure.tensor, tensor_map,
    id_tensorHom, tensorHom_id, comp_whiskerRight, Category.assoc]
  rw [associator_inv_naturality_middle_assoc]

private theorem oriented_cancellation (laws : SfCoefficientEvaluationLaws T s) (L I : B) :
    OrientedDoubleHomCancellation T s L I := by
  let _ := T.monoidal
  let _ := s
  intro a b
  have hi (U : B) : IsIso (orientedHomCancellationInverse T L U) :=
    oriented_inverse_isIso T L I a b U
  let q (U : B) := (asIso (orientedHomCancellationInverse T L U)).symm
  refine ⟨q, fun _ ↦ rfl, ?_, ?_, ?_, ?_⟩
  · intro U U' f
    apply (cancel_epi (q U).inv).1
    apply (cancel_mono (q U').inv).1
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [Iso.inv_hom_id_assoc]
    exact oriented_inverse_natural T L U U' f
  · intro U V v
    change (T.transpose V (T.tensor.obj (U, L)) L).symm
      (T.transpose V U (𝟙_ B) v ≫ orientedHomCancellationInverse T L U) = _
    rw [oriented_uncurry_inverse T, Equiv.symm_apply_apply]
  · intro U V
    have hh := ((T.transpose V U (𝟙_ B)).trans
      (((q U).symm.homToEquiv).trans (T.transpose V (U ⊗ L) L).symm)).bijective
    have he : (fun v : T.tensor.obj (V, U) ⟶ 𝟙_ B ↦
        (T.transpose V (U ⊗ L) L).symm
          (T.transpose V U (𝟙_ B) v ≫ orientedHomCancellationInverse T L U)) =
        (fun v ↦ (α_ V U L).inv ≫ T.tensor.map (Prod.mkHom v (𝟙 L)) ≫
          (λ_ L).hom) := by
      funext v
      erw [oriented_uncurry_inverse T, Equiv.symm_apply_apply]
    erw [← he]
    exact hh
  · intro W gamma P _ hc
    let A := H.obj (op P, 𝟙_ B)
    let theta := orientedHomThetaInverse T s P L W gamma
    have hev : theta.hom ▷ P ≫ T.evaluation P W =
        (α_ A L P).hom ≫ A ◁ (β_ L P).hom ≫ (α_ A P L).inv ≫
          T.evaluation P (𝟙_ B) ▷ L ≫ (λ_ L).hom ≫ gamma.hom := by
      have hcu := congrArg (T.transpose (T.tensor.obj (A, L)) P L).symm (laws.1 P L)
      dsimp only [A, CoefficientClosedStructure.tensor] at hcu
      erw [Equiv.symm_apply_apply] at hcu
      have ht := oriented_uncurry_map T
        (ringedSiteDualEvaluationLeft T s (𝟙_ B) (Iso.refl _) P L) (𝟙 P) gamma.hom
      erw [hcu] at ht
      rw [oriented_uncurry_eq T] at ht
      dsimp only [CoefficientClosedStructure.tensor] at ht
      simp only [tensor_map, tensorHom_id, id_tensorHom, id_whiskerRight] at ht
      erw [Category.id_comp] at ht
      simpa only [theta, orientedHomThetaInverse, Iso.trans_hom, asIso_hom,
        Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, A,
        CoefficientClosedStructure.tensor, tensor_map, tensorHom_id, id_tensorHom,
        MonoidalCategory.whiskerLeft_id, id_whiskerRight, Category.id_comp,
        op_id, Category.assoc] using ht
    -- Compare uncurries before cancelling the canonical inverse of q.
    apply (cancel_mono (q A).inv).1
    change (ringedSiteBidual T s W P ≫
      (orientedHomDoubleIso T s P L W gamma).hom ≫ (q A).hom) ≫ (q A).inv = _
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change ringedSiteBidual T s W P ≫
      H.map (Prod.mkHom theta.hom.op gamma.inv) =
        ringedSiteBidual T s (𝟙_ B) P ≫ orientedHomCancellationInverse T L A
    apply (T.transpose P (T.tensor.obj (A, L)) L).symm.injective
    rw [oriented_uncurry_map T, oriented_uncurry_inverse T]
    simp only [ringedSiteBidual, Equiv.symm_apply_apply]
    simp only [CoefficientClosedStructure.tensor, tensor_map, id_tensorHom, tensorHom_id]
    dsimp only [A]
    erw [Equiv.symm_apply_apply]
    simp only [Category.assoc]
    erw [BraidedCategory.braiding_naturality_right_assoc]
    erw [← Category.assoc (theta.hom ▷ P) (T.evaluation P W) gamma.inv, hev]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change (β_ P (A ⊗ L)).hom ≫ (α_ A L P).hom ≫ A ◁ (β_ L P).hom ≫
      (α_ A P L).inv ≫ T.evaluation P (𝟙_ B) ▷ L ≫ (λ_ L).hom = _
    -- The hexagon exposes the two opposite crossings of P and L.
    rw [BraidedCategory.braiding_tensor_right_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, SymmetricCategory.symmetry,
      MonoidalCategory.whiskerLeft_id, Category.id_comp, comp_whiskerRight]
    monoidal

/-- The cancellation argument only needs the closed evaluation laws: the two
opposite-line contractions are the arguments of its conclusion. This exposes the
categorical argument used at all four coefficient stages, allowing the same proof
for isomorphic presentations of the shifted line.
Source: blueprint sk-thm-sf-dual-perfect, proof sentence 4; Stacks 0GWJ, 0FFM
(blueprint: lem-sf-oriented-double-hom-cancellation).
Proof: apply the preceding tensor-Hom argument. Tensor by L is fully faithful
using its two contractions, so the specified cancellation transpose is invertible.
Uncurrying the relative bidual, substituting the evaluation law, and cancelling
the opposite signed crossings gives coefficient biduality. -/
theorem sfOrientedCancellation_of_evaluationLaws
    (laws : SfCoefficientEvaluationLaws T s) (L I : B) :
    OrientedDoubleHomCancellation T s L I :=
  oriented_cancellation T s laws L I

end Maps

/-- The published signed finite line as an ambient derived object. The existing
dlAdicGeometricResidueInvertible supplies the residue inverses forced by ell distinct from p.
Source: blueprint coefficient conventions and sk-thm-sf-dual-perfect, proof sentence 4
(blueprint: lem-sf-oriented-double-hom-cancellation). -/
def orientedFiniteTateObject (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : SixFunctorSpace D) (n : ℕ) (m : ℤ) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  (DerivedCategory.singleFunctor _ 0).obj (finiteCoefficientTwist C.l E X.obj.left n m)

/-- The same completed integral line with the standing residue inverses supplied,
without any additional hypothesis. Source: blueprint coefficient conventions and
sk-thm-sf-dual-perfect, proof sentence 4
(blueprint: lem-sf-oriented-double-hom-cancellation). -/
def orientedIntegralTateObject (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : SixFunctorSpace D) (m : ℤ) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  sfIntegralTwistingObject C.l E X.obj.left m

/-- Rational image of the existing completed signed line, with the standing
residue inverses supplied. Source: blueprint coefficient conventions
(blueprint: lem-sf-oriented-double-hom-cancellation). -/
def orientedRationalTateObject (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : SixFunctorSpace D) (m : ℤ) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  sfRationalTwistingCoefficient C.l E X.obj.left m

/-- The recorded common-stage signed line, with the standing residue inverses supplied.
Source: blueprint coefficient conventions
(blueprint: lem-sf-oriented-double-hom-cancellation). -/
def orientedCommonTateObject (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (X : SixFunctorSpace D) (m : ℤ) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  sfQbarTwistingCoefficient C.l X.obj.left C.Qbar m

/-- Cancellation-normalized double-Hom compatibility at every coefficient stage.
The equalities specifying L and I merely give the underlying shifted Tate lines;
their full-subcategory membership witnesses are immaterial. No separatedness or
smoothness hypothesis on X, and no use of geometric biduality, is required.
Source: blueprint main-20261015, sk-thm-sf-dual-perfect.proof.md, sentence 4;
Stacks Project, Categories, Tags 0GWJ and 0FFM
(blueprint: lem-sf-oriented-double-hom-cancellation).

Proof:
1. Apply lem-sf-invertible-factor-hom-cancellation with X=U, Y=1, J=L, I=L inverse.
   Its evaluation-normalized s inverse, composed with H(1,lambda inverse), is q.
   Naturality and the inverse transpose formula give the displayed test-object
   bijection v maps to lambda (v tensor 1), with the actual associator.
2. Put A=H(P,1), B=H(P,W), and e=evaluation into 1. By the conditional formula of
   lem-sf-coefficient-evaluation-naturality, evaluation after theta inverse tensor P
   is gamma lambda (e tensor 1) (1 tensor symmetry(L,P)).
3. Uncurry t delta. Naturality of evaluation and symmetry moves theta inverse to
   the evaluation input. Substitution of step 2 cancels gamma inverse gamma.
4. Expand symmetry(P,A tensor L) by the hexagon. The two crossings of P and L
   cancel by the symmetry axiom, leaving lambda ((e symmetry(P,A)) tensor 1).
   This is exactly the uncurry of j followed by q inverse from step 1.
5. Injectivity of transposition gives t delta = j q inverse; compose with q.
   The isomorphism t is the internal-Hom image of theta inverse and gamma inverse.
All steps use the recorded completed, rationalized or common-stage tensor and signed
symmetry. The explicit perfectness and comparison-invertibility hypotheses are
retained; no geometric dualizing object or unsigned cohomology identification enters. -/
theorem sixFunctor_orientedDoubleHomCancellation
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ)
    (S : SixFunctorDatum D C E (n + 1) (Nat.succ_pos n)) (X : SixFunctorSpace D) :
    (∀ (m r : ℤ)
      (L I : (S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory),
      L.obj.obj = (orientedFiniteTateObject D C E X n m)⟦2 * r⟧ →
      I.obj.obj = (orientedFiniteTateObject D C E X n (-m))⟦-(2 * r)⟧ →
      OrientedDoubleHomCancellation (S.finiteClosed X).closed (S.finiteClosed X).symmetric
        L I) ∧
    (∀ (m r : ℤ)
      (L I : (S.toSixFunctorOperationDatum.integralFiniteTorDomain X).FullSubcategory),
      L.obj.obj = (orientedIntegralTateObject D C E X m)⟦2 * r⟧ →
      I.obj.obj = (orientedIntegralTateObject D C E X (-m))⟦-(2 * r)⟧ →
      OrientedDoubleHomCancellation (S.integralClosed X).closed (S.integralClosed X).symmetric
        L I) ∧
    (∀ (m r : ℤ) (L I : (⊤ : ObjectProperty
        (sfRationalConstructibleCategory C.l E X.obj.left)).FullSubcategory),
      L.obj = (orientedRationalTateObject D C E X m)⟦2 * r⟧ →
      I.obj = (orientedRationalTateObject D C E X (-m))⟦-(2 * r)⟧ →
      OrientedDoubleHomCancellation (S.rationalClosed X).closed (S.rationalClosed X).symmetric
        L I) ∧
    (∀ (m r : ℤ) (L I : (⊤ : ObjectProperty
        (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)).FullSubcategory),
      L.obj = (orientedCommonTateObject D C X m)⟦2 * r⟧ →
      I.obj = (orientedCommonTateObject D C X (-m))⟦-(2 * r)⟧ →
      OrientedDoubleHomCancellation (S.commonClosed X).closed (S.commonClosed X).symmetric
        L I) := by
  obtain ⟨hf, hi, hr, hc, _⟩ := sfCoefficientEvaluationNaturality S X
  exact ⟨fun _ _ L I _ _ ↦ oriented_cancellation _ _ hf L I,
    fun _ _ L I _ _ ↦ oriented_cancellation _ _ hi L I,
    fun _ _ L I _ _ ↦ oriented_cancellation _ _ hr L I,
    fun _ _ L I _ _ ↦ oriented_cancellation _ _ hc L I⟩

end WeilConjectures
