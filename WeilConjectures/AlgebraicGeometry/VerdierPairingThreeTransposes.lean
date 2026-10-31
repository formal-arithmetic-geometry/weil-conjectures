/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction

import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Projection--evaluation pairing and its three Weil transposes

Source: blueprint, prop-weil-operations, evaluation/adjunction construction of the formal
Verdier exchange (blueprint: lem-pod-verdier-pairing-three-transposes).

The supplied-domain interfaces below retain the underlying tensor--Hom adjunctions,
the evaluation normalization, and the underlying units of the lifted adjunctions.
They assert no existence of exceptional adjoints on an ambient derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w vX vY vC vB
open CategoryTheory CategoryTheory.Endofunctor Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.VerdierPairing

/-- The rational or common-stage category, with precisely the coefficient categories of the
recorded dependencies. `none` means algebraically closed coefficients.
Source: prop-weil-operations, supplied domains
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
abbrev CategoryAt (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (T : Scheme.{u})
    (E : Option (ConstructibleExceptionalCoefficients.FieldStage.{u} l)) :=
  ConstructibleExceptionalCoefficients.C l Ω T
    (match E with | some E' => .rational E' | none => .closed)

/-- The actual geometric-Frobenius pullback in either coefficient category.
Source: prop-weil-operations, Weil-pair convention
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def frobenius (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (E : Option (ConstructibleExceptionalCoefficients.FieldStage.{u} l)) :
    CategoryAt l Ω (D.geometricFiber T₀).left E ⥤
      CategoryAt l Ω (D.geometricFiber T₀).left E :=
  match E with
  | some E' => sfWeilFrobeniusPullback D l hl T₀ E'.carrier
  | none => sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω

/-- Restrict Frobenius to the supplied full domain, using its stipulated stability.
Source: prop-weil-operations, supplied domains
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def restrict {C : Type v} [Category.{w} C] (Φ : C ⥤ C) (S : ObjectProperty C)
    (stable : ∀ K : S.FullSubcategory, S (Φ.obj K.obj)) :
    S.FullSubcategory ⥤ S.FullSubcategory :=
  S.lift (S.ι ⋙ Φ) stable

section Calculus
variable {X : Type v} {Y : Type w} [Category.{vX} X] [Category.{vY} Y]
  (ΦX : X ⥤ X) (ΦY : Y ⥤ Y)

/-- The supplied tensor and partial Hom, restricted to their closed domain, with their
canonical Frobenius comparisons. No tensor--Hom adjunction on X is presumed globally.
Source: prop-weil-operations, supplied canonical operations
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
structure TensorHomData {C : Type v} [Category.{vC} C] (Φ : C ⥤ C) where
  tensor : C ⥤ C ⥤ C
  hom : Cᵒᵖ ⥤ C ⥤ C
  tensorComparison : Functor.uncurry.obj tensor ⋙ Φ ≅
    Φ.prod Φ ⋙ Functor.uncurry.obj tensor
  homComparison : Functor.uncurry.obj hom ⋙ Φ ≅
    Φ.op.prod Φ ⋙ Functor.uncurry.obj hom

/-- On Y the supplied adjunctions have evaluation as counit;
`evaluation_naturality` fixes the contravariant Hom action to be precomposition.
The last field is evaluation compatibility of the canonical Frobenius comparisons.
Source: prop-weil-operations, evaluation and lifted operations
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
structure ClosedData {C : Type v} [Category.{vC} C] (Φ : C ⥤ C)
    extends TensorHomData Φ where
  adj : ∀ K : C, tensor.obj K ⊣ hom.obj (op K)
  evaluation_naturality : ∀ (K L W : C) (f : K ⟶ L),
    (tensor.map f).app ((hom.obj (op L)).obj W) ≫ (adj L).counit.app W =
      (tensor.obj K).map ((hom.map f.op).app W) ≫ (adj K).counit.app W
  evaluation_compatibility : ∀ K W : C,
    tensorComparison.hom.app (K, (hom.obj (op K)).obj W) ≫
      (tensor.obj (Φ.obj K)).map (homComparison.hom.app (op K, W)) ≫
        (adj (Φ.obj K)).counit.app (Φ.obj W) = Φ.map ((adj K).counit.app W)

/-- The existing bifunctor lift of the supplied tensor.
Source: prop-weil-operations, tensor Weil lift
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def TensorHomData.weilTensor {C : Type v} [Category.{vC} C] {Φ : C ⥤ C} (d : TensorHomData Φ) :
    IsoAlgebra Φ ⥤ IsoAlgebra Φ ⥤ IsoAlgebra Φ :=
  IsoAlgebra.mapOfNatIso₂ d.tensor d.tensorComparison

/-- Hom on fixed pairs uses the opposite of the inverse structure in its first variable.
Source: prop-weil-operations, explicit dual structure formula
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def TensorHomData.weilHom {C : Type v} [Category.{vC} C] {Φ : C ⥤ C} (d : TensorHomData Φ) :
    (IsoAlgebra Φ)ᵒᵖ ⥤ IsoAlgebra Φ ⥤ IsoAlgebra Φ :=
  IsoAlgebra.opFunctor ⋙ IsoAlgebra.mapOfNatIso₂ d.hom d.homComparison

/-- The dual Weil pair on the fixed underlying object RHom(K,omega).
Source: prop-weil-operations, explicit dual structure formula
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def ClosedData.dual {C : Type v} [Category.{vC} C] {Φ : C ⥤ C} (d : ClosedData Φ)
    (W K : IsoAlgebra Φ) : IsoAlgebra Φ :=
  ((d.toTensorHomData.weilHom.obj (op K)).obj W)

/-- A supplied adjunction and its canonical Weil lifts, with the prescribed underlying
units and counits. It is only asserted on the supplied domains.
Source: prop-weil-operations, lifted adjunctions
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
structure LiftedAdjunction (L : X ⥤ Y) (R : Y ⥤ X) where
  adj : L ⊣ R
  leftComparison : L ⋙ ΦY ≅ ΦX ⋙ L
  rightComparison : R ⋙ ΦX ≅ ΦY ⋙ R
  weilAdj : IsoAlgebra.mapOfNatIso leftComparison ⊣
    IsoAlgebra.mapOfNatIso rightComparison
  unit_eq : ∀ K : IsoAlgebra ΦX, (weilAdj.unit.app K).hom.f = adj.unit.app K.carrier
  counit_eq : ∀ K : IsoAlgebra ΦY,
    (weilAdj.counit.app K).hom.f = adj.counit.app K.carrier

/-- Composition and inversion equations in the underlying category of fixed pairs.
This includes inversion when only the underlying arrow has been declared invertible.
Source: prop-weil-operations, arrow condition
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def ArrowLaws {C : Type v} [Category.{vC} C] (Φ : C ⥤ C) : Prop :=
  (∀ (B C' D : IsoAlgebra Φ) (u : B ⟶ C') (v' : C' ⟶ D),
    B.str.hom ≫ (u.hom.f ≫ v'.hom.f) =
      Φ.map (u.hom.f ≫ v'.hom.f) ≫ D.str.hom) ∧
  (∀ (B C' : IsoAlgebra Φ) (u : B ⟶ C') (hu : IsIso u.hom.f),
    C'.str.hom ≫ @inv _ _ _ _ u.hom.f hu =
      Φ.map (@inv _ _ _ _ u.hom.f hu) ≫ B.str.hom)

/-- The evaluation structure formula, its equivariance equation and uniqueness, all on the
same underlying Hom object. The first factor is K, so no implicit symmetry is suppressed.
Source: prop-weil-operations, dual evaluation
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def EvaluationAssertion {C : Type v} [Category.{vC} C] {Φ : C ⥤ C} (d : ClosedData Φ)
    (W : IsoAlgebra Φ) : Prop :=
  ∀ K : IsoAlgebra Φ,
    (d.dual W K).str.hom = d.homComparison.hom.app (op K.carrier, W.carrier) ≫
      (d.hom.map K.str.inv.op).app (Φ.obj W.carrier) ≫
        (d.hom.obj (op K.carrier)).map W.str.hom ∧
    (((d.toTensorHomData.weilTensor.obj K).obj (d.dual W K)).str.hom ≫
      (d.adj K.carrier).counit.app W.carrier =
        Φ.map ((d.adj K.carrier).counit.app W.carrier) ≫ W.str.hom) ∧
    ∀ δ : Φ.obj ((d.hom.obj (op K.carrier)).obj W.carrier) ≅
        (d.hom.obj (op K.carrier)).obj W.carrier,
      d.tensorComparison.hom.app (K.carrier, (d.hom.obj (op K.carrier)).obj W.carrier) ≫
          (Functor.uncurry.obj d.tensor).map (Prod.mkHom K.str.hom δ.hom) ≫
            (d.adj K.carrier).counit.app W.carrier =
          Φ.map ((d.adj K.carrier).counit.app W.carrier) ≫ W.str.hom →
        δ = (d.dual W K).str

/-- The particular dual A = D_Y(FM), with its induced structure.
Source: prop-weil-operations, pairing construction
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def imageDual (y : ClosedData ΦY) (W : IsoAlgebra ΦY)
    {F : X ⥤ Y} {G : Y ⥤ X} (e : LiftedAdjunction ΦX ΦY F G)
    (M : IsoAlgebra ΦX) : IsoAlgebra ΦY :=
  y.dual W ((IsoAlgebra.mapOfNatIso e.leftComparison).obj M)

/-- The particular source V = M tensor P(A), with the canonical tensor lift.
Source: prop-weil-operations, pairing construction
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def tensorSource (x : TensorHomData ΦX) (y : ClosedData ΦY) (W : IsoAlgebra ΦY)
    {F : X ⥤ Y} {G : Y ⥤ X} {P : Y ⥤ X} {Q : X ⥤ Y}
    (e : LiftedAdjunction ΦX ΦY F G) (o : LiftedAdjunction ΦY ΦX P Q)
    (M : IsoAlgebra ΦX) : IsoAlgebra ΦX :=
  (x.weilTensor.obj M).obj
    ((IsoAlgebra.mapOfNatIso o.leftComparison).obj (imageDual ΦX ΦY y W e M))

/-- The pairing and all three transposes, with the displayed underlying formulas.
`pi` is the component of the recorded projection, never an arbitrary invertible arrow.
The exceptional, tensor--Hom and ordinary Hom bijections are retained in the conclusion.
Source: prop-weil-operations, inverse projection followed by evaluation
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def TransposeAssertion
    {B : Type u} [Category.{vB} B]
    (d : CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage
      (DX := X) (DB := B) (DY := Y) (DX' := X) (DB' := B) (DY' := Y))
    (x : TensorHomData ΦX) (y : ClosedData ΦY)
    (G : Y ⥤ X) (Q : X ⥤ Y)
    (e : LiftedAdjunction ΦX ΦY d.compactSupport G)
    (o : LiftedAdjunction ΦY ΦX d.pull Q) (W : IsoAlgebra ΦY) : Prop :=
  ∀ (M : IsoAlgebra ΦX)
    (underlying : x.tensor.obj M.carrier ⊣ x.hom.obj (op M.carrier))
    (a : (x.weilTensor.obj M) ⊣ (x.weilHom.obj (op M)))
    (_a_unit : ∀ K : IsoAlgebra ΦX,
      (a.unit.app K).hom.f = underlying.unit.app K.carrier)
    (_a_counit : ∀ K : IsoAlgebra ΦX,
      (a.counit.app K).hom.f = underlying.counit.app K.carrier)
    (pi : (y.tensor.obj (d.compactSupport.obj M.carrier)).obj
        (imageDual ΦX ΦY y W e M).carrier ≅
      d.compactSupport.obj (tensorSource ΦX ΦY x y W e o M).carrier)
    (_pi_eq : HEq pi.hom
      ((d.projection.app M.carrier).app (imageDual ΦX ΦY y W e M).carrier))
    (_pi_weil : ((y.toTensorHomData.weilTensor.obj
        ((IsoAlgebra.mapOfNatIso e.leftComparison).obj M)).obj
          (imageDual ΦX ΦY y W e M)).str.hom ≫ pi.hom =
      ΦY.map pi.hom ≫ ((IsoAlgebra.mapOfNatIso e.leftComparison).obj
        (tensorSource ΦX ΦY x y W e o M)).str.hom),
  ∃ (b : (IsoAlgebra.mapOfNatIso e.leftComparison).obj
        (tensorSource ΦX ΦY x y W e o M) ⟶ W)
    (t : tensorSource ΦX ΦY x y W e o M ⟶
      (IsoAlgebra.mapOfNatIso e.rightComparison).obj W)
    (r : (IsoAlgebra.mapOfNatIso o.leftComparison).obj (imageDual ΦX ΦY y W e M) ⟶
      (x.weilHom.obj (op M)).obj ((IsoAlgebra.mapOfNatIso e.rightComparison).obj W))
    (s : imageDual ΦX ΦY y W e M ⟶ (IsoAlgebra.mapOfNatIso o.rightComparison).obj
      ((x.weilHom.obj (op M)).obj ((IsoAlgebra.mapOfNatIso e.rightComparison).obj W))),
    b.hom.f = pi.inv ≫ (y.adj (d.compactSupport.obj M.carrier)).counit.app W.carrier ∧
    t.hom.f = e.adj.unit.app (tensorSource ΦX ΦY x y W e o M).carrier ≫ G.map b.hom.f ∧
    r.hom.f = underlying.unit.app
        (d.pull.obj (imageDual ΦX ΦY y W e M).carrier) ≫
      (x.hom.obj (op M.carrier)).map t.hom.f ∧
    s.hom.f = o.adj.unit.app (imageDual ΦX ΦY y W e M).carrier ≫ Q.map r.hom.f ∧
    t = (e.weilAdj.homEquiv (tensorSource ΦX ΦY x y W e o M) W) b ∧
    r = (a.homEquiv
      ((IsoAlgebra.mapOfNatIso o.leftComparison).obj (imageDual ΦX ΦY y W e M))
      ((IsoAlgebra.mapOfNatIso e.rightComparison).obj W)) t ∧
    s = (o.weilAdj.homEquiv (imageDual ΦX ΦY y W e M) _) r

private theorem arrow_inverse {C : Type v} [Category.{vC} C] (Φ : C ⥤ C)
    {A B : C} {a : Φ.obj A ⟶ A} {b : Φ.obj B ⟶ B}
    (f : A ⟶ B) [IsIso f] (h : a ≫ f = Φ.map f ≫ b) :
    b ≫ inv f = Φ.map (inv f) ≫ a := by
  apply (cancel_epi (Φ.map f)).mp
  simp only [← Category.assoc, ← Φ.map_comp, IsIso.hom_inv_id, Φ.map_id,
    Category.id_comp]
  rw [← h]
  simp

private theorem arrow_laws {C : Type v} [Category.{vC} C] (Φ : C ⥤ C) :
    ArrowLaws Φ := by
  constructor
  · intro B C' D u v'
    simpa only [IsoAlgebra.str_hom, IsoAlgebra.comp_hom_f] using (u ≫ v').hom.h.symm
  · intro B C' u hu
    exact arrow_inverse Φ u.hom.f u.hom.h.symm

private theorem evaluation_transport {C : Type v} [Category.{vC} C] {Φ : C ⥤ C}
    (d : ClosedData Φ) {K L W W' : C} (α : L ≅ K) (β : W' ⟶ W) :
    (d.tensor.map α.hom).app ((d.hom.obj (op L)).obj W') ≫
        (d.tensor.obj K).map ((d.hom.map α.inv.op).app W' ≫
          (d.hom.obj (op K)).map β) ≫ (d.adj K).counit.app W =
      (d.adj L).counit.app W' ≫ β := by
  have hn : (d.tensor.obj K).map ((d.hom.obj (op K)).map β) ≫
      (d.adj K).counit.app W = (d.adj K).counit.app W' ≫ β :=
    (d.adj K).counit.naturality β
  have hc : (d.tensor.map α.hom).app ((d.hom.obj (op L)).obj W') ≫
      (d.tensor.obj K).map ((d.hom.map α.inv.op).app W') ≫
        (d.adj K).counit.app W' = (d.adj L).counit.app W' := by
    rw [← d.evaluation_naturality K L W' α.inv]
    simp only [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp,
      α.hom_inv_id]
    rw [d.tensor.map_id, NatTrans.id_app, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ β) hc

private theorem evaluation_assertion {C : Type v} [Category.{vC} C] {Φ : C ⥤ C}
    (d : ClosedData Φ) (W : IsoAlgebra Φ) : EvaluationAssertion d W := by
  intro K
  have hd : (d.dual W K).str.hom =
      d.homComparison.hom.app (op K.carrier, W.carrier) ≫
        (d.hom.map K.str.inv.op).app (Φ.obj W.carrier) ≫
          (d.hom.obj (op K.carrier)).map W.str.hom := by
    simp [ClosedData.dual, TensorHomData.weilHom,
      IsoAlgebra.mapOfNatIso₂_obj_obj_str, Functor.uncurry_obj_map]
    rfl
  have ht : (((d.toTensorHomData.weilTensor.obj K).obj (d.dual W K))).str.hom =
      d.tensorComparison.hom.app (K.carrier, (d.hom.obj (op K.carrier)).obj W.carrier) ≫
        (d.tensor.map K.str.hom).app (Φ.obj ((d.hom.obj (op K.carrier)).obj W.carrier)) ≫
          (d.tensor.obj K.carrier).map (d.dual W K).str.hom := by
    simp [TensorHomData.weilTensor, IsoAlgebra.mapOfNatIso₂_obj_obj_str,
      Functor.uncurry_obj_map]
    rfl
  have he : (((d.toTensorHomData.weilTensor.obj K).obj (d.dual W K))).str.hom ≫
        (d.adj K.carrier).counit.app W.carrier =
      Φ.map ((d.adj K.carrier).counit.app W.carrier) ≫ W.str.hom := by
    have hn := (d.tensor.map K.str.hom).naturality
      (d.homComparison.hom.app (op K.carrier, W.carrier))
    dsimp only [Functor.comp_obj, Functor.uncurry_obj_obj, Functor.prod_obj] at hn
    rw [ht, hd]
    have hc := evaluation_transport d K.str W.str.hom
    calc
      _ = d.tensorComparison.hom.app
          (K.carrier, (d.hom.obj (op K.carrier)).obj W.carrier) ≫
          (d.tensor.map K.str.hom).app
            (Φ.obj ((d.hom.obj (op K.carrier)).obj W.carrier)) ≫
          (d.tensor.obj K.carrier).map
            (d.homComparison.hom.app (op K.carrier, W.carrier)) ≫
          (d.tensor.obj K.carrier).map
            ((d.hom.map K.str.inv.op).app (Φ.obj W.carrier) ≫
              (d.hom.obj (op K.carrier)).map W.str.hom) ≫
          (d.adj K.carrier).counit.app W.carrier := by
        simp only [Functor.map_comp, Category.assoc]
      _ = d.tensorComparison.hom.app
          (K.carrier, (d.hom.obj (op K.carrier)).obj W.carrier) ≫
          (d.tensor.obj (Φ.obj K.carrier)).map
            (d.homComparison.hom.app (op K.carrier, W.carrier)) ≫
          (d.tensor.map K.str.hom).app
            ((d.hom.obj (op (Φ.obj K.carrier))).obj (Φ.obj W.carrier)) ≫
          (d.tensor.obj K.carrier).map
            ((d.hom.map K.str.inv.op).app (Φ.obj W.carrier) ≫
              (d.hom.obj (op K.carrier)).map W.str.hom) ≫
          (d.adj K.carrier).counit.app W.carrier := by
        simpa only [Category.assoc, Functor.op_obj] using congrArg
          (fun z ↦ d.tensorComparison.hom.app
            (K.carrier, (d.hom.obj (op K.carrier)).obj W.carrier) ≫ z ≫
            (d.tensor.obj K.carrier).map
              ((d.hom.map K.str.inv.op).app (Φ.obj W.carrier) ≫
                (d.hom.obj (op K.carrier)).map W.str.hom) ≫
            (d.adj K.carrier).counit.app W.carrier) hn.symm
      _ = _ := by
        rw [hc]
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ W.str.hom)
          (d.evaluation_compatibility K.carrier W.carrier)
  refine ⟨hd, he, ?_⟩
  intro δ hδ
  apply Iso.ext
  apply (d.adj K.carrier).homEquiv _ _ |>.symm.injective
  change (d.tensor.obj K.carrier).map δ.hom ≫ (d.adj K.carrier).counit.app W.carrier =
    (d.tensor.obj K.carrier).map (d.dual W K).str.hom ≫
      (d.adj K.carrier).counit.app W.carrier
  apply (cancel_epi ((d.tensor.map K.str.hom).app
    (Φ.obj ((d.hom.obj (op K.carrier)).obj W.carrier)))).mp
  apply (cancel_epi (d.tensorComparison.hom.app
    (K.carrier, (d.hom.obj (op K.carrier)).obj W.carrier))).mp
  simpa only [Functor.uncurry_obj_map, Category.assoc, ht, Functor.prod_obj] using hδ.trans he.symm

private theorem transpose_assertion {B : Type u} [Category.{vB} B]
    (d : CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage
      (DX := X) (DB := B) (DY := Y) (DX' := X) (DB' := B) (DY' := Y))
    (x : TensorHomData ΦX) (y : ClosedData ΦY) (G : Y ⥤ X) (Q : X ⥤ Y)
    (e : LiftedAdjunction ΦX ΦY d.compactSupport G)
    (o : LiftedAdjunction ΦY ΦX d.pull Q) (W : IsoAlgebra ΦY) :
    TransposeAssertion ΦX ΦY d x y G Q e o W := by
  intro M underlying a a_unit _a_counit pi _pi_eq pi_weil
  let K := (IsoAlgebra.mapOfNatIso e.leftComparison).obj M
  let A := imageDual ΦX ΦY y W e M
  let V := tensorSource ΦX ΦY x y W e o M
  let b : (IsoAlgebra.mapOfNatIso e.leftComparison).obj V ⟶ W :=
    ObjectProperty.homMk
      { f := pi.inv ≫ (y.adj (d.compactSupport.obj M.carrier)).counit.app W.carrier
        h := by
          have hi := arrow_inverse ΦY pi.hom pi_weil
          have he := (evaluation_assertion y W K).2.1
          change ((y.weilTensor.obj K).obj A).str.hom ≫
            (y.adj K.carrier).counit.app W.carrier =
              ΦY.map ((y.adj K.carrier).counit.app W.carrier) ≫ W.str.hom at he
          change ΦY.map (pi.inv ≫ (y.adj K.carrier).counit.app W.carrier) ≫
            W.str.hom = ((IsoAlgebra.mapOfNatIso e.leftComparison).obj V).str.hom ≫
              pi.inv ≫ (y.adj K.carrier).counit.app W.carrier
          have hi' : ((IsoAlgebra.mapOfNatIso e.leftComparison).obj V).str.hom ≫
              pi.inv = ΦY.map pi.inv ≫ ((y.weilTensor.obj K).obj A).str.hom := by
            simpa only [IsIso.Iso.inv_hom] using hi
          rw [Functor.map_comp, Category.assoc, ← he, ← Category.assoc, ← hi']
          exact Category.assoc _ _ _ }
  let t := (e.weilAdj.homEquiv V W) b
  let r := (a.homEquiv ((IsoAlgebra.mapOfNatIso o.leftComparison).obj A)
    ((IsoAlgebra.mapOfNatIso e.rightComparison).obj W)) t
  let s := (o.weilAdj.homEquiv A _) r
  refine ⟨b, t, r, s, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · change (e.weilAdj.unit.app V ≫
      (IsoAlgebra.mapOfNatIso e.rightComparison).map b).hom.f = _
    simp only [IsoAlgebra.comp_hom_f, IsoAlgebra.mapOfNatIso_map_hom_f, e.unit_eq]
    rfl
  · change (a.unit.app ((IsoAlgebra.mapOfNatIso o.leftComparison).obj A) ≫
      (x.weilHom.obj (op M)).map t).hom.f = _
    rw [IsoAlgebra.comp_hom_f, a_unit]
    simp [TensorHomData.weilHom, IsoAlgebra.mapOfNatIso₂, Functor.curry,
      Functor.curryObj, Functor.uncurry_obj_map, IsoAlgebra.prod, A]
    rfl
  · change (o.weilAdj.unit.app A ≫
      (IsoAlgebra.mapOfNatIso o.rightComparison).map r).hom.f = _
    simp only [IsoAlgebra.comp_hom_f, IsoAlgebra.mapOfNatIso_map_hom_f, o.unit_eq]
    rfl

end Calculus

/-- A full, Frobenius-stable domain in the recorded rational/common-stage category.
Source: prop-weil-operations, supplied-domain proviso
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
structure Domain (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (E : Option (ConstructibleExceptionalCoefficients.FieldStage.{u} l)) where
  objects : ObjectProperty (CategoryAt l Ω (D.geometricFiber T₀).left E)
  stable : ∀ K : objects.FullSubcategory,
    objects ((frobenius D l hl Ω T₀ E).obj K.obj)

namespace Domain
variable {D : FiniteFieldDatum.{u}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
  {Ω : Type u} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {T₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
  {E : Option (ConstructibleExceptionalCoefficients.FieldStage.{u} l)}

/-- The supplied full subcategory, with the original underlying Hom sets.
Source: prop-weil-operations, supplied-domain proviso
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
abbrev C (S : Domain D l hl Ω T₀ E) := S.objects.FullSubcategory

/-- The inherited category structure on the supplied full domain.
Source: prop-weil-operations, supplied-domain proviso
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
instance category (S : Domain D l hl Ω T₀ E) : Category.{u + 2} S.C := inferInstance

/-- Geometric Frobenius on the supplied full domain, restricted from the actual pullback.
Source: prop-weil-operations, supplied-domain proviso
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def phi (S : Domain D l hl Ω T₀ E) : S.C ⥤ S.C :=
  restrict (frobenius D l hl Ω T₀ E) S.objects S.stable
end Domain

section Realization
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
  (E : Option (ConstructibleExceptionalCoefficients.FieldStage.{u} l))

/-- The existing tensor functor at the selected rational or common coefficient stage.
Source: def-weil-derived-pullback-tensor-hom, rational and common-stage formulas
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def tensorAt : CategoryAt l Ω (D.geometricFiber T₀).left E ×
      CategoryAt l Ω (D.geometricFiber T₀).left E ⥤
    CategoryAt l Ω (D.geometricFiber T₀).left E :=
  letI := fun z ↦ sfWeilPrimeInvertible D l hl T₀ z
  match E with
  | some E' => rationalDerivedTensor l E'.carrier (D.geometricFiber T₀).left
  | none => commonStageDerivedTensor l Ω (D.geometricFiber T₀).left

/-- The actual permitted pairs for the recorded partial internal Hom.
Source: def-weil-derived-pullback-tensor-hom, permitted-pair restriction
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def homPairsAt : ObjectProperty
    ((CategoryAt l Ω (D.geometricFiber T₀).left E)ᵒᵖ ×
      CategoryAt l Ω (D.geometricFiber T₀).left E) :=
  match E with
  | some E' => constructibleRationalHomPairs l E'.carrier (D.geometricFiber T₀).left
  | none => commonStageHomPairs l Ω (D.geometricFiber T₀).left

/-- The recorded internal Hom on its permitted pairs, rather than a new Hom construction.
Source: def-weil-derived-pullback-tensor-hom, rational and common-stage formulas
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def homAt : (homPairsAt D l Ω T₀ E).FullSubcategory ⥤
    CategoryAt l Ω (D.geometricFiber T₀).left E :=
  match E with
  | some E' => rationalDerivedInternalHom l E'.carrier (D.geometricFiber T₀).left
  | none => commonStageDerivedInternalHom l Ω (D.geometricFiber T₀).left

/-- Include the supplied Hom inputs in the recorded permitted-pair domain.
Source: prop-weil-operations, closure under the displayed composites
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def homInputs (S : Domain D l hl Ω T₀ E)
    (permitted : ∀ K L : S.C, homPairsAt D l Ω T₀ E (op K.obj, L.obj)) :
    S.Cᵒᵖ × S.C ⥤ (homPairsAt D l Ω T₀ E).FullSubcategory :=
  (homPairsAt D l Ω T₀ E).lift (S.objects.ι.op.prod S.objects.ι)
    (fun K ↦ permitted K.1.unop K.2)

/-- The supplied tensor and Hom really restrict the recorded derived operations.
The comparison isomorphisms are supplied endpoint identifications on full domains;
their data do not come from existence choices or postponed proofs.
Source: prop-weil-operations, supplied-domain and canonical-operation hypotheses
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
structure Realizes (S : Domain D l hl Ω T₀ E) (d : TensorHomData S.phi) where
  tensor : Functor.uncurry.obj d.tensor ⋙ S.objects.ι ≅
    S.objects.ι.prod S.objects.ι ⋙ tensorAt D l hl Ω T₀ E
  permitted : ∀ K L : S.C, homPairsAt D l Ω T₀ E (op K.obj, L.obj)
  hom : Functor.uncurry.obj d.hom ⋙ S.objects.ι ≅
    homInputs D l hl Ω T₀ E S permitted ⋙ homAt D l Ω T₀ E
end Realization

/-- Pullback along the actual geometric fibre of f_0, at the selected coefficient stage.
Source: def-weil-derived-pullback-tensor-hom, rational and common-stage formulas
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def geometricPullback (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀)
    (E : Option (ConstructibleExceptionalCoefficients.FieldStage.{u} l)) :
    CategoryAt l Ω (D.geometricFiber Y₀).left E ⥤
      CategoryAt l Ω (D.geometricFiber X₀).left E :=
  letI := fun z ↦ sfWeilPrimeInvertible D l hl X₀ z
  letI := fun z ↦ sfWeilPrimeInvertible D l hl Y₀ z
  match E with
  | some E' => rationalDerivedPullback l E'.carrier
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left)
  | none => commonStageDerivedPullback l Ω
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left)

/-- Projection--evaluation pairing and the exceptional, tensor--Hom and ordinary
transposes on a supplied rational/common-stage domain. `W` is the supplied canonical
Weil pair omega_Y = Ra_Y^! Lambda_s. The assertion is formal in this fixed pair;
it neither constructs nor postulates an ambient exceptional adjoint.
Source: prop-weil-operations, evaluation and adjunction construction of the formal
Verdier exchange (blueprint: lem-pod-verdier-pairing-three-transposes).

Proof:
1. The fixed-pair arrow condition gives closure under composition by functoriality;
   conjugating the same square by the inverses gives the inverse-arrow equation.
2. For K, the opposite-variable lift uses theta_K inverse. Hence the dual structure
   is h_K followed by Hom(theta_K inverse,theta_omega). Evaluation naturality in
   both variables and evaluation compatibility of h_K show that evaluation is a
   Weil arrow. This is the counit, in the K tensor D(K) order.
3. If another structure makes evaluation equivariant, cancel the tensor comparison
   and theta_K. The resulting equal uncurries imply equality by injectivity of the
   tensor--Hom adjunction: its inverse Hom equivalence sends a map to tensoring
   that map followed by the counit. No perfectness or nondegeneracy is needed.
4. Take K = FM. The inverse of the specified equivariant projection is equivariant
   by Step 1, so its composite with evaluation is the Weil arrow b.
5. Transpose b successively through the three supplied lifted adjunctions.
   The unit normalizations identify the underlying maps with G(b) after eta!,
   H_M(t) after nu, and Q(r) after eta*. These are the same adjunction transposes
   by lem-weil-pbc-adjunct-counit-identity, Adjunction.eq_unit_comp_map_iff.
6. Everything is an equation in the underlying rational/common-stage category.
   The same argument applies to both cases of CategoryAt. No integral lattice,
   scalar reduction of a rational inverse, or finite-Tor condition is used.
-/
theorem verdier_pairing_three_transposes
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (E : Option (ConstructibleExceptionalCoefficients.FieldStage.{u} l))
    (_embedding : ∀ E' ∈ E, E'.carrier →ₐ[Padic l] Ω)
    (SX : Domain D l hl Ω X₀ E) (SY : Domain D l hl Ω Y₀ E)
    {B : Type v} [Category.{vB} B]
    (d : CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage
      (DX := SX.C) (DB := B) (DY := SY.C) (DX' := SX.C) (DB' := B) (DY' := SY.C))
    (_pullback : d.pull ⋙ SX.objects.ι ≅
      SY.objects.ι ⋙ geometricPullback D l hl Ω X₀ Y₀ f₀ E)
    (x : TensorHomData SX.phi) (y : ClosedData SY.phi)
    (_x_realizes : Realizes D l hl Ω X₀ E SX x)
    (_y_realizes : Realizes D l hl Ω Y₀ E SY y.toTensorHomData)
    (_tensorX : d.tensorX = x.tensor) (_tensorY : d.tensorY = y.tensor)
    (G : SY.C ⥤ SX.C) (Q : SX.C ⥤ SY.C)
    (e : LiftedAdjunction SX.phi SY.phi d.compactSupport G)
    (o : LiftedAdjunction SY.phi SX.phi d.pull Q)
    (W : IsoAlgebra SY.phi) :
    EvaluationAssertion y W ∧
      TransposeAssertion SX.phi SY.phi d x y G Q e o W ∧
      ArrowLaws SX.phi ∧ ArrowLaws SY.phi := by
  exact ⟨evaluation_assertion y W,
    transpose_assertion SX.phi SY.phi d x y G Q e o W,
    arrow_laws SX.phi, arrow_laws SY.phi⟩

end WeilConjectures.VerdierPairing
