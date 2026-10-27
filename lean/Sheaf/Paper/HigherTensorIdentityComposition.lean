/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T7
-/
module

public import Sheaf.Paper.CommonProjectionPullbackTensorCompatibility
public import Sheaf.Paper.ConstructibleProjectionMates
import Sheaf.Paper.IntegralSystemReductionFullyFaithful
import Sheaf.Paper.IntegralDatumPullCompositionReduction
import Sheaf.Paper.IntegralProperTensorPullbackReduction
import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
import Sheaf.SixFunctors.IntegralSystemTensorComposition
import Sheaf.Paper.RationalProjectionTensorModels
import Mathlib.Algebra.CharP.CharAndCard

/-! # Composition of the higher tensor comparisons at identity

Source: composition clause of lem-pur-derived-pullback-tensor-iso, transported
through the recorded operation normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
namespace WeilConjectures

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

@[reducible] private def identityCompositor {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type*} [∀ X, Category (B X)]
    (P : SixFunctorPushStage D B) (X : SixFunctorSpace D) :
    P.pull (𝟙 X) ≅ P.pull (𝟙 X) ⋙ P.pull (𝟙 X) :=
  eqToIso (congrArg (fun f ↦ P.pull f) (Category.id_comp (𝟙 X)).symm) ≪≫
    P.pullComposition (𝟙 X) (𝟙 X)

@[reducible] private def uncurryComparison {A : Type*} [Category A]
    (U : A ⥤ A) (T : A ⥤ A ⥤ A)
    (μ : (Functor.postcompose₂.obj U).obj T ≅
      (((Functor.whiskeringLeft₂ A).obj U).obj U).obj T) :
    Functor.uncurry.obj T ⋙ U ≅ U.prod U ⋙ Functor.uncurry.obj T :=
  NatIso.ofComponents (fun p ↦ (μ.app p.1).app p.2) (by
    rintro ⟨M, L⟩ ⟨M', L'⟩ ⟨a, b⟩
    have h := (Functor.uncurry.mapIso μ).hom.naturality (Prod.mkHom a b)
    change (U.map ((T.map a).app L) ≫ U.map ((T.obj M').map b)) ≫
        (μ.hom.app M').app L' =
      (μ.hom.app M).app L ≫
        ((T.map (U.map a)).app (U.obj L) ≫ (T.obj (U.obj M')).map (U.map b)) at h
    simpa only [Functor.uncurry_obj_map, Functor.comp_map, Functor.prod_map,
      Functor.map_comp, Category.assoc, Iso.app_hom, Functor.prod_obj] using h)

private theorem identityCompositor_app_hom
    {B : SixFunctorSpace D → Type*} [∀ X, Category (B X)]
    (P : SixFunctorPushStage D B) (X : SixFunctorSpace D) (M : B X) :
    (identityCompositor P X).hom.app M =
      (eqToIso (congrArg (fun f ↦ (P.pull f).obj M)
        (Category.id_comp (𝟙 X)).symm) ≪≫
        (P.pullComposition (𝟙 X) (𝟙 X)).app M).hom := by
  simp only [identityCompositor, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, Iso.app_hom]

private theorem curriedComparison_hom_app
    {A B : Type*} [Category* A] [Category* B]
    (R : A ⥤ B) (T : A ⥤ A ⥤ A) (W : B ⥤ B ⥤ B)
    (t : Functor.uncurry.obj T ⋙ R ≅ R.prod R ⋙ Functor.uncurry.obj W) (M L : A) :
    ((projectionCurriedTensorComparison R T W t).hom.app M).app L =
      t.hom.app (M, L) := by
  unfold projectionCurriedTensorComparison
  rfl

private theorem identity_tensor_raw
    {B : SixFunctorSpace D → Type*} [∀ X, Category (B X)]
    (P : SixFunctorPushStage D B) (X : SixFunctorSpace D) (T : B X ⥤ B X ⥤ B X)
    (μ : (Functor.postcompose₂.obj (P.pull (𝟙 X))).obj T ≅
      (((Functor.whiskeringLeft₂ (B X)).obj (P.pull (𝟙 X))).obj
        (P.pull (𝟙 X))).obj T)
    (h : let U := P.pull (𝟙 X)
      let W := Functor.uncurry.obj T
      let m := uncurryComparison U T μ
      let c := identityCompositor P X
      ∀ M L, m.hom.app (M, L) ≫ W.map (Prod.mkHom (c.hom.app M) (c.hom.app L)) =
        c.hom.app (W.obj (M, L)) ≫ U.map (m.hom.app (M, L)) ≫
          m.hom.app (U.obj M, U.obj L)) :
    let U := P.pull (𝟙 X)
    let W := Functor.uncurry.obj T
    let m := fun M L ↦ (μ.hom.app M).app L
    let c : ∀ M, U.obj M ≅ U.obj (U.obj M) := fun M ↦
      eqToIso (congrArg (fun f ↦ (P.pull f).obj M) (Category.id_comp (𝟙 X)).symm) ≪≫
        (P.pullComposition (𝟙 X) (𝟙 X)).app M
    ∀ M L, m M L ≫ W.map (Prod.mkHom (c M).hom (c L).hom) =
      (c (W.obj (M, L))).hom ≫ U.map (m M L) ≫ m (U.obj M) (U.obj L) := by
  dsimp only
  intro M L
  have hh := h M L
  change (μ.hom.app M).app L ≫ (Functor.uncurry.obj T).map
      (Prod.mkHom ((identityCompositor P X).hom.app M)
        ((identityCompositor P X).hom.app L)) =
    (identityCompositor P X).hom.app ((Functor.uncurry.obj T).obj (M, L)) ≫
      (P.pull (𝟙 X)).map ((μ.hom.app M).app L) ≫
      (μ.hom.app ((P.pull (𝟙 X)).obj M)).app ((P.pull (𝟙 X)).obj L) at hh
  simpa only [identityCompositor_app_hom] using hh

private theorem identityComparison_comp
    {A B I : Type*} [Category A] [Category B]
    (R : A ⥤ B) (F : I → A ⥤ A) (G : I → B ⥤ B)
    (p : ∀ i, F i ⋙ R ≅ R ⋙ G i)
    {i j : I} (e : i = j) (c : F i ≅ F j ⋙ F j) (d : G i ≅ G j ⋙ G j)
    (h : ∀ M, R.map (c.hom.app M) ≫ (p j).hom.app ((F j).obj M) ≫
      (G j).map ((p j).hom.app M) = (p i).hom.app M ≫ d.hom.app (R.obj M))
    (M : A) :
    R.map ((eqToIso (congrArg F e.symm) ≪≫ c).hom.app M) ≫
        (p j).hom.app ((F j).obj M) ≫ (G j).map ((p j).hom.app M) =
      (p j).hom.app M ≫ (eqToIso (congrArg G e.symm) ≪≫ d).hom.app (R.obj M) := by
  cases e
  simpa using h M

private theorem identity_tensor_transport
    {A I : Type*} [Category A] (T : A × A ⥤ A)
    (F : I → A ⥤ A) (μ : ∀ i, T ⋙ F i ≅ (F i).prod (F i) ⋙ T)
    {i j : I} (e : i = j) (c : F i ≅ F j ⋙ F j)
    (h : ∀ M L, (μ i).hom.app (M, L) ≫
      T.map (Prod.mkHom (c.hom.app M) (c.hom.app L)) =
      c.hom.app (T.obj (M, L)) ≫ (F j).map ((μ j).hom.app (M, L)) ≫
        (μ j).hom.app ((F j).obj M, (F j).obj L)) (M L : A) :
    (μ j).hom.app (M, L) ≫
        T.map (Prod.mkHom ((eqToIso (congrArg F e.symm) ≪≫ c).hom.app M)
          ((eqToIso (congrArg F e.symm) ≪≫ c).hom.app L)) =
      (eqToIso (congrArg F e.symm) ≪≫ c).hom.app (T.obj (M, L)) ≫
        (F j).map ((μ j).hom.app (M, L)) ≫
        (μ j).hom.app ((F j).obj M, (F j).obj L) := by
  cases e
  simpa using h M L

private theorem tensor_composition_of_iso
    {A : Type*} [Category A] (U : A ⥤ A) (T : A × A ⥤ A)
    (μ : T ⋙ U ≅ U.prod U ⋙ T) (c : U ≅ U ⋙ U)
    {M L M' L' : A} (e : M ≅ M') (f : L ≅ L')
    (h : μ.hom.app (M, L) ≫ T.map (Prod.mkHom (c.hom.app M) (c.hom.app L)) =
      c.hom.app (T.obj (M, L)) ≫ U.map (μ.hom.app (M, L)) ≫
        μ.hom.app (U.obj M, U.obj L)) :
    μ.hom.app (M', L') ≫ T.map (Prod.mkHom (c.hom.app M') (c.hom.app L')) =
      c.hom.app (T.obj (M', L')) ≫ U.map (μ.hom.app (M', L')) ≫
        μ.hom.app (U.obj M', U.obj L') := by
  let lhs : T ⋙ U ⟶ (U ⋙ U).prod (U ⋙ U) ⋙ T :=
    μ.hom ≫ Functor.whiskerRight (NatTrans.prod c.hom c.hom) T
  let rhs : T ⋙ U ⟶ (U ⋙ U).prod (U ⋙ U) ⋙ T :=
    Functor.whiskerLeft T c.hom ≫ Functor.whiskerRight μ.hom U ≫
      Functor.whiskerLeft (U.prod U) μ.hom
  have hl := lhs.naturality (Prod.mkHom e.hom f.hom)
  have hr := rhs.naturality (Prod.mkHom e.hom f.hom)
  have hh : lhs.app (M, L) = rhs.app (M, L) := h
  have he : lhs.app (M', L') = rhs.app (M', L') := by
    let : IsIso (Prod.mkHom e.hom f.hom) := by
      change IsIso (e.prod f).hom
      infer_instance
    apply (cancel_epi ((T ⋙ U).map (Prod.mkHom e.hom f.hom))).1
    rw [hl, hr, hh]
  exact he

private theorem pair_map_comp {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ B) {P Q R P' Q' R' : A}
    (f : P ⟶ Q) (g : P' ⟶ Q') (h : Q ⟶ R) (k : Q' ⟶ R') :
    T.map (Prod.mkHom f g) ≫ T.map (Prod.mkHom h k) =
      T.map (Prod.mkHom (f ≫ h) (g ≫ k)) := by
  rw [← T.map_comp]
  rfl

private theorem tensor_inverse_square
    {A : Type*} [Category A] (W : A × A ⥤ A)
    {P P' Q Q' B B' : A} (p : P ≅ P') (q : Q ≅ Q') (r : B ≅ B')
    (a : B ⟶ W.obj (P, Q)) (b : B' ⟶ W.obj (P', Q'))
    (h : b ≫ W.map (Prod.mkHom p.inv (𝟙 Q')) ≫
      W.map (Prod.mkHom (𝟙 P) q.inv) = r.inv ≫ a) :
    a ≫ W.map (Prod.mkHom p.hom q.hom) = r.hom ≫ b := by
  have h' := congrArg (fun k ↦ r.hom ≫ k ≫ W.map (Prod.mkHom p.hom q.hom)) h
  simpa only [Category.assoc, ← W.map_comp, prod_comp, Category.id_comp,
    Category.comp_id, Iso.inv_hom_id, Iso.hom_inv_id_assoc, ← prod_id,
    W.map_id] using h'.symm

private theorem tensor_forward_square
    {A : Type*} [Category A] (W : A × A ⥤ A)
    {P P' Q Q' B : A} (p : P ≅ P') (q : Q ≅ Q')
    (a : B ⟶ W.obj (P, Q)) (b : B ⟶ W.obj (P', Q'))
    (h : a = b ≫ W.map (Prod.mkHom p.inv (𝟙 Q')) ≫
      W.map (Prod.mkHom (𝟙 P) q.inv)) :
    a ≫ W.map (Prod.mkHom p.hom q.hom) = b := by
  have h' := congrArg (fun k ↦ k ≫ W.map (Prod.mkHom p.hom q.hom)) h
  simpa only [Category.assoc, ← W.map_comp, prod_comp, Category.id_comp,
    Category.comp_id, Iso.inv_hom_id, ← prod_id, W.map_id] using h'

private theorem tensor_comparison_compatible
    {A B : Type*} [Category* A] [Category* B]
    (R : A ⥤ B) (U : A ⥤ A) (V : B ⥤ B)
    (T : A ⥤ A ⥤ A) (W : B ⥤ B ⥤ B)
    (μ : (Functor.postcompose₂.obj U).obj T ≅
      (((Functor.whiskeringLeft₂ A).obj U).obj U).obj T)
    (ν : (Functor.postcompose₂.obj V).obj W ≅
      (((Functor.whiskeringLeft₂ B).obj V).obj V).obj W)
    (p : U ⋙ R ≅ R ⋙ V)
    (t : Functor.uncurry.obj T ⋙ R ≅ R.prod R ⋙ Functor.uncurry.obj W)
    (h : Adjunction.ComparisonCompatible p.symm μ.hom ν.hom
      (projectionCurriedTensorComparison R T W t)
      (projectionCurriedTensorComparison R T W t)) (M L : A) :
    R.map ((uncurryComparison U T μ).hom.app (M, L)) ≫
        t.hom.app (U.obj M, U.obj L) ≫
          (Functor.uncurry.obj W).map (Prod.mkHom (p.hom.app M) (p.hom.app L)) =
      p.hom.app ((Functor.uncurry.obj T).obj (M, L)) ≫ V.map (t.hom.app (M, L)) ≫
        (uncurryComparison V W ν).hom.app (R.obj M, R.obj L) := by
  change R.map ((μ.hom.app M).app L) ≫ t.hom.app (U.obj M, U.obj L) ≫
      (Functor.uncurry.obj W).map (Prod.mkHom (p.hom.app M) (p.hom.app L)) =
    p.hom.app ((T.obj M).obj L) ≫ V.map (t.hom.app (M, L)) ≫
      (ν.hom.app (R.obj M)).app (R.obj L)
  have hi := h M L
  simp only [curriedComparison_hom_app, Iso.symm_inv, Iso.symm_hom] at hi
  simpa only [Category.assoc, Iso.app_hom, Functor.comp_obj] using
    tensor_forward_square (Functor.uncurry.obj W) (p.app M) (p.app L)
      (R.map ((μ.hom.app M).app L) ≫ t.hom.app (U.obj M, U.obj L))
      (p.hom.app ((T.obj M).obj L) ≫ V.map (t.hom.app (M, L)) ≫
        (ν.hom.app (R.obj M)).app (R.obj L))
      (by simpa [Category.assoc, Functor.uncurry_obj_map] using hi)

private theorem tensor_composition_compare
    {A B : Type*} [Category A] [Category B]
    (R : A ⥤ B) (U : A ⥤ A) (V : B ⥤ B)
    (T : A × A ⥤ A) (W : B × B ⥤ B)
    (μ : T ⋙ U ≅ U.prod U ⋙ T) (ν : W ⋙ V ≅ V.prod V ⋙ W)
    (c : ∀ M, U.obj M ≅ U.obj (U.obj M))
    (d : V ≅ V ⋙ V)
    (p : U ⋙ R ≅ R ⋙ V) (t : T ⋙ R ≅ R.prod R ⋙ W)
    (hc : ∀ M, R.map (c M).hom ≫ p.hom.app (U.obj M) ≫ V.map (p.hom.app M) =
      p.hom.app M ≫ d.hom.app (R.obj M))
    (hμ : ∀ M L, R.map (μ.hom.app (M, L)) ≫ t.hom.app (U.obj M, U.obj L) ≫
      W.map (Prod.mkHom (p.hom.app M) (p.hom.app L)) =
      p.hom.app (T.obj (M, L)) ≫ V.map (t.hom.app (M, L)) ≫
        ν.hom.app (R.obj M, R.obj L))
    (M L : A) :
    (R.map (μ.hom.app (M, L) ≫ T.map (Prod.mkHom (c M).hom (c L).hom)) =
      R.map ((c (T.obj (M, L))).hom ≫ U.map (μ.hom.app (M, L)) ≫
        μ.hom.app (U.obj M, U.obj L))) ↔
    (ν.hom.app (R.obj M, R.obj L) ≫
        W.map (Prod.mkHom (d.hom.app (R.obj M)) (d.hom.app (R.obj L))) =
      d.hom.app (W.obj (R.obj M, R.obj L)) ≫
        V.map (ν.hom.app (R.obj M, R.obj L)) ≫
        ν.hom.app (V.obj (R.obj M), V.obj (R.obj L))) := by
  let : IsIso (Prod.mkHom (p.hom.app (U.obj M)) (p.hom.app (U.obj L))) := by
    change IsIso ((p.app (U.obj M)).prod (p.app (U.obj L))).hom
    infer_instance
  let : IsIso (Prod.mkHom (V.map (p.hom.app M)) (V.map (p.hom.app L))) := by
    change IsIso ((V.mapIso (p.app M)).prod (V.mapIso (p.app L))).hom
    infer_instance
  let post := t.hom.app (U.obj (U.obj M), U.obj (U.obj L)) ≫
    W.map (Prod.mkHom (p.hom.app (U.obj M)) (p.hom.app (U.obj L))) ≫
    W.map (Prod.mkHom (V.map (p.hom.app M)) (V.map (p.hom.app L)))
  let pre := p.hom.app (T.obj (M, L)) ≫ V.map (t.hom.app (M, L))
  let tail := V.map (V.map (t.hom.app (M, L)))
  have hl : R.map (μ.hom.app (M, L) ≫ T.map (Prod.mkHom (c M).hom (c L).hom)) ≫
      post = pre ≫ ν.hom.app (R.obj M, R.obj L) ≫
        W.map (Prod.mkHom (d.hom.app (R.obj M)) (d.hom.app (R.obj L))) := by
    dsimp only [post, pre]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% (t.hom.naturality (Prod.mkHom (c M).hom (c L).hom))]
    dsimp only [Functor.comp_map, Functor.prod_map]
    rw [pair_map_comp, pair_map_comp, hc M, hc L, ← pair_map_comp]
    rw [reassoc_of% (hμ M L)]
  have hr : R.map ((c (T.obj (M, L))).hom ≫ U.map (μ.hom.app (M, L)) ≫
      μ.hom.app (U.obj M, U.obj L)) ≫ post =
      pre ≫ d.hom.app (W.obj (R.obj M, R.obj L)) ≫
        V.map (ν.hom.app (R.obj M, R.obj L)) ≫
        ν.hom.app (V.obj (R.obj M), V.obj (R.obj L)) := by
    dsimp only [post, pre]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% (hμ (U.obj M) (U.obj L))]
    have hp := p.hom.naturality (μ.hom.app (M, L))
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.prod_obj] at hp
    rw [reassoc_of% hp]
    have hn := ν.hom.naturality (Prod.mkHom (p.hom.app M) (p.hom.app L))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj,
      Functor.prod_obj] at hn
    rw [← hn]
    rw [← V.map_comp_assoc, ← V.map_comp_assoc]
    simp only [Category.assoc]
    rw [hμ]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% (hc (T.obj (M, L)))]
    -- The compositor is natural along the tensor comparison.
    have hdn : d.hom.app (R.obj (T.obj (M, L))) ≫ tail =
        V.map (t.hom.app (M, L)) ≫
          d.hom.app (W.obj (R.obj M, R.obj L)) := by
      exact (d.hom.naturality (t.hom.app (M, L))).symm
    rw [reassoc_of% hdn]
  exact ⟨fun h ↦ (cancel_epi pre).1 (hl.symm.trans
      ((congrArg (fun a ↦ a ≫ post) h).trans hr)),
    fun h ↦ (cancel_mono post).1 (hl.trans ((congrArg (fun a ↦ pre ≫ a) h).trans hr.symm))⟩

private theorem transported_component
    {A B : Type*} [Category A] [Category B]
    {F F' G G' : A ⥤ A ⥤ B} (hF : F = F') (hG : G' = G)
    (e : F' ≅ G') (M N : A) :
    HEq (((eqToIso hF ≪≫ e ≪≫ eqToIso hG).hom.app M).app N)
      ((e.hom.app M).app N) := by
  subst F' G'
  simp

private theorem transport_comparison_heq
    {A B : Type*} [Category A] [Category B]
    {F F' : A ⥤ B} {T T' : B ⥤ B ⥤ B} {W W' : A ⥤ A ⥤ A}
    (hF : F = F') (hT : T = T') (hW : W = W')
    (μ : (Functor.postcompose₂.obj F).obj W ≅
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj T) (M L : A) :
    HEq (((projectionTransportTensorComparison hF hT hW μ).hom.app M).app L)
      ((μ.hom.app M).app L) := by
  subst F' T' W'
  rfl

private theorem projectionPullbackTensor_heq
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type*} [∀ X, Category (B X)]
    {P : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (A : SixFunctorExchangeData P T Q)
    (M L : B Q.Y) :
    HEq (((projectionPullbackTensor A).hom.app M).app L)
      ((A.stage.tensorPullback.hom.app M).app L) := by
  unfold projectionPullbackTensor
  exact transport_comparison_heq A.properPull A.tensorBar A.tensorY
    A.stage.tensorPullback M L

-- Compare functors through their APIs without expanding derived-category implementations.
attribute [local irreducible] HasDerivedCategory.standard DerivedCategory
  instCategoryDerivedCategory

private theorem integral_reduction_faithful (X : SixFunctorSpace D)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)] :
    (IntegralProjectionReduction.ProperCoordinates.reduce (C := C) (E := E) X).Faithful := by
  exact (integralSystemReduction_fullyFaithful C.l E X.obj.left).2

-- The preceding bridge identifies the two system-category presentations before hiding this data.
attribute [local irreducible] CategoryTheory.constantSheaf
  Scheme.residueField integralDerivedPullback integralCompletedTensor pullbackTensorCalculus
  SheafOfModules.instAbelian
  pullbackTensorSequenceDerived pullbackTensorSequenceInverse pullbackTensorSystemComparison

private theorem integral_tensor_composition (S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) [IsProper (𝟙 X : X ⟶ X).hom.left] :
    let U := S.higher.integral.pull (𝟙 X)
    let T := Functor.uncurry.obj (S.higher.integralTensor X)
    let μ := uncurryComparison U (S.higher.integralTensor X)
      (projectionPullbackTensor (S.higher.integralExchange
        (compactSupportProperSquare (𝟙 X : X ⟶ X))))
    let c := identityCompositor S.higher.integral X
    ∀ M L, μ.hom.app (M, L) ≫ T.map (Prod.mkHom (c.hom.app M) (c.hom.app L)) =
      c.hom.app (T.obj (M, L)) ≫ U.map (μ.hom.app (M, L)) ≫
        μ.hom.app (U.obj M, U.obj L) := by
  let hl : IsUnit (C.l : D.k) := by
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
    exact isUnit_iff_ne_zero.mpr
      (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : C.l.Prime) C.different.symm)
  let hz := IntegralSystemRealization.integralCompactificationSystemRealization
    C.l E D C.different
  let o := hz.choose
  let z := Classical.choice hz.choose_spec
  let R := IntegralProjectionReduction.ProperCoordinates.reduce (C := C) (E := E) X
  let U := S.higher.integral.pull (𝟙 X)
  let V := IntegralSystemRealization.pull C.l E ((𝟙 X : X ⟶ X).hom.left)
  let T := Functor.uncurry.obj (S.higher.integralTensor X)
  let W := (IntegralSystemRealization.calculus C.l E X.obj.left).systemClosed.tensor
  let μ := uncurryComparison U (S.higher.integralTensor X)
    (projectionPullbackTensor (S.higher.integralExchange
      (compactSupportProperSquare (𝟙 X : X ⟶ X))))
  let ν := pullbackTensorSystemComparison C.l E ((𝟙 X : X ⟶ X).hom.left)
  let c := identityCompositor S.higher.integral X
  let G := fun f : X ⟶ X ↦ IntegralSystemRealization.pull C.l E f.hom.left
  let d : V ≅ V ⋙ V :=
    eqToIso (congrArg G (Category.id_comp (𝟙 X)).symm) ≪≫
      z.compositors.pullComp ((𝟙 X : X ⟶ X).hom.left) ((𝟙 X : X ⟶ X).hom.left)
  let p : U ⋙ R ≅ R ⋙ V :=
    IntegralProjectionReduction.ProperCoordinates.pullComparison S.higher hl o z (𝟙 X)
  let t : T ⋙ R ≅ R.prod R ⋙ W :=
    FixProjectionCompactification.Coordinates.datumTensorReductionIso D C E S.higher hl X
  let := FixProjectionCompactification.Coordinates.residueUnits hl X
  let : R.Faithful := integral_reduction_faithful X
  have hc (M) : R.map (c.hom.app M) ≫ p.hom.app (U.obj M) ≫ V.map (p.hom.app M) =
      p.hom.app M ≫ d.hom.app (R.obj M) := by
    exact identityComparison_comp R (fun f : X ⟶ X ↦ S.higher.integral.pull f) G
      (fun f ↦ IntegralProjectionReduction.ProperCoordinates.pullComparison S.higher hl o z f)
      (Category.id_comp (𝟙 X)) (S.higher.integral.pullComposition (𝟙 X) (𝟙 X))
      (z.compositors.pullComp ((𝟙 X : X ⟶ X).hom.left) ((𝟙 X : X ⟶ X).hom.left))
      (fun K ↦ IntegralProjectionReduction.OpenCoordinates.integralDatumPullCompositionReduction
        C E n hn S hl o z (𝟙 X) (𝟙 X) K) M
  have hμ (M L) : R.map (μ.hom.app (M, L)) ≫ t.hom.app (U.obj M, U.obj L) ≫
      W.map (Prod.mkHom (p.hom.app M) (p.hom.app L)) =
      p.hom.app (T.obj (M, L)) ≫ V.map (t.hom.app (M, L)) ≫
        ν.hom.app (R.obj M, R.obj L) := by
    have hp : ∀ A B,
        (((IntegralProjectionReduction.ProperCoordinates.pullTensor S.higher (𝟙 X)).hom.app
          A).app B) = ((projectionPullbackTensor (S.higher.integralExchange
            (compactSupportProperSquare (𝟙 X : X ⟶ X)))).hom.app A).app B := by
      intro A B
      exact eq_of_heq ((transported_component _ _
        (S.higher.integralExchange (compactSupportProperSquare (𝟙 X : X ⟶ X))).stage.tensorPullback
        A B).trans (projectionPullbackTensor_heq
          (S.higher.integralExchange (compactSupportProperSquare (𝟙 X : X ⟶ X)))
          A B).symm)
    have h := IntegralProjectionReduction.integralProperTensorPullbackReduction
      S.higher hl o z (𝟙 X) M L
    simp only [Functor.curryObj, Functor.curry, Functor.curryObjProdComp,
      Iso.trans_hom, NatTrans.comp_app, NatIso.ofComponents_hom_app, Iso.refl_hom,
      Functor.mapIso_hom, Category.comp_id] at h
    change V.map (t.hom.app (M, L)) ≫ ν.hom.app (R.obj M, R.obj L) ≫
        W.map (Prod.mkHom (p.inv.app M) (𝟙 _)) ≫
        W.map (Prod.mkHom (𝟙 _) (p.inv.app L)) =
      p.inv.app (T.obj (M, L)) ≫
        R.map (((IntegralProjectionReduction.ProperCoordinates.pullTensor
          S.higher (𝟙 X)).hom.app M).app L) ≫ t.hom.app (U.obj M, U.obj L) at h
    have hf := tensor_inverse_square W (p.app M) (p.app L) (p.app (T.obj (M, L)))
      (R.map (((IntegralProjectionReduction.ProperCoordinates.pullTensor
        S.higher (𝟙 X)).hom.app M).app L) ≫ t.hom.app (U.obj M, U.obj L))
      (V.map (t.hom.app (M, L)) ≫ ν.hom.app (R.obj M, R.obj L))
      (by simpa only [Category.assoc, Iso.app_inv, Iso.app_hom, V, T, R,
        IntegralSystemRealization.pull, Functor.comp_obj] using h)
    exact (congrArg (fun a ↦ R.map a ≫ t.hom.app (U.obj M, U.obj L) ≫
      W.map (Prod.mkHom (p.hom.app M) (p.hom.app L))) (hp M L)).symm.trans
        (by simpa only [Category.assoc, Iso.app_hom, Functor.comp_obj] using hf)
  have hd (M L) : ν.hom.app (M, L) ≫
      W.map (Prod.mkHom (d.hom.app M) (d.hom.app L)) =
      d.hom.app (W.obj (M, L)) ≫ V.map (ν.hom.app (M, L)) ≫
        ν.hom.app (V.obj M, V.obj L) := by
    exact identity_tensor_transport W G
      (fun f ↦ pullbackTensorSystemComparison C.l E f.hom.left)
      (Category.id_comp (𝟙 X))
      (z.compositors.pullComp ((𝟙 X : X ⟶ X).hom.left) ((𝟙 X : X ⟶ X).hom.left))
      (fun A B ↦ (IntegralSystemRealization.integralSystemTensorComposition C.l E
        o z.compositors ((𝟙 X : X ⟶ X).hom.left) ((𝟙 X : X ⟶ X).hom.left) A B).symm) M L
  change ∀ M L, μ.hom.app (M, L) ≫
    T.map (Prod.mkHom (c.hom.app M) (c.hom.app L)) =
      c.hom.app (T.obj (M, L)) ≫ U.map (μ.hom.app (M, L)) ≫
        μ.hom.app (U.obj M, U.obj L)
  intro M L
  apply R.map_injective
  exact (tensor_composition_compare R U V T W μ ν (fun K ↦ c.app K) d p t hc hμ M L).2
    (hd (R.obj M) (R.obj L))

attribute [local irreducible] sfRationalTriangulationDatum ScalarLocalization.composition
  ScalarLocalization.category

private theorem rational_tensor_composition (S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) [IsProper (𝟙 X : X ⟶ X).hom.left] :
    let U := S.higher.rational.pull (𝟙 X)
    let T := Functor.uncurry.obj (S.higher.rationalTensor X)
    let μ := uncurryComparison U (S.higher.rationalTensor X)
      (projectionPullbackTensor (S.higher.rationalExchange
        (compactSupportProperSquare (𝟙 X : X ⟶ X))))
    let c := identityCompositor S.higher.rational X
    ∀ M L, μ.hom.app (M, L) ≫ T.map (Prod.mkHom (c.hom.app M) (c.hom.app L)) =
      c.hom.app (T.obj (M, L)) ≫ U.map (μ.hom.app (M, L)) ≫
        μ.hom.app (U.obj M, U.obj L) := by
  let : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) :=
    fun x ↦ (sixFunctorSpace_coefficient_invertible C X x).some
  let : ∀ x : (compactSupportProperSquare (𝟙 X : X ⟶ X)).Z.obj.left,
      Invertible (C.l : (compactSupportProperSquare (𝟙 X : X ⟶ X)).Z.obj.left.residueField x) := by
    change ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)
    infer_instance
  let : ∀ x : (compactSupportProperSquare (𝟙 X : X ⟶ X)).Y.obj.left,
      Invertible (C.l : (compactSupportProperSquare (𝟙 X : X ⟶ X)).Y.obj.left.residueField x) := by
    change ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)
    infer_instance
  let R := sfRationalConstructibleLocalization C.l E X.obj.left
  let U := S.higher.integral.pull (𝟙 X)
  let V := S.higher.rational.pull (𝟙 X)
  let T := Functor.uncurry.obj (S.higher.integralTensor X)
  let W := Functor.uncurry.obj (S.higher.rationalTensor X)
  let μ := uncurryComparison U (S.higher.integralTensor X)
    (projectionPullbackTensor (S.higher.integralExchange
      (compactSupportProperSquare (𝟙 X : X ⟶ X))))
  let ν := uncurryComparison V (S.higher.rationalTensor X)
    (projectionPullbackTensor (S.higher.rationalExchange
      (compactSupportProperSquare (𝟙 X : X ⟶ X))))
  let c := identityCompositor S.higher.integral X
  let d := identityCompositor S.higher.rational X
  let p : U ⋙ R ≅ R ⋙ V := (S.higher.rationalization.directAdjunction (𝟙 X)).left
  let t : T ⋙ R ≅ R.prod R ⋙ W := rationalProjectionTensorComparison S.higher X
  have hc (M) : R.map (c.hom.app M) ≫ p.hom.app (U.obj M) ≫ V.map (p.hom.app M) =
      p.hom.app M ≫ d.hom.app (R.obj M) := by
    exact identityComparison_comp R (fun f : X ⟶ X ↦ S.higher.integral.pull f)
      (fun f ↦ S.higher.rational.pull f)
      (fun f ↦ (S.higher.rationalization.directAdjunction f).left)
      (Category.id_comp (𝟙 X)) (S.higher.integral.pullComposition (𝟙 X) (𝟙 X))
      (S.higher.rational.pullComposition (𝟙 X) (𝟙 X))
      (S.higher.rationalization.pullComposition (𝟙 X) (𝟙 X)) M
  have hμ (M L) : R.map (μ.hom.app (M, L)) ≫ t.hom.app (U.obj M, U.obj L) ≫
      W.map (Prod.mkHom (p.hom.app M) (p.hom.app L)) =
      p.hom.app (T.obj (M, L)) ≫ V.map (t.hom.app (M, L)) ≫
        ν.hom.app (R.obj M, R.obj L) := by
    exact rationalProjectionPullTensorSquare S.higher (𝟙 X)
      (projectionPullbackTensor (S.higher.integralExchange
        (compactSupportProperSquare (𝟙 X : X ⟶ X))))
      (projectionPullbackTensor (S.higher.rationalExchange
        (compactSupportProperSquare (𝟙 X : X ⟶ X)))) M L
      ((projectionPullbackTensor_heq
        (S.higher.integralExchange (compactSupportProperSquare (𝟙 X : X ⟶ X))) M L).trans
        (S.higher.integralTensorPullbackNormalization
          (compactSupportProperSquare (𝟙 X : X ⟶ X)) M L))
      ((projectionPullbackTensor_heq
        (S.higher.rationalExchange (compactSupportProperSquare (𝟙 X : X ⟶ X)))
        (R.obj M) (R.obj L)).trans
        (S.higher.rationalTensorPullbackNormalization
          (compactSupportProperSquare (𝟙 X : X ⟶ X)) (R.obj M) (R.obj L)))
  change ∀ M L, ν.hom.app (M, L) ≫
    W.map (Prod.mkHom (d.hom.app M) (d.hom.app L)) =
      d.hom.app (W.obj (M, L)) ≫ V.map (ν.hom.app (M, L)) ≫
        ν.hom.app (V.obj M, V.obj L)
  intro M L
  exact (tensor_composition_compare R U V T W μ ν (fun K ↦ c.app K) d p t hc hμ
    M.obj L.obj).1 (congrArg R.map (integral_tensor_composition S X M.obj L.obj))

-- Use the API of common-stage composition rather than its quotient implementation.
attribute [local irreducible] StageSystem.PairCategory.categoryStruct

private def coefficientDatum (S : SixFunctorOperationDatum D C E n hn)
    (F : Padic.FiniteCoefficientFields C.l C.Qbar) :
    SixFunctorOperationDatum D C
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) 1 (Nat.le_refl 1) :=
  { (S.coefficientIntegralNormalization F).finiteLevels 0 with
    higher := S.closure.coefficientStages F
    integralNormalization := S.coefficientIntegralNormalization F
    closure := S.closure
    coefficientIntegralNormalization := S.coefficientIntegralNormalization
    commonStageCoherence := S.commonStageCoherence }

private theorem coefficientDatum_higher (S : SixFunctorOperationDatum D C E n hn)
    (F : Padic.FiniteCoefficientFields C.l C.Qbar) :
    (coefficientDatum S F).higher = S.closure.coefficientStages F := rfl

attribute [local irreducible] coefficientDatum

private theorem common_tensor_composition (S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) [IsProper (𝟙 X : X ⟶ X).hom.left] :
    let U := S.closure.commonStage.pull (𝟙 X)
    let T := Functor.uncurry.obj (S.closure.commonStageTensor X)
    let μ := uncurryComparison U (S.closure.commonStageTensor X)
      (projectionPullbackTensor (S.closure.commonStageExchange
        (compactSupportProperSquare (𝟙 X : X ⟶ X))))
    let c := identityCompositor S.closure.commonStage X
    ∀ M L, μ.hom.app (M, L) ≫ T.map (Prod.mkHom (c.hom.app M) (c.hom.app L)) =
      c.hom.app (T.obj (M, L)) ≫ U.map (μ.hom.app (M, L)) ≫
        μ.hom.app (U.obj M, U.obj L) := by
  let V := S.closure.commonStage.pull (𝟙 X)
  let W := Functor.uncurry.obj (S.closure.commonStageTensor X)
  let ν := uncurryComparison V (S.closure.commonStageTensor X)
    (projectionPullbackTensor (S.closure.commonStageExchange
      (compactSupportProperSquare (𝟙 X : X ⟶ X))))
  let d := identityCompositor S.closure.commonStage X
  let J := fun F : Padic.FiniteCoefficientFields C.l C.Qbar ↦
    inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F
  have hstage (F : Padic.FiniteCoefficientFields C.l C.Qbar)
      (M L : Stage C.l C.Qbar X.obj.left F) :
      ν.hom.app (
        (J F).obj M,
          (J F).obj L) ≫
          W.map (Prod.mkHom (d.hom.app ((J F).obj M))
            (d.hom.app ((J F).obj L))) =
        d.hom.app (W.obj ((J F).obj M,
          (J F).obj L)) ≫
          V.map (ν.hom.app (
        (J F).obj M,
          (J F).obj L)) ≫
          ν.hom.app (
        V.obj ((J F).obj M), V.obj ((J F).obj L)) := by
    let H := S.closure.coefficientStages F
    let R := J F
    let U := H.rational.pull (𝟙 X)
    let T := Functor.uncurry.obj (H.rationalTensor X)
    let μ := uncurryComparison U (H.rationalTensor X)
      (projectionPullbackTensor (H.rationalExchange
        (compactSupportProperSquare (𝟙 X : X ⟶ X))))
    let c := identityCompositor H.rational X
    let p : U ⋙ R ≅ R ⋙ V := ((S.closure.commonStageComparison F).directAdjunction (𝟙 X)).left
    let t : T ⋙ R ≅ R.prod R ⋙ W := commonProjectionTensorComparison S.closure F X
    have hc (K) : R.map (c.hom.app K) ≫ p.hom.app (U.obj K) ≫ V.map (p.hom.app K) =
        p.hom.app K ≫ d.hom.app (R.obj K) := by
      exact identityComparison_comp R (fun f : X ⟶ X ↦ H.rational.pull f)
        (fun f ↦ S.closure.commonStage.pull f)
        (fun f ↦ ((S.closure.commonStageComparison F).directAdjunction f).left)
        (Category.id_comp (𝟙 X)) (H.rational.pullComposition (𝟙 X) (𝟙 X))
        (S.closure.commonStage.pullComposition (𝟙 X) (𝟙 X))
        ((S.closure.commonStageComparison F).pullComposition (𝟙 X) (𝟙 X)) K
    have hμ (K N) : R.map (μ.hom.app (K, N)) ≫ t.hom.app (U.obj K, U.obj N) ≫
        W.map (Prod.mkHom (p.hom.app K) (p.hom.app N)) =
        p.hom.app (T.obj (K, N)) ≫ V.map (t.hom.app (K, N)) ≫
          ν.hom.app (R.obj K, R.obj N) := by
      apply tensor_comparison_compatible R U V (H.rationalTensor X)
        (S.closure.commonStageTensor X)
        (projectionPullbackTensor (H.rationalExchange
          (compactSupportProperSquare (𝟙 X : X ⟶ X))))
        (projectionPullbackTensor (S.closure.commonStageExchange
          (compactSupportProperSquare (𝟙 X : X ⟶ X)))) p t
      have h := commonProjectionPullbackTensorCompatibility S.closure F
        (compactSupportProperSquare (𝟙 X : X ⟶ X))
      unfold projectionTensorComparisonCompatible at h
      exact h
    have hr := rational_tensor_composition (coefficientDatum S F) X M L
    simp only [coefficientDatum_higher] at hr
    exact (tensor_composition_compare R U V T W μ ν (fun K ↦ c.app K) d p t hc hμ M L).1
      (congrArg R.map hr)
  change ∀ M L, ν.hom.app (M, L) ≫
    W.map (Prod.mkHom (d.hom.app M) (d.hom.app L)) =
      d.hom.app (W.obj (M, L)) ≫ V.map (ν.hom.app (M, L)) ≫
        ν.hom.app (V.obj M, V.obj L)
  intro M L
  obtain ⟨F, hM, hL⟩ := exists_ge_ge M.stage L.stage
  exact tensor_composition_of_iso V W ν d
    (M := (J F).obj (M.toStage hM)) (L := (J F).obj (L.toStage hL))
    (M' := M) (L' := L)
    ((stageSystem C.l C.Qbar X.obj.left).isoToStage M hM).symm
    ((stageSystem C.l C.Qbar X.obj.left).isoToStage L hL).symm
    (hstage F (M.toStage hM) (L.toStage hL))

/-- The twice-identity composition squares for the three higher tensor comparisons,
expressed in the supplied operation coordinates. These equations involve the
compositor and two tensor comparisons; they assert no compatibility of an
identity unit with tensor.

Source: composition clause of lem-pur-derived-pullback-tensor-iso; identity
paragraph of prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-higher-tensor-identity-composition).

Proof: the prime-to-characteristic coefficient convention makes the coefficient
prime invertible on X. In the integral square use integralPullback and
integralTensorNormalization
to identify functors, and integralTensorPullbackNormalization to identify the
comparison. Expand projectionTransportTensorComparison by substitution of the
recorded functor equalities; the HEq normalization then compares arrows with
these same endpoints, including their equality transports. The reduction
comparison of integralNormalization is the prescribed
projection-adjoint map by pullProjection. Its pullComposition equation, together
with finitePullCompositionNormalization, therefore identifies the supplied
compositor with the canonical completed pullback compositor after every coherent
finite reduction. The coherent reduction functor on complete constructible
objects is faithful. Hence the canonical integral tensor/composition equation
from derivedPullbackTensorIso gives the displayed equation. This calculation is
on whole coherent quotient systems and retains the completion counit, rather
than inferring equality merely from separate reductions. For the rational
square apply rationalization.pullComposition and its fixed object and morphism
normalizations: localization carries the integral compositor and tensor square
to the rational one. For the common-stage square choose one coefficient field
containing both objects and the two composites. The pullComposition equation of
commonStageComparison identifies the common compositor with the rational one,
and commonProjectionPullbackTensorCompatibility identifies the tensor/pullback
comparisons. Apply ofHom at that field to the rational square; transition
naturality makes this independent of the field. In all three squares cancel the
displayed equality transports for identity composition. No identity unit or
projection counit is used. Zero objects and empty schemes require no exception. -/
theorem higherTensor_identityComposition (S : SixFunctorOperationDatum D C E n hn) :
    (∀ X : SixFunctorSpace D,
      letI : IsProper (𝟙 X : X ⟶ X).hom.left := by
        change IsProper (𝟙 X.obj.left)
        infer_instance
      let U := S.higher.integral.pull (𝟙 X)
      let T := Functor.uncurry.obj (S.higher.integralTensor X)
      let μ := fun M L ↦
        ((projectionPullbackTensor (S.higher.integralExchange
          (compactSupportProperSquare (𝟙 X : X ⟶ X)))).hom.app M).app L
      let c : ∀ M, U.obj M ≅ U.obj (U.obj M) := fun M ↦
        eqToIso (congrArg (fun f ↦ (S.higher.integral.pull f).obj M)
          (Category.id_comp (𝟙 X)).symm) ≪≫
          (S.higher.integral.pullComposition (𝟙 X) (𝟙 X)).app M
      ∀ M L, μ M L ≫ T.map (Prod.mkHom (c M).hom (c L).hom) =
        (c (T.obj (M, L))).hom ≫ U.map (μ M L) ≫ μ (U.obj M) (U.obj L)) ∧
    (∀ X : SixFunctorSpace D,
      letI : IsProper (𝟙 X : X ⟶ X).hom.left := by
        change IsProper (𝟙 X.obj.left)
        infer_instance
      let U := S.higher.rational.pull (𝟙 X)
      let T := Functor.uncurry.obj (S.higher.rationalTensor X)
      let μ := fun M L ↦
        ((projectionPullbackTensor (S.higher.rationalExchange
          (compactSupportProperSquare (𝟙 X : X ⟶ X)))).hom.app M).app L
      let c : ∀ M, U.obj M ≅ U.obj (U.obj M) := fun M ↦
        eqToIso (congrArg (fun f ↦ (S.higher.rational.pull f).obj M)
          (Category.id_comp (𝟙 X)).symm) ≪≫
          (S.higher.rational.pullComposition (𝟙 X) (𝟙 X)).app M
      ∀ M L, μ M L ≫ T.map (Prod.mkHom (c M).hom (c L).hom) =
        (c (T.obj (M, L))).hom ≫ U.map (μ M L) ≫ μ (U.obj M) (U.obj L)) ∧
    (∀ X : SixFunctorSpace D,
      letI : IsProper (𝟙 X : X ⟶ X).hom.left := by
        change IsProper (𝟙 X.obj.left)
        infer_instance
      let U := S.closure.commonStage.pull (𝟙 X)
      let T := Functor.uncurry.obj (S.closure.commonStageTensor X)
      let μ := fun M L ↦
        ((projectionPullbackTensor (S.closure.commonStageExchange
          (compactSupportProperSquare (𝟙 X : X ⟶ X)))).hom.app M).app L
      let c : ∀ M, U.obj M ≅ U.obj (U.obj M) := fun M ↦
        eqToIso (congrArg (fun f ↦ (S.closure.commonStage.pull f).obj M)
          (Category.id_comp (𝟙 X)).symm) ≪≫
          (S.closure.commonStage.pullComposition (𝟙 X) (𝟙 X)).app M
      ∀ M L, μ M L ≫ T.map (Prod.mkHom (c M).hom (c L).hom) =
        (c (T.obj (M, L))).hom ≫ U.map (μ M L) ≫ μ (U.obj M) (U.obj L)) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro X
    let : IsProper (𝟙 X : X ⟶ X).hom.left := by
      change IsProper (𝟙 X.obj.left)
      infer_instance
  · exact identity_tensor_raw S.higher.integral X (S.higher.integralTensor X)
      (projectionPullbackTensor (S.higher.integralExchange
        (compactSupportProperSquare (𝟙 X : X ⟶ X)))) (integral_tensor_composition S X)
  · exact identity_tensor_raw S.higher.rational X (S.higher.rationalTensor X)
      (projectionPullbackTensor (S.higher.rationalExchange
        (compactSupportProperSquare (𝟙 X : X ⟶ X)))) (rational_tensor_composition S X)
  · exact identity_tensor_raw S.closure.commonStage X (S.closure.commonStageTensor X)
      (projectionPullbackTensor (S.closure.commonStageExchange
        (compactSupportProperSquare (𝟙 X : X ⟶ X)))) (common_tensor_composition S X)

end WeilConjectures
