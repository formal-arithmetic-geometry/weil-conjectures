/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionFiniteEvaluationData
public import WeilConjectures.SixFunctors.FixProjectionCompactification.Coordinates.IntegralProjectionCoordinateData
import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProperTensorPullbackReduction
import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProperSupportReductionIdentity
import WeilConjectures.SixFunctors.IntegralProjectionReduction.SystemProperIdentityOpenProjection
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat

/-! # Whole-system normalization of the proper counit projection

Source: fix-prop-projection-formula.proof.md, proper counit and coefficient reduction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open IntegralSystemRealization

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus CompactSupportFiniteProjection.partialTensor
  CompactSupportFiniteProjection.component compactSupportProjectionComponent
  compactSupportProperProjection

open CategoryTheory.Functor
open ProperCoordinates

attribute [local irreducible]
  FixProjectionCompactification.Coordinates.supportReduction
  FixProjectionCompactification.Coordinates.supportValue
  FixProjectionCompactification.Coordinates.reconstruction
  FixProjectionCompactification.Coordinates.datumTensorReductionIso
  FixProjectionCompactification.Coordinates.inputReduction
  FixProjectionCompactification.Coordinates.pullReduction
  FixProjectionCompactification.Coordinates.pullValue
  IntegralSystemRealization.properProjection
  IntegralSystemRealization.compactificationProjection
  ProperCoordinates.openIdentity

/-- Pasting the source tensor comparison uses only bifunctoriality and naturality.
Source: the source endpoint calculation of the proper coefficient square. -/
private theorem tensor_source_paste
    {A B C : Type*} [Category A] [Category B] [Category C] (T : A × B ⥤ C)
    {P Q R S : A} (L : B) {U V : C}
    (τ₀ : U ⟶ T.obj (P, L)) (τ₁ : V ⟶ T.obj (Q, L)) (v : U ⟶ V)
    (a : P ⟶ R) (b : R ⟶ S) (c : P ⟶ Q) (e : Q ⟶ S)
    (hs : a ≫ b = c ≫ e)
    (hn : v ≫ τ₁ = τ₀ ≫ T.map (Prod.mkHom c (𝟙 L))) :
    (τ₀ ≫ T.map (Prod.mkHom a (𝟙 L))) ≫ T.map (Prod.mkHom b (𝟙 L)) =
      v ≫ (τ₁ ≫ T.map (Prod.mkHom e (𝟙 L))) := by
  calc
    _ = τ₀ ≫ T.map (Prod.mkHom (a ≫ b) (𝟙 L)) := by
      simpa only [Category.assoc, prod_comp, Prod.mkHom, Category.comp_id] using
        congrArg (fun m ↦ τ₀ ≫ m)
          (T.map_comp (Prod.mkHom a (𝟙 L)) (Prod.mkHom b (𝟙 L))).symm
    _ = τ₀ ≫ T.map (Prod.mkHom (c ≫ e) (𝟙 L)) :=
      congrArg (fun m ↦ τ₀ ≫ T.map (Prod.mkHom m (𝟙 L))) hs
    _ = (τ₀ ≫ T.map (Prod.mkHom c (𝟙 L))) ≫ T.map (Prod.mkHom e (𝟙 L)) := by
      simpa only [Category.assoc, prod_comp, Prod.mkHom, Category.comp_id] using
        congrArg (fun m ↦ τ₀ ≫ m)
          (T.map_comp (Prod.mkHom c (𝟙 L)) (Prod.mkHom e (𝟙 L)))
    _ = (v ≫ τ₁) ≫ T.map (Prod.mkHom e (𝟙 L)) :=
      congrArg (fun m ↦ m ≫ T.map (Prod.mkHom e (𝟙 L))) hn.symm
    _ = _ := Category.assoc _ _ _

/-- Cancel an isomorphism after applying a functor.
Source: functoriality and the inverse identity. -/
private theorem map_iso_paste {A B : Type*} [Category A] [Category B]
    (G : A ⥤ B) {U : B} {V W Z : A}
    (a : U ⟶ G.obj V) (b : U ⟶ G.obj Z) (t : V ⟶ W) (v : W ≅ Z)
    (h : a ≫ G.map t = b ≫ G.map v.inv) : b = a ≫ G.map (t ≫ v.hom) := by
  have hv : G.map v.inv ≫ G.map v.hom = 𝟙 _ := by
    rw [← G.map_comp, v.inv_hom_id, G.map_id]
  calc
    b = b ≫ (G.map v.inv ≫ G.map v.hom) := by rw [hv, Category.comp_id]
    _ = (b ≫ G.map v.inv) ≫ G.map v.hom := (Category.assoc _ _ _).symm
    _ = (a ≫ G.map t) ≫ G.map v.hom := congrArg (fun m ↦ m ≫ G.map v.hom) h.symm
    _ = _ := by rw [Category.assoc, G.map_comp]

/-- Naturality pastes the target comparison with its one-input normalization.
Source: naturality and functoriality. -/
private theorem target_paste {A B : Type*} [Category A] [Category B]
    (G : A ⥤ B) {J : A ⥤ A} (u : J ⟶ 𝟭 A) {M N : A} {U V : B}
    (a : U ⟶ G.obj (J.obj M)) (β : U ⟶ V) (δ : V ⟶ G.obj M) (i : M ⟶ N)
    (h : a ≫ G.map (u.app M) = β ≫ δ) :
    (a ≫ G.map (J.map i)) ≫ G.map (u.app N) = β ≫ (δ ≫ G.map i) := by
  rw [Category.assoc, ← G.map_comp, u.naturality i]
  simp only [Functor.id_map, G.map_comp]
  rw [← Category.assoc, h, Category.assoc]

/-- The proper compactification has the identity open factor, as a whole functor.
Source: Compactification.ofIsProper. -/
private theorem proper_support_functor_eq
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (o : Operations C.l E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left] :
    Operations.shriek C.l E o (Compactification.ofIsProper f.hom.left).i ⋙
        Operations.push C.l E o (Compactification.ofIsProper f.hom.left).g =
      Operations.shriek C.l E o (𝟙 X.obj.left) ⋙
        Operations.push C.l E o f.hom.left := rfl

/-- Paste the direct projection square and its two endpoint normalizations.
Source: composition of the four coefficient squares and cancellation of their endpoint isos. -/
private theorem projection_paste {A B : Type*} [Category A] [Category B]
    (R : A ⥤ B) {A₀ A₁ A₂ A₃ : A} (v : A₀ ⟶ A₁) (p : A₁ ⟶ A₂) (β : A₃ ≅ A₂)
    {U V W Z : B} (s₀ : R.obj A₀ ⟶ U) (s₁ : R.obj A₁ ⟶ V) (a : U ⟶ V)
    (pc : U ⟶ W) (pd : V ⟶ Z) (t₀ : R.obj A₃ ⟶ W) (t₁ : R.obj A₂ ⟶ Z)
    (u : W ≅ Z) (hs : s₀ ≫ a = R.map v ≫ s₁)
    (hc : a ≫ pd = pc ≫ u.hom) (hd : s₁ ≫ pd = R.map p ≫ t₁)
    (ht : t₀ ≫ u.hom = R.map β.hom ≫ t₁) :
    s₀ ≫ pc = R.map (v ≫ p ≫ β.inv) ≫ t₀ := by
  apply (cancel_mono u.hom).1
  calc
    (s₀ ≫ pc) ≫ u.hom = s₀ ≫ (a ≫ pd) := by rw [Category.assoc, ← hc]
    _ = (s₀ ≫ a) ≫ pd := (Category.assoc _ _ _).symm
    _ = (R.map v ≫ s₁) ≫ pd := congrArg (fun m ↦ m ≫ pd) hs
    _ = R.map v ≫ (R.map p ≫ t₁) := by rw [Category.assoc, hd]
    _ = R.map (v ≫ p ≫ β.inv) ≫ (R.map β.hom ≫ t₁) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc (R.map β.inv), ← R.map_comp, β.inv_hom_id,
        R.map_id, Category.id_comp]
    _ = (R.map (v ≫ p ≫ β.inv) ≫ t₀) ≫ u.hom := by rw [Category.assoc, ht]

/-- Projection maps respect equality transport of their tensor and adjunction data.
Source: equality induction, followed by the definition of rightAdjointProjectionMap. -/
private theorem projection_transport
    {A B : Type*} [Category A] [Category B]
    {F F' : B ⥤ A} {G G' : A ⥤ B} {T T' : A ⥤ A ⥤ A}
    {S S' : B ⥤ B ⥤ B} (adj : F ⊣ G) (adj' : F' ⊣ G')
    (φ : (postcompose₂.obj F).obj S ⟶ (((whiskeringLeft₂ _).obj F).obj F).obj T)
    (φ' : (postcompose₂.obj F').obj S' ⟶ (((whiskeringLeft₂ _).obj F').obj F').obj T')
    (hF : F = F') (hG : G = G') (hT : T = T') (hS : S = S')
    (ha : HEq adj adj') (hφ : HEq φ φ') (M : A) (N : B) :
    HEq (((adj.rightAdjointProjectionMap φ).app M).app N)
      (((adj'.rightAdjointProjectionMap φ').app M).app N) := by
  subst F'; subst G'; subst T'; subst S'
  cases eq_of_heq ha
  cases eq_of_heq hφ
  rfl

/-- The proper-square presentation is the direct counit projection in actual coordinates.
Source: compactSupportProperProjection and its exchange-data normalization fields. -/
private theorem properProjection_eq
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (H : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    compactSupportProperProjection H.integralExchange f K L =
      (((H.integral.pullDirectAdjunction f).rightAdjointProjectionMap
        (pullTensor H f).hom).app K).app L := by
  let A := H.integralExchange (compactSupportProperSquare f)
  unfold compactSupportProperProjection
  apply eq_of_heq
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  have hφ : HEq A.stage.tensorPullback.hom (pullTensor H f).hom := by
    unfold pullTensor
    simp only [Iso.trans_hom, eqToIso.hom,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    rfl
  exact projection_transport _ _ _ _ A.properPull A.properPush A.tensorBar A.tensorY
    A.properAdjunction hφ K L

/-- Inverse input reduction is tensor reduction followed by pullback comparison.
Source: the explicit inputReduction construction in IntegralProjectionCoordinateData. -/
private theorem inputReduction_inv
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (H : SixFunctorHigherOperations D C E) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (FixProjectionCompactification.Coordinates.inputReduction D C E H hl o z f K L).inv =
      ((tensor H hl X).app K).app ((H.integral.pull f).obj L) ≫
        ((Functor.curryObj (calculus C.l E X.obj.left).systemClosed.tensor).obj
          ((reduce X).obj K)).map ((pullComparison H hl o z f).hom.app L) := by
  rw [pullComparison_hom_app]
  simp only [FixProjectionCompactification.Coordinates.inputReduction, Iso.trans_inv,
    Functor.mapIso_inv, Iso.prod, Iso.refl_inv, Iso.symm_inv,
    Iso.trans_inv, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rfl

/-- The direct-image projection square follows from tensor compatibility of the pull mate.
Source: the proved generic rightAdjointProjectionMap_mate theorem. -/
private theorem direct_projection_square
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (H : SixFunctorHigherOperations D C E) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    source H hl o z f K L ≫
        ((properProjection C.l E o f.hom.left).app ((reduce X).obj K)).app
          ((reduce Y).obj L) =
      (reduce Y).map (compactSupportProperProjection H.integralExchange f K L) ≫
        target H hl o z f K L := by
  let P := pull C.l E f.hom.left
  let G := Operations.push C.l E o f.hom.left
  let T := Functor.curryObj (calculus C.l E X.obj.left).systemClosed.tensor
  let q := pullComparison H hl o z f
  let v := (T.obj ((reduce X).obj K)).mapIso (q.app L)
  have hm := Adjunction.rightAdjointProjectionMap_mate
    (T₂ := Functor.curryObj (calculus C.l E X.obj.left).systemClosed.tensor)
    (S₂ := Functor.curryObj (calculus C.l E Y.obj.left).systemClosed.tensor)
    (H.integral.pullDirectAdjunction f) (o.direct f.hom.left).adj
    (pullTensor H f).hom
    (Functor.curry.mapIso (pullbackTensorSystemComparison C.l E f.hom.left) ≪≫
      Functor.curryObjProdComp P P (calculus C.l E X.obj.left).systemClosed.tensor).hom
    (tensor H hl Y) (tensor H hl X) q.inv (direct H hl o z f)
    (integralProperTensorPullbackReduction H hl o z f)
    (fun M ↦ mateEquiv_counit (H.integral.pullDirectAdjunction f)
      (o.direct f.hom.left).adj (TwoSquare.mk _ _ _ _ q.inv) M) K L
  have hp := congrArg (fun a ↦ (reduce Y).map a ≫
      (direct H hl o z f).app
        (((H.integralTensor X).obj K).obj ((H.integral.pull f).obj L)) ≫
      G.map (((tensor H hl X).app K).app ((H.integral.pull f).obj L)))
    (properProjection_eq H f K L)
  have hm₁ := hp.trans hm
  have hm₂ :
      (reduce Y).map (compactSupportProperProjection H.integralExchange f K L) ≫
          (direct H hl o z f).app
            (((H.integralTensor X).obj K).obj ((H.integral.pull f).obj L)) ≫
          G.map (((tensor H hl X).app K).app ((H.integral.pull f).obj L)) =
        source H hl o z f K L ≫
          ((properProjection C.l E o f.hom.left).app ((reduce X).obj K)).app
            ((reduce Y).obj L) ≫ G.map v.inv := by
    simpa only [source, properProjection, Functor.curryObj, v, T,
      Functor.mapIso_inv, Iso.app_inv, Category.assoc] using hm₁
  have hm₃ := map_iso_paste G
    ((reduce Y).map (compactSupportProperProjection H.integralExchange f K L) ≫
      (direct H hl o z f).app
        (((H.integralTensor X).obj K).obj ((H.integral.pull f).obj L)))
    (source H hl o z f K L ≫
      ((properProjection C.l E o f.hom.left).app ((reduce X).obj K)).app
        ((reduce Y).obj L))
    (((tensor H hl X).app K).app ((H.integral.pull f).obj L)) v
    (by simpa only [Category.assoc] using hm₂)
  have hi := congrArg (fun a ↦
      (reduce Y).map (compactSupportProperProjection H.integralExchange f K L) ≫
        (direct H hl o z f).app
          (((H.integralTensor X).obj K).obj ((H.integral.pull f).obj L)) ≫ G.map a)
    (inputReduction_inv H hl o z f K L)
  have hm₄ := hm₃.trans (by
    simpa only [v, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using hi.symm)
  simpa only [target, Category.assoc] using hm₄

/-- The proper counit square before finite evaluation, expressed through the
identity-open support comparison. No finite projection or finite tensor coordinate
occurs in this statement.

Source: fix-prop-projection-formula.proof.md, proper counit computation in the
successive coefficient reductions; the proper part of the individual-map normalization.
(blueprint: lem-sf-integral-proper-projection-system-normalization).

Proof: transpose the proper projection under the specified pull/direct adjunction.
Its transpose is the tensor of the counit and the identity after the prescribed tensor
pullback isomorphism. Reduce this expression on simultaneous strict quotient models.
The reduction adjunction's unit/counit compatibility and normalized completed tensor
associator identify it with the corresponding system transpose. Integral residue Tor
justifies the completed tensor comparisons. Transpose back and insert the properIdentity
isomorphism on both endpoints. To identify this properIdentity with the canonical
support/direct comparison, apply supportProjection, directProjection and the coefficient
properIdentity equation at every quotient. finiteProperNormalization identifies the
resulting finite maps with the identity-open unit comparison. The proved constructible
integral reduction faithfulness then identifies the integral maps; no faithfulness on
unrestricted system categories is needed. Thus supportValue for the identity-open
compactification is the same direct-image comparison. Its open reduction is the
identity-open unit, and the reconstruction counit cancels it by the triangle identity.
Consequently the two inserted endpoint maps are precisely sourceMap and
targetMap. In the system compactification expression the identity-open tensor map and
pullback compositor cancel, leaving the same proper counit projection. This gives the
displayed whole-system square. The argument is a computation with actual adjunction
mates, not a deduction from joint faithfulness of finite evaluation, and includes zero
inputs and the identity proper map. -/
theorem integralProperProjectionSystemNormalization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (d : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left)
    (hL : finiteTorConstructibleIntegral C.l E Y.obj.left L.obj) :
    FixProjectionCompactification.Coordinates.sourceMap
        D C E d.higher hl o z f (.ofIsProper f.hom.left) K L ≫
      compactificationProjection C.l E o z.compositors z.openComparisons
        (.ofIsProper f.hom.left)
        ((calculus C.l E X.obj.left).reduction.obj K.obj)
        ((calculus C.l E Y.obj.left).reduction.obj L.obj) =
      (calculus C.l E Y.obj.left).reduction.map (properViaSupport d f K L).hom ≫
        FixProjectionCompactification.Coordinates.targetMap
          D C E d.higher hl o z f (.ofIsProper f.hom.left) K L := by
  have _hL := hL
  clear hL _hL
  let H := d.higher
  let R := reduce (C := C) (E := E) Y
  let G := Operations.push C.l E o f.hom.left
  let T := (calculus C.l E Y.obj.left).systemClosed.tensor
  let M := ((H.integralTensor X).obj K).obj ((H.integral.pull f).obj L)
  change _ = R.map (properViaSupport d f K L) ≫ _
  let u := G.mapIso ((openIdentity o z X.obj.left).app
    ((calculus C.l E X.obj.left).systemClosed.tensor.obj
      (((reduce X).obj K), (pull C.l E f.hom.left).obj ((reduce Y).obj L))))
  have hs := integralProperSupportReductionIdentity d hl o z f K
  have ht := integralProperSupportReductionIdentity d hl o z f M
  have hn := NatTrans.congr_app ((tensor H hl Y).naturality
    ((H.integral.properIdentity f).hom.app K)) L
  have hsource :
      FixProjectionCompactification.Coordinates.sourceMap
          D C E H hl o z f (.ofIsProper f.hom.left) K L ≫
        T.map (Prod.mkHom (G.map
          ((openIdentity o z X.obj.left).hom.app ((reduce X).obj K))) (𝟙 _)) =
      R.map (((H.integralTensor Y).map
        ((H.integral.properIdentity f).hom.app K)).app L) ≫ source H hl o z f K L := by
    have hn' :
        R.map (((H.integralTensor Y).map
          ((H.integral.properIdentity f).hom.app K)).app L) ≫
            ((tensor H hl Y).app ((H.integral.direct f).obj K)).app L =
          ((tensor H hl Y).app ((H.integral.support f (.ofIsProper f.hom.left)).obj K)).app L ≫
            T.map (Prod.mkHom (R.map ((H.integral.properIdentity f).hom.app K))
              (𝟙 ((reduce Y).obj L))) := by
      simpa only [R, T, reduce, ObjectProperty.ι_obj, ObjectProperty.ι_map,
        NatTrans.comp_app, Functor.postcompose₂, Functor.whiskeringLeft₂,
        Functor.whiskeringRight, Functor.whiskeringLeft, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.comp, Functor.curryObj] using hn
    exact tensor_source_paste T ((reduce Y).obj L)
      (((tensor H hl Y).app ((H.integral.support f (.ofIsProper f.hom.left)).obj K)).app L)
      (((tensor H hl Y).app ((H.integral.direct f).obj K)).app L)
      (R.map (((H.integralTensor Y).map ((H.integral.properIdentity f).hom.app K)).app L))
      (FixProjectionCompactification.Coordinates.supportReduction
        D C E H hl o z f (.ofIsProper f.hom.left) K)
      (G.map ((openIdentity o z X.obj.left).hom.app ((reduce X).obj K)))
      (R.map ((H.integral.properIdentity f).hom.app K))
      ((direct H hl o z f).app K) hs hn'
  have htarget :
      FixProjectionCompactification.Coordinates.targetMap
          D C E H hl o z f (.ofIsProper f.hom.left) K L ≫ u.hom =
      R.map ((H.integral.properIdentity f).hom.app M) ≫ target H hl o z f K L := by
    have hx := target_paste G (openIdentity o z X.obj.left).hom
      (FixProjectionCompactification.Coordinates.supportReduction
        D C E H hl o z f (.ofIsProper f.hom.left) M)
      (R.map ((H.integral.properIdentity f).hom.app M))
      ((direct H hl o z f).app M)
      (FixProjectionCompactification.Coordinates.inputReduction D C E H hl o z f K L).inv ht
    simpa only [FixProjectionCompactification.Coordinates.targetMap, target, u,
      M, G, reduce, Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj,
      Functor.mapIso_hom, Iso.app_hom, proper_support_functor_eq o f,
      Functor.comp_map] using hx
  have hc := systemProperIdentityOpenProjection o z f.hom.left
    ((reduce X).obj K) ((reduce Y).obj L)
  have hd := direct_projection_square H hl o z f K L
  have hp := projection_paste R
    (((H.integralTensor Y).map ((H.integral.properIdentity f).hom.app K)).app L)
    (compactSupportProperProjection H.integralExchange f K L)
    ((H.integral.properIdentity f).app M)
    (FixProjectionCompactification.Coordinates.sourceMap
      D C E H hl o z f (.ofIsProper f.hom.left) K L)
    (source H hl o z f K L)
    (T.map (Prod.mkHom
      (G.map ((openIdentity o z X.obj.left).hom.app ((reduce X).obj K)))
      (𝟙 ((reduce Y).obj L))))
    (compactificationProjection C.l E o z.compositors z.openComparisons
      (.ofIsProper f.hom.left) ((reduce X).obj K) ((reduce Y).obj L))
    (((properProjection C.l E o f.hom.left).app ((reduce X).obj K)).app ((reduce Y).obj L))
    (FixProjectionCompactification.Coordinates.targetMap
      D C E H hl o z f (.ofIsProper f.hom.left) K L)
    (target H hl o z f K L) u hsource
    (by simpa only [u, Functor.mapIso_hom, Iso.app_hom] using hc) hd
    (by simpa only [Iso.app_hom] using htarget)
  simpa only [properViaSupport, Iso.app_inv, H, M, R, reduce, Functor.comp_obj,
    Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map] using hp

end WeilConjectures.IntegralProjectionReduction
