/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionFactors.IntegralProjectionMiddleMap
public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionFactors.IntegralProjectionFactorData
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralProjectionSupportFactorCoordinates
import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProperTensorPullbackReduction
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-! # Reduction of the proper factor of one projection

Source: prop-sf-pf-coherence.proof.md, the proper-factor counit transpose.
(blueprint: lem-sf-integral-projection-proper-factor-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification
open IntegralSystemRealization IntegralProjectionReduction
open CategoryTheory.Functor

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus Coordinates.sourceMap Coordinates.targetMap
  ProjectionFactors.middleMap ProjectionFactors.first ProjectionFactors.second
  ProjectionFactors.systemFirst
  ProjectionFactors.directReduction ProjectionFactors.properPullReduction
  ProjectionFactors.barTensorReduction ProjectionFactors.openReduction
  Coordinates.supportReduction Coordinates.supportValue Coordinates.reconstruction
  Coordinates.datumTensorReductionIso
  Coordinates.pullReduction Coordinates.pullValue IntegralSystemRealization.properProjection
  sfIntegralConstructible pullbackTensorSystemComparison pullbackTensorSequenceDerived
  SheafOfModules.instCategory

private def curriedTensorIso
    {B N : Type*} [Category B] [Category N] (T : B ⥤ B ⥤ B)
    (R : B ⥤ N) (U : N × N ⥤ N)
    (e : Functor.uncurry.obj T ⋙ R ≅ (R.prod R) ⋙ U) :
    (postcompose₂.obj R).obj T ≅
      (((whiskeringLeft₂ _).obj R).obj R).obj (Functor.curryObj U) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun N ↦ e.app (M, N))
    (fun a ↦ by simpa [Functor.uncurry, Functor.curryObj] using
      e.hom.naturality (Prod.mkHom (𝟙 M) a)))
    (fun a ↦ by ext N; simpa [Functor.uncurry, Functor.curryObj] using
      e.hom.naturality (Prod.mkHom a (𝟙 N)))

private theorem curried_hom_heq
    {B N : Type*} [Category B] [Category N]
    {F F' : B ⥤ N} {T T' : N ⥤ N ⥤ N} {S S' : B ⥤ B ⥤ B}
    (hF : F = F') (hT : T = T') (hS : S = S')
    (p : (postcompose₂.obj F).obj S ⟶ (((whiskeringLeft₂ _).obj F).obj F).obj T)
    (q : (postcompose₂.obj F').obj S' ⟶ (((whiskeringLeft₂ _).obj F').obj F').obj T')
    (h : ∀ M L, HEq ((p.app M).app L) ((q.app M).app L)) : HEq p q := by
  subst F' T' S'
  apply heq_of_eq
  ext M L
  exact eq_of_heq (h M L)

private theorem transported_component
    {B N : Type*} [Category B] [Category N]
    {F F' G G' : B ⥤ B ⥤ N} (hF : F = F') (hG : G' = G)
    (e : F' ≅ G') (M L : B) :
    HEq (((eqToIso hF ≪≫ e ≪≫ eqToIso hG).hom.app M).app L)
      ((e.hom.app M).app L) := by
  subst F' G'
  simp

private theorem comparison_transport
    {B N B' N' : Type*} [Category B] [Category N] [Category B'] [Category N']
    {F F' : B ⥤ N} {T T' : N ⥤ N ⥤ N} {S S' : B ⥤ B ⥤ B}
    {U : B ⥤ B'} {V : N ⥤ N'} {P : B' ⥤ N'}
    {TC : N' ⥤ N' ⥤ N'} {TD : B' ⥤ B' ⥤ B'}
    (hF : F = F') (hT : T = T') (hS : S = S')
    (q : F' ⋙ V ≅ U ⋙ P)
    (c : (postcompose₂.obj V).obj T' ≅
      (((whiskeringLeft₂ _).obj V).obj V).obj TC)
    (d : (postcompose₂.obj U).obj S' ≅
      (((whiskeringLeft₂ _).obj U).obj U).obj TD)
    (p : (postcompose₂.obj F).obj S ⟶ (((whiskeringLeft₂ _).obj F).obj F).obj T)
    (p' : (postcompose₂.obj F').obj S' ⟶ (((whiskeringLeft₂ _).obj F').obj F').obj T')
    (ps : (postcompose₂.obj P).obj TD ⟶ (((whiskeringLeft₂ _).obj P).obj P).obj TC)
    (hp : HEq p p') (h : Adjunction.ComparisonCompatible q.symm p' ps c d) :
    Adjunction.ComparisonCompatible
      (Functor.isoWhiskerRight (eqToIso hF) V ≪≫ q).symm p ps
      (eqToIso (congrArg ((postcompose₂.obj V).obj) hT) ≪≫ c)
      (eqToIso (congrArg ((postcompose₂.obj U).obj) hS) ≪≫ d) := by
  subst F' T' S'
  cases eq_of_heq hp
  simpa using h

private theorem mate_component
    {B N B' N' : Type*} [Category B] [Category N] [Category B'] [Category N']
    {F : B ⥤ N} {G : N ⥤ B} {P : B' ⥤ N'} {Q : N' ⥤ B'}
    {U : B ⥤ B'} {V : N ⥤ N'} (adj : F ⊣ G) (adj' : P ⊣ Q)
    (alpha : TwoSquare U F P V) (M : N) :
    adj'.homEquiv _ _ (alpha.app (G.obj M) ≫ V.map (adj.counit.app M)) =
      (mateEquiv adj adj' alpha).app M := by
  apply (adj'.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact (mateEquiv_counit adj adj' alpha M).symm

private theorem replace_projection_mates
    {B C : Type*} [Category B] [Category C] (T : B ⥤ B ⥤ B) (P : C ⥤ B)
    {W X S S' N : B} {H H' : C}
    (a : W ⟶ X) (b : X ⟶ P.obj H) (c : H ⟶ H')
    (d : W ⟶ (T.obj S).obj N) (e : S ⟶ S')
    (f : (T.obj S').obj N ⟶ P.obj H')
    (h : a ≫ b ≫ P.map c = d ≫ (T.map e).app N ≫ f)
    (b' : X ⟶ P.obj H) (e' : S ⟶ S')
    (f' : (T.obj S').obj N ⟶ P.obj H')
    (hb : b' = b) (he : e' = e) (hf : f' = f) :
    a ≫ b' ≫ P.map c = d ≫ (T.map e').app N ≫ f' := by
  rw [hb, he, hf]
  exact h

private theorem identity_Y {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) :
    (identitySquare f c).Y = Y := rfl

private theorem identity_p_left {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) :
    (identitySquare f c).p.hom.left = c.g := rfl

private theorem identity_Z_left {D : FiniteFieldDatum.{u}} {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) (c : Compactification f.hom.left) :
    (identitySquare f c).Z.obj.left = c.Z := rfl

@[irreducible] private def proper_component
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (o : Operations C.l E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (M : System C.l E c.Z) (N : System C.l E Y.obj.left) :
    (calculus C.l E Y.obj.left).systemClosed.tensor.obj
      ((Operations.push C.l E o c.g).obj M, N) ⟶
    (Operations.push C.l E o c.g).obj
      ((calculus C.l E c.Z).systemClosed.tensor.obj (M, (pull C.l E c.g).obj N)) :=
  ((properProjection C.l E o c.g).app M).app N

private theorem proper_component_naturality
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (o : Operations C.l E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    {M M' : System C.l E c.Z} (j : M ⟶ M') (N : System C.l E Y.obj.left) :
    (calculus C.l E Y.obj.left).systemClosed.tensor.map
        (Prod.mkHom ((Operations.push C.l E o c.g).map j) (𝟙 N)) ≫
      proper_component D C E o f c M' N =
    proper_component D C E o f c M N ≫ (Operations.push C.l E o c.g).map
      ((calculus C.l E c.Z).systemClosed.tensor.map
        (Prod.mkHom j (𝟙 ((pull C.l E c.g).obj N)))) := by
  unfold proper_component
  exact NatTrans.congr_app ((properProjection C.l E o c.g).naturality j) N

private theorem source_transport_cancel
    {B N : Type*} [Category B] [Category N] (R : B ⥤ N)
    {X X' Y : B} (a : X ⟶ X') [IsIso a] (p : X' ⟶ Y) (q : X ⟶ Y)
    {U V : N} (t : R.obj X' ⟶ U) (s : U ⟶ V) (r : R.obj Y ⟶ V)
    (ha : a ≫ p = q) (h : (R.map a ≫ t) ≫ s = R.map q ≫ r) :
    t ≫ s = R.map p ≫ r := by
  apply (cancel_epi (R.map a)).mp
  calc
    R.map a ≫ (t ≫ s) = (R.map a ≫ t) ≫ s := (Category.assoc _ _ _).symm
    _ = R.map q ≫ r := h
    _ = R.map (a ≫ p) ≫ r := congrArg (fun v ↦ R.map v ≫ r) ha.symm
    _ = R.map a ≫ (R.map p ≫ r) := by rw [R.map_comp, Category.assoc]

/-- Reduction carries the proper counit projection at an arbitrary intermediate
object to the system proper projection. There is no support identification or
open extension in this equation.

Source: prop-sf-pf-coherence.proof.md, the proper-factor counit transpose;
lem-sf-integral-projection-proper-factor-reduction, proof step 2.
(blueprint: lem-sf-integral-projection-proper-factor-reduction).

Proof: transpose under the system pull/direct adjunction. Substitute directReduction
and the counit formula for rightAdjointProjectionMap. Tensor naturality moves the
reduced counit to the right. The integralTensorPullbackNormalization equation,
followed by the canonical completed pullback/tensor reduction square, identifies
the remaining tensor/pullback maps. The reconstruction counit is natural, and its
triangle equation cancels the completion-unit conjugations. The two transposes
therefore agree, and the Hom equivalence is injective. This calculation is on the
whole reduction system, with its actual transition maps. It uses no support
identification, open projection, or choice of coefficient comparisons. -/
private theorem integralProjectionProperMateCoordinates
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (M : sfIntegralConstructibleCategory C.l E (identitySquare f c).Z.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left)
    (p : ((S.higher.integralTensor Y).obj
        ((S.higher.integralExchange (identitySquare f c)).stage.properPush.obj M)).obj L ⟶
      (S.higher.integralExchange (identitySquare f c)).stage.properPush.obj
        (((S.higher.integralExchange (identitySquare f c)).stage.tensorBar.obj M).obj
          ((S.higher.integralExchange (identitySquare f c)).stage.properPull.obj L)))
    (hp : let A := S.higher.integralExchange (identitySquare f c)
      HEq p (((A.stage.properAdjunction.rightAdjointProjectionMap
        A.stage.tensorPullback.hom).app M).app L)) :
    let A := S.higher.integralExchange (identitySquare f c)
    (Coordinates.datumTensorReduction D C E S.higher hl Y
        (A.stage.properPush.obj M) L).hom ≫
        (calculus C.l E Y.obj.left).systemClosed.tensor.map
          (Prod.mkHom (ProjectionFactors.directReduction D C E n hn S hl o z f c M)
            (𝟙 _)) ≫
        proper_component D C E o f c
          ((calculus C.l E c.Z).reduction.obj M.obj)
          ((calculus C.l E Y.obj.left).reduction.obj L.obj) =
      (calculus C.l E Y.obj.left).reduction.map p.hom ≫
        ProjectionFactors.directReduction D C E n hn S hl o z f c
          ((A.stage.tensorBar.obj M).obj (A.stage.properPull.obj L)) ≫
        (Operations.push C.l E o c.g).map
          ((ProjectionFactors.barTensorReduction D C E n hn S hl f c M
              (A.stage.properPull.obj L)).hom ≫
            (calculus C.l E c.Z).systemClosed.tensor.map
              (Prod.mkHom (𝟙 _) (ProjectionFactors.properPullReduction
                D C E n hn S hl o z f c L).hom))  := by
  let A := S.higher.integralExchange (identitySquare f c)
  let : IsProper (identitySquare f c).p.hom.left := (identitySquare f c).proper_p
  let := Coordinates.residueUnits hl (identitySquare f c).Z
  let := Coordinates.residueUnits hl Y
  let R := (calculus C.l E c.Z).reduction
  let RY := (calculus C.l E Y.obj.left).reduction
  let IZ := (sfIntegralConstructible C.l E c.Z).ι ⋙ R
  let IY := (sfIntegralConstructible C.l E Y.obj.left).ι ⋙ RY
  let TZ := (calculus C.l E c.Z).systemClosed.tensor
  let TY := (calculus C.l E Y.obj.left).systemClosed.tensor
  let P := pull C.l E c.g
  let q0 := IntegralProjectionReduction.ProperCoordinates.pullComparison
    S.higher hl o z (identitySquare f c).p
  let q := Functor.isoWhiskerRight (eqToIso A.properPull) IZ ≪≫ q0
  let tZ0 := curriedTensorIso (S.higher.integralTensor (identitySquare f c).Z) IZ TZ
    (Coordinates.datumTensorReductionIso D C E S.higher hl (identitySquare f c).Z)
  let tY0 := curriedTensorIso (S.higher.integralTensor Y) IY TY
    (Coordinates.datumTensorReductionIso D C E S.higher hl Y)
  let tZ := eqToIso (congrArg ((postcompose₂.obj IZ).obj) A.tensorBar) ≪≫ tZ0
  let tY := eqToIso (congrArg ((postcompose₂.obj IY).obj) A.tensorY) ≪≫ tY0
  let phi : (postcompose₂.obj P).obj (Functor.curryObj TY) ⟶
      (((whiskeringLeft₂ _).obj P).obj P).obj (Functor.curryObj TZ) :=
    (Functor.curry.mapIso (pullbackTensorSystemComparison C.l E c.g) ≪≫
    Functor.curryObjProdComp P P TZ).hom
  have hphi : HEq A.stage.tensorPullback.hom
      (IntegralProjectionReduction.ProperCoordinates.pullTensor S.higher
        (identitySquare f c).p).hom := by
    apply curried_hom_heq A.properPull A.tensorBar A.tensorY
    intro U V
    have h0 : HEq (((IntegralProjectionReduction.ProperCoordinates.pullTensor
        S.higher (identitySquare f c).p).hom.app U).app V)
        (canonicalIntegralPullbackTensor C.l E c.g U V).hom := by
      exact (transported_component _ _
        (S.higher.integralExchange
          (compactSupportProperSquare (identitySquare f c).p)).stage.tensorPullback U V).trans
        (S.higher.integralTensorPullbackNormalization
          (compactSupportProperSquare (identitySquare f c).p) U V)
    exact (S.higher.integralTensorPullbackNormalization (identitySquare f c) U V).trans
      h0.symm
  have hc0 : Adjunction.ComparisonCompatible q0.symm
      (IntegralProjectionReduction.ProperCoordinates.pullTensor S.higher
        (identitySquare f c).p).hom phi tZ0 tY0 := by
    intro U V
    have h := integralProperTensorPullbackReduction S.higher hl o z
      (identitySquare f c).p U V
    apply (cancel_epi (q0.inv.app (((S.higher.integralTensor Y).obj U).obj V))).mp
    simp only [Iso.symm_inv, Iso.symm_hom]
    erw [q0.inv_hom_id_app_assoc]
    simpa only [Category.assoc, tZ0, tY0, curriedTensorIso,
      IntegralProjectionReduction.ProperCoordinates.tensor, Coordinates.datumTensorReduction,
      NatIso.ofComponents_hom_app, q0, phi, TZ, TY, P,
      identity_p_left, identity_Z_left, identity_Y] using h.symm
  have hc : Adjunction.ComparisonCompatible q.symm A.stage.tensorPullback.hom phi tZ tY :=
    comparison_transport A.properPull A.tensorBar A.tensorY q0 tZ0 tY0
      A.stage.tensorPullback.hom _ phi hphi hc0
  let beta := (mateEquiv A.stage.properAdjunction (o.direct c.g).adj
    (TwoSquare.mk _ _ _ _ q.inv)).natTrans
  have hm0 := A.stage.properAdjunction.map_rightAdjointProjectionMap_comp_mateEquiv
    (o.direct c.g).adj (α := q.symm) (φ := A.stage.tensorPullback.hom)
    (φ' := phi) (m_C := tZ) (m_D := tY) hc M L
  have hq (N : sfIntegralConstructibleCategory C.l E Y.obj.left) :
      q.app N = ProjectionFactors.properPullReduction D C E n hn S hl o z f c N := by
    apply Iso.ext
    simp only [q, q0, Iso.app_hom, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, Functor.whiskerRight_app,
      IntegralProjectionReduction.ProperCoordinates.pullComparison_hom_app,
      ProjectionFactors.properPullReduction, Functor.mapIso_hom, eqToIso.hom,
      eqToHom_app, eqToHom_map, IZ, IntegralProjectionReduction.ProperCoordinates.reduce,
      Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.eqToHom_hom,
      identity_p_left, identity_Z_left]
  have hqhom (N : sfIntegralConstructibleCategory C.l E Y.obj.left) :
      q.hom.app N = (ProjectionFactors.properPullReduction
        D C E n hn S hl o z f c N).hom := congrArg Iso.hom (hq N)
  have hqinv (N : sfIntegralConstructibleCategory C.l E Y.obj.left) :
      q.inv.app N = (ProjectionFactors.properPullReduction D C E n hn S hl o z f c N).inv :=
    congrArg Iso.inv (hq N)
  have hz (U V : sfIntegralConstructibleCategory C.l E c.Z) :
      ((tZ.hom.app U).app V) =
        (ProjectionFactors.barTensorReduction D C E n hn S hl f c U V).hom := by
    simp only [tZ, tZ0, curriedTensorIso, Iso.trans_hom, eqToIso.hom,
      NatTrans.comp_app, eqToHom_app, NatIso.ofComponents_hom_app,
      ProjectionFactors.barTensorReduction, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, eqToIso.hom, IZ, eqToHom_map,
      ]
  have hb (U : sfIntegralConstructibleCategory C.l E c.Z) :
      ProjectionFactors.directReduction D C E n hn S hl o z f c U = beta.app U := by
    unfold ProjectionFactors.directReduction
    calc
      _ = (o.direct c.g).adj.homEquiv _ _
          (q.inv.app (A.stage.properPush.obj U) ≫ IZ.map
            (A.stage.properAdjunction.counit.app U)) := by
        simp only [hqinv, IZ, R, A, IntegralProjectionReduction.ProperCoordinates.reduce,
          identity_Y, Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_map,
          ObjectProperty.ι_obj]
      _ = beta.app U := mate_component A.stage.properAdjunction (o.direct c.g).adj
        (TwoSquare.mk _ _ _ _ q.inv) U
  have hpi :
      proper_component D C E o f c (IZ.obj M) (IY.obj L) =
        (((o.direct c.g).adj.rightAdjointProjectionMap phi).app (IZ.obj M)).app
          (IY.obj L) := by
    unfold proper_component properProjection
    rfl
  have hm := replace_projection_mates (Functor.curryObj TY)
    (Operations.push C.l E o c.g) _ _ _ _ _ _ hm0
    (ProjectionFactors.directReduction D C E n hn S hl o z f c
      ((A.stage.tensorBar.obj M).obj (A.stage.properPull.obj L)))
    (ProjectionFactors.directReduction D C E n hn S hl o z f c M)
    (proper_component D C E o f c (IZ.obj M) (IY.obj L))
    (hb ((A.stage.tensorBar.obj M).obj (A.stage.properPull.obj L))) (hb M) hpi
  let a : (A.stage.tensorY.obj (A.stage.properPush.obj M)).obj L ⟶
      ((S.higher.integralTensor Y).obj (A.stage.properPush.obj M)).obj L :=
    eqToHom (by rw [A.tensorY]; rfl)
  have hy : ((tY.hom.app (A.stage.properPush.obj M)).app L) =
      RY.map a.hom ≫ (Coordinates.datumTensorReduction D C E S.higher hl Y
        (A.stage.properPush.obj M) L).hom := by
    simp only [tY, tY0, curriedTensorIso, Iso.trans_hom, eqToIso.hom,
      NatTrans.comp_app, eqToHom_app, NatIso.ofComponents_hom_app,
      a, IY, eqToHom_map, ObjectProperty.eqToHom_hom]
  have ha : a ≫ p =
      ((A.stage.properAdjunction.rightAdjointProjectionMap
        A.stage.tensorPullback.hom).app M).app L := by
    apply eq_of_heq
    simpa only [a, eqToHom_comp_heq_iff] using hp
  let raw := ((A.stage.properAdjunction.rightAdjointProjectionMap
    A.stage.tensorPullback.hom).app M).app L
  let tau := (Coordinates.datumTensorReduction D C E S.higher hl Y
    (A.stage.properPush.obj M) L).hom
  let sigma := TY.map
      (Prod.mkHom (ProjectionFactors.directReduction D C E n hn S hl o z f c M) (𝟙 _)) ≫
    proper_component D C E o f c (R.obj M.obj) (RY.obj L.obj)
  let rho := ProjectionFactors.directReduction D C E n hn S hl o z f c
      ((A.stage.tensorBar.obj M).obj (A.stage.properPull.obj L)) ≫
    (Operations.push C.l E o c.g).map
      ((ProjectionFactors.barTensorReduction D C E n hn S hl f c M
        (A.stage.properPull.obj L)).hom ≫
        TZ.map (Prod.mkHom (𝟙 _) (ProjectionFactors.properPullReduction
          D C E n hn S hl o z f c L).hom))
  have he : (RY.map a.hom ≫ tau) ≫ sigma = RY.map raw.hom ≫ rho := by
    calc
      _ = ((tY.hom.app (A.stage.properPush.obj M)).app L) ≫ sigma :=
        congrArg (fun v ↦ v ≫ sigma) hy.symm
      _ = _ := by
        simpa only [sigma, rho, raw, IY, IZ, Functor.comp_map, ObjectProperty.ι_map,
          Category.assoc, hz, hqhom, Iso.symm_inv, Iso.symm_hom,
          Functor.curryObj, R, RY, P, TZ, TY,
          IntegralProjectionReduction.ProperCoordinates.reduce, identity_Y,
          Functor.comp_obj, ObjectProperty.ι_obj] using hm.symm
  have h := source_transport_cancel IY a p raw tau sigma rho ha he
  simpa only [IY, tau, sigma, rho, A, TY, TZ, R, RY, Category.assoc,
    Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_map, ObjectProperty.ι_obj] using h

private theorem tensor_identification_cancel
    {B : Type*} [Category B] (T U : B ⥤ B ⥤ B) (hT : U = T)
    {P Q R W : B} (e : P ≅ Q) (hP : P = R) (L : B)
    (p : (U.obj Q).obj L ⟶ W) :
    (T.map (e.inv ≫ eqToHom hP)).app L ≫
        (eqToHom (by rw [hT, hP]) ≫ (U.map e.hom).app L ≫ p) =
      eqToHom (by rw [hT]) ≫ p := by
  subst U R
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  rw [← Category.assoc, ← NatTrans.comp_app, ← T.map_comp, e.inv_hom_id, T.map_id]
  simp only [NatTrans.id_app, Category.id_comp]

private theorem first_tensor_naturality
    {B N : Type*} [Category B] [Category N] (T : B ⥤ B ⥤ B)
    (F : B ⥤ N) (U : N × N ⥤ N)
    (e : Functor.uncurry.obj T ⋙ F ≅ (F.prod F) ⋙ U)
    {X Y : B} (r : X ⟶ Y) (L : B) :
    F.map ((T.map r).app L) ≫ e.hom.app (Y, L) =
      e.hom.app (X, L) ≫ U.map (Prod.mkHom (F.map r) (𝟙 (F.obj L))) := by
  have h := e.hom.naturality (Prod.mkHom r (𝟙 L))
  change F.map ((T.map r).app L ≫ (T.obj Y).map (𝟙 L)) ≫ e.hom.app (Y, L) =
    e.hom.app (X, L) ≫ U.map (Prod.mkHom (F.map r) (F.map (𝟙 L))) at h
  rw [(T.obj Y).map_id L, Category.comp_id, F.map_id L] at h
  exact h

private theorem tensor_two_maps
    {B N : Type*} [Category B] [Category N] (T : B × B ⥤ N)
    {P Q R P' Q' R' : B} (a : P ⟶ Q) (b : Q ⟶ R)
    (a' : P' ⟶ Q') (b' : Q' ⟶ R') :
    T.map (Prod.mkHom a a') ≫ T.map (Prod.mkHom b b') =
      T.map (Prod.mkHom (a ≫ b) (a' ≫ b')) := by
  rw [← T.map_comp]
  rfl

private theorem map_factorization
    {B N : Type*} [Category B] [Category N] (F : B ⥤ N)
    {X Y Z : B} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (h : a ≫ b = c) : F.map a ≫ F.map b = F.map c := by
  rw [← F.map_comp, h]

private theorem proper_factor_paste
    {B C : Type*} [Category B] [Category C]
    (T : B × B ⥤ B) (U : C × C ⥤ C) (P : C ⥤ B)
    {V W Z A A' N : B} {M M' Q Q' H : C}
    (v : V ⟶ W) [Epi v] (first : W ⟶ Z) (p : V ⟶ Z)
    (tau : V ⟶ T.obj (A, N)) (tau' : W ⟶ T.obj (A', N))
    (r : A ⟶ A') (s : A' ⟶ P.obj M') (d : A ⟶ P.obj M) (j : M ⟶ M')
    (q : Q ⟶ Q') (b : H ⟶ U.obj (M, Q)) (d' : Z ⟶ P.obj H)
    (pi : T.obj (P.obj M, N) ⟶ P.obj (U.obj (M, Q')))
    (pi' : T.obj (P.obj M', N) ⟶ P.obj (U.obj (M', Q')))
    (hf : v ≫ first = p)
    (ht : v ≫ tau' = tau ≫ T.map (Prod.mkHom r (𝟙 N)))
    (hs : r ≫ s = d ≫ P.map j)
    (hp : tau ≫ T.map (Prod.mkHom d (𝟙 N)) ≫ pi =
      p ≫ d' ≫ P.map (b ≫ U.map (Prod.mkHom (𝟙 M) q)))
    (hn : T.map (Prod.mkHom (P.map j) (𝟙 N)) ≫ pi' =
      pi ≫ P.map (U.map (Prod.mkHom j (𝟙 Q')))) :
    (tau' ≫ T.map (Prod.mkHom s (𝟙 N))) ≫ pi' =
      first ≫ (d' ≫ P.map (b ≫ U.map (Prod.mkHom j q))) := by
  apply (cancel_epi v).mp
  simp only [Category.assoc]
  rw [← Category.assoc v first, hf, ← Category.assoc v tau', ht]
  rw [Category.assoc, ← T.map_comp_assoc]
  simp only [prod_comp, Category.comp_id]
  rw [hs]
  have he := tensor_two_maps T d (P.map j) (𝟙 N) (𝟙 N)
  simp only [Category.comp_id] at he
  rw [← he]
  simp only [Category.assoc]
  rw [hn, reassoc_of% hp]
  simp only [Category.assoc, ← P.map_comp, ← U.map_comp, prod_comp,
    Category.comp_id, Category.id_comp]

private theorem systemFirst_component
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (o : Operations C.l E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (M : System C.l E X.obj.left) (N : System C.l E Y.obj.left) :
    proper_component D C E o f c
      ((Operations.shriek C.l E o c.i).obj M) N =
        ProjectionFactors.systemFirst D C E o f c M N := by
  unfold ProjectionFactors.systemFirst proper_component
  rfl

/-- The coefficient square up to, and including, the proper projection mate.
The intermediate coefficient map is constructed independently of either projection.
No open projection is present in this equality.

Source: prop-sf-pf-coherence.proof.md, paragraph beginning "On the p factor";
lem-sf-integral-projection-reduction-normalization, proof step 1.
(blueprint: lem-sf-integral-projection-proper-factor-reduction).

Proof: expand sourceMap and first. The compact-support identification is the specified
open/proper factorization. The supportProjection and directProjection equations of
S.integralNormalization identify its reduction with the composite of the canonical
open reduction mate and the direct-image mate defined in directReduction. Their
normalization is on simultaneous quotient complexes, so it preserves transitions.
Apply the system proper adjunction Hom bijection. Substitute the defining transpose
of directReduction and the counit transpose of rightAdjointProjectionMap. Naturality
of the tensor comparison moves the support coefficient map through tensor. The
integralTensorPullbackNormalization equation identifies the proper tensor comparison
with the prescribed completed pullback/tensor map. The completion-unit and counit
normalizations of tensorReductionIso and pullReduction identify their quotient maps.
Both resulting transposes are the same tensor comparison followed by reduction of
the proper counit tensored with identity. Cancel the adjunction triangle, and use
injectivity of the Hom bijection. Residue Tor supplies the bound on K; hL supplies
the second bound. All steps are maps of the entire strict quotient system, before
localization; zero inputs and identity proper factors use the same unit equations. -/
theorem integralProjectionProperFactorReduction
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left)
    (hL : finiteTorConstructibleIntegral C.l E Y.obj.left L.obj) :
    Coordinates.sourceMap D C E S.higher hl o z f c K L ≫
        ProjectionFactors.systemFirst D C E o f c
          ((calculus C.l E X.obj.left).reduction.obj K.obj)
          ((calculus C.l E Y.obj.left).reduction.obj L.obj) =
      (calculus C.l E Y.obj.left).reduction.map
        (ProjectionFactors.first (S.higher.integralExchange (identitySquare f c)) K L).hom ≫
          ProjectionFactors.middleMap D C E n hn S hl o z f c K L  := by
  have _ := hL
  let A := S.higher.integralExchange (identitySquare f c)
  let M := A.stage.openExtension.obj K
  let RY := (calculus C.l E Y.obj.left).reduction
  let R := (calculus C.l E c.Z).reduction
  let TY := (calculus C.l E Y.obj.left).systemClosed.tensor
  let TZ := (calculus C.l E c.Z).systemClosed.tensor
  let P := Operations.push C.l E o c.g
  let N := RY.obj L.obj
  let r := ProjectionFactors.supportMap A K
  let v := ((S.higher.integralTensor Y).map r).app L
  let p : ((S.higher.integralTensor Y).obj (A.stage.properPush.obj M)).obj L ⟶
      A.stage.properPush.obj ((A.stage.tensorBar.obj M).obj (A.stage.properPull.obj L)) :=
    eqToHom (by rw [A.tensorY]; rfl) ≫
      ((A.stage.properAdjunction.rightAdjointProjectionMap
        A.stage.tensorPullback.hom).app M).app L
  let d : RY.obj (A.stage.properPush.obj M).obj ⟶ P.obj (R.obj M.obj) :=
    ProjectionFactors.directReduction D C E n hn S hl o z f c M
  let j : R.obj M.obj ⟶ (Operations.shriek C.l E o c.i).obj
      ((calculus C.l E X.obj.left).reduction.obj K.obj) :=
    ProjectionFactors.openReduction D C E n hn S hl o z f c K
  let q : R.obj (A.stage.properPull.obj L).obj ⟶ (pull C.l E c.g).obj N :=
    (ProjectionFactors.properPullReduction D C E n hn S hl o z f c L).hom
  have hv : IsIso v := by
    dsimp only [v, r, ProjectionFactors.supportMap]
    infer_instance
  let := hv
  have hfirst : v ≫ ProjectionFactors.first A K L = p := by
    dsimp only [v, r, p]
    unfold ProjectionFactors.first ProjectionFactors.supportMap
    exact tensor_identification_cancel (S.higher.integralTensor Y) A.stage.tensorY
      A.tensorY (A.stage.compactSupportIdentification.app K)
      (congrArg (fun F ↦ F.obj K) A.compactSupport) L _
  have hs := integralProjectionSupportFactorCoordinates D C E n hn S hl o z f c K
  have hpraw : HEq p (((A.stage.properAdjunction.rightAdjointProjectionMap
      A.stage.tensorPullback.hom).app M).app L) := by
    simp only [p, eqToHom_comp_heq_iff]
    exact HEq.rfl
  have hp := integralProjectionProperMateCoordinates D C E n hn S hl o z f c M L p hpraw
  have ht := first_tensor_naturality (S.higher.integralTensor Y)
    ((sfIntegralConstructible C.l E Y.obj.left).ι ⋙ RY) TY
    (Coordinates.datumTensorReductionIso D C E S.higher hl Y) r L
  have hnat := proper_component_naturality D C E o f c j N
  have hred : RY.map v.hom ≫ RY.map (ProjectionFactors.first A K L).hom =
      RY.map p.hom := by
    simpa only [Functor.comp_map, ObjectProperty.ι_map] using
      map_factorization ((sfIntegralConstructible C.l E Y.obj.left).ι ⋙ RY)
        v (ProjectionFactors.first A K L) p hfirst
  let tau := (Coordinates.datumTensorReduction D C E S.higher hl Y
    (A.stage.properPush.obj M) L).hom
  let b : R.obj (((A.stage.tensorBar.obj M).obj (A.stage.properPull.obj L)).obj) ⟶
      TZ.obj (R.obj M.obj, R.obj (A.stage.properPull.obj L).obj) :=
    (ProjectionFactors.barTensorReduction D C E n hn S hl f c M
      (A.stage.properPull.obj L)).hom
  let d' : RY.obj (A.stage.properPush.obj
      ((A.stage.tensorBar.obj M).obj (A.stage.properPull.obj L))).obj ⟶
      P.obj (R.obj (((A.stage.tensorBar.obj M).obj (A.stage.properPull.obj L)).obj)) :=
    ProjectionFactors.directReduction D C E n hn S hl o z f c
      ((A.stage.tensorBar.obj M).obj (A.stage.properPull.obj L))
  let pi0 : TY.obj (P.obj (R.obj M.obj), N) ⟶
      P.obj (TZ.obj (R.obj M.obj, (pull C.l E c.g).obj N)) :=
    proper_component D C E o f c (R.obj M.obj) N
  let pi1 : TY.obj ((P.obj ((Operations.shriek C.l E o c.i).obj
      ((calculus C.l E X.obj.left).reduction.obj K.obj))), N) ⟶
      P.obj (TZ.obj (((Operations.shriek C.l E o c.i).obj
        ((calculus C.l E X.obj.left).reduction.obj K.obj)), (pull C.l E c.g).obj N)) :=
    proper_component D C E o f c
      ((Operations.shriek C.l E o c.i).obj
        ((calculus C.l E X.obj.left).reduction.obj K.obj)) N
  have hs' : RY.map r.hom ≫ Coordinates.supportReduction
      D C E S.higher hl o z f c K = d ≫ P.map j := hs.symm
  have hn' : TY.map (Prod.mkHom (P.map j) (𝟙 N)) ≫ pi1 =
      pi0 ≫ P.map (TZ.map (Prod.mkHom j (𝟙 _))) := by
    exact hnat
  have hp' : tau ≫ TY.map (Prod.mkHom d (𝟙 N)) ≫ pi0 =
      RY.map p.hom ≫ d' ≫ P.map (b ≫ TZ.map (Prod.mkHom (𝟙 _) q)) := hp
  have hresult : Coordinates.sourceMap D C E S.higher hl o z f c K L ≫ pi1 =
      RY.map (ProjectionFactors.first A K L).hom ≫
        ProjectionFactors.middleMap D C E n hn S hl o z f c K L := by
    unfold Coordinates.sourceMap ProjectionFactors.middleMap
    exact proper_factor_paste TY TZ P (RY.map v.hom)
      (RY.map (ProjectionFactors.first A K L).hom) (RY.map p.hom) tau
      (Coordinates.datumTensorReduction D C E S.higher hl Y
        ((S.higher.integral.support f c).obj K) L).hom
      (RY.map r.hom) (Coordinates.supportReduction D C E S.higher hl o z f c K)
      d j q b d' pi0 pi1 hred ht hs' hp' hn'
  have hc := systemFirst_component D C E o f c
    ((calculus C.l E X.obj.left).reduction.obj K.obj) N
  exact (congrArg (fun v ↦ Coordinates.sourceMap D C E S.higher hl o z f c K L ≫ v)
    hc.symm).trans hresult

end WeilConjectures.FixProjectionCompactification
