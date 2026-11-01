/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionFactors.IntegralProjectionMiddleMap
public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionFactors.IntegralProjectionFactorData
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralProjectionOpenTensorCoordinates
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralProjectionSupportFactorCoordinates

/-! # Reduction of the open factor of one projection

Source: prop-sf-pf-coherence.proof.md, the open-factor unit transpose.
(blueprint: lem-sf-integral-projection-open-factor-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification
open IntegralSystemRealization

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus Coordinates.sourceMap Coordinates.targetMap
  ProjectionFactors.middleMap ProjectionFactors.first ProjectionFactors.second
  ProjectionFactors.directReduction ProjectionFactors.properPullReduction
  ProjectionFactors.openReduction ProjectionFactors.barTensorReduction
  ProjectionFactors.openMap ProjectionFactors.supportMap

private theorem map_paste {B C : Type*} [Category B] [Category C]
    (P : B ⥤ C) {U V W : B} {Z : C} (d : Z ⟶ P.obj U)
    (a : U ⟶ V) (b : V ⟶ W) (t : U ⟶ W) (h : a ≫ b = t) :
    (d ≫ P.map a) ≫ P.map b = d ≫ P.map t := by
  rw [Category.assoc, ← P.map_comp, h]

private theorem pullReduction_naturality
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Integral C.l E Y} (v : M ⟶ N) :
    (calculus C.l E X).reduction.map ((integralDerivedPullback C.l E f).map v) ≫
        (Coordinates.pullReduction D C E o z f N).hom =
      (Coordinates.pullReduction D C E o z f M).hom ≫
        (pull C.l E f).map ((calculus C.l E Y).reduction.map v) := by
  let R := (calculus C.l E X).reduction
  let P := pullbackTensorIntegralPullbackModel C.l E f
  have hP := P.hom.naturality v
  have hε := (calculus C.l E X).adjunction.counit.naturality
    ((pull C.l E f).map ((calculus C.l E Y).reduction.map v))
  dsimp only [Coordinates.pullReduction, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, asIso_hom]
  rw [← Category.assoc, ← R.map_comp, hP, R.map_comp, Category.assoc]
  simpa only [R, P, pullbackTensorReferencePullback, Functor.comp_map,
    Functor.id_map, Category.assoc] using
    congrArg (fun t ↦ R.map (P.hom.app M) ≫ t) hε

private theorem properPullReduction_naturality
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    {M N : sfIntegralConstructibleCategory C.l E Y.obj.left} (v : M ⟶ N) :
    (calculus C.l E c.Z).reduction.map
        (((S.higher.integralExchange (identitySquare f c)).stage.properPull.map v).hom) ≫
        (ProjectionFactors.properPullReduction D C E n hn S hl o z f c N).hom =
      (ProjectionFactors.properPullReduction D C E n hn S hl o z f c M).hom ≫
        (pull C.l E c.g).map ((calculus C.l E Y.obj.left).reduction.map v.hom) := by
  let A := S.higher.integralExchange (identitySquare f c)
  let IY := (sfIntegralConstructible C.l E Y.obj.left).ι
  let IZ := (sfIntegralConstructible C.l E c.Z).ι
  let R := (calculus C.l E c.Z).reduction
  let := Coordinates.residueUnits hl Y
  let := Coordinates.residueUnits hl (identitySquare f c).Z
  let e : A.stage.properPull ⋙ IZ ≅ IY ⋙ integralDerivedPullback C.l E c.g :=
    eqToIso (by rw [A.properPull, S.higher.integralPullback]; rfl)
  let r : IY ⋙ integralDerivedPullback C.l E c.g ⋙ R ⟶
      IY ⋙ (calculus C.l E Y.obj.left).reduction ⋙ pull C.l E c.g :=
    { app := fun N ↦ (Coordinates.pullReduction D C E o z c.g N.obj).hom
      naturality := fun _ _ v ↦ pullReduction_naturality D C E o z c.g v.hom }
  have h := ((Functor.whiskerRight e.hom R) ≫ r).naturality v
  simpa only [e, r, IY, IZ, NatTrans.comp_app, Functor.whiskerRight_app,
    eqToIso.hom, eqToHom_app, eqToHom_map, Functor.comp_map,
    ObjectProperty.ι_map, ProjectionFactors.properPullReduction, Coordinates.pullValue,
    Iso.trans_hom, Functor.mapIso_hom, eqToHom_trans_assoc, eqToHom_trans] using h

private theorem directReduction_naturality
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    {M N : sfIntegralConstructibleCategory C.l E (identitySquare f c).Z.obj.left}
    (v : M ⟶ N) :
    (calculus C.l E Y.obj.left).reduction.map
        (((S.higher.integralExchange (identitySquare f c)).stage.properPush.map v).hom) ≫
        ProjectionFactors.directReduction D C E n hn S hl o z f c N =
      ProjectionFactors.directReduction D C E n hn S hl o z f c M ≫
        (Operations.push C.l E o c.g).map
          ((calculus C.l E c.Z).reduction.map v.hom) := by
  let A := S.higher.integralExchange (identitySquare f c)
  let R := (calculus C.l E c.Z).reduction
  let RY := (calculus C.l E Y.obj.left).reduction
  let eM := ProjectionFactors.properPullReduction D C E n hn S hl o z f c
    (A.stage.properPush.obj M)
  let eN := ProjectionFactors.properPullReduction D C E n hn S hl o z f c
    (A.stage.properPush.obj N)
  have hn := properPullReduction_naturality D C E n hn S hl o z f c
    (A.stage.properPush.map v)
  have hi : (pull C.l E c.g).map (RY.map (A.stage.properPush.map v).hom) ≫ eN.inv =
      eM.inv ≫ R.map (A.stage.properPull.map (A.stage.properPush.map v)).hom := by
    apply eM.eq_inv_comp.mpr
    rw [← Category.assoc, ← hn, Category.assoc]
    change R.map (A.stage.properPull.map (A.stage.properPush.map v)).hom ≫
      (eN.hom ≫ eN.inv) = _
    rw [eN.hom_inv_id, Category.comp_id]
  unfold ProjectionFactors.directReduction
  apply (o.direct c.g).adj.homEquiv_naturality_left_square
  rw [← Category.assoc, hi]
  simpa only [Functor.comp_map, Functor.id_map, ObjectProperty.FullSubcategory.comp_hom,
    Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ eM.inv ≫ R.map t.hom)
      (A.stage.properAdjunction.counit.naturality v)

/-- The coefficient square after the proper projection mate.
It contains the open tensor map, pullback compositor and target support identification;
it makes no assertion about a proper projection mate.

Source: prop-sf-pf-coherence.proof.md, the j_! factor and compactification sentence;
lem-sf-integral-projection-reduction-normalization, proof step 2.
(blueprint: lem-sf-integral-projection-open-factor-reduction).

Proof: factor second through the local open arrow and the one-input support map.
Naturality of pullReduction follows from its defining natural isomorphism and
counit naturality. Transport this naturality to properPullReduction and use the
proper adjunction Hom bijection and the integral counit to prove naturality of
directReduction. Push the local open tensor/compositor square through proper
direct image. Move its integral open arrow past directReduction by naturality,
and substitute the one-input support square. Functoriality combines the two
integral arrows into second, and the remaining open image of inputReduction is
exactly the second factor of targetMap. -/
theorem integralProjectionOpenFactorReduction
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
    ProjectionFactors.middleMap D C E n hn S hl o z f c K L ≫
        ProjectionFactors.systemSecond D C E o z f c
          ((calculus C.l E X.obj.left).reduction.obj K.obj)
          ((calculus C.l E Y.obj.left).reduction.obj L.obj) =
      (calculus C.l E Y.obj.left).reduction.map
        (ProjectionFactors.second (S.higher.integralExchange (identitySquare f c)) K L).hom ≫
          Coordinates.targetMap D C E S.higher hl o z f c K L := by
  let A := S.higher.integralExchange (identitySquare f c)
  let W := ((S.higher.integralTensor X).obj K).obj ((S.higher.integral.pull f).obj L)
  let q := ProjectionFactors.openMap A K L
  let r := ProjectionFactors.supportMap A W
  let P := Operations.push C.l E o c.g
  let R := (calculus C.l E c.Z).reduction
  let RY := (calculus C.l E Y.obj.left).reduction
  let M := (A.stage.tensorBar.obj (A.stage.openExtension.obj K)).obj
    (A.stage.properPull.obj L)
  let d : RY.obj (A.stage.properPush.obj M).obj ⟶ P.obj (R.obj M.obj) :=
    ProjectionFactors.directReduction D C E n hn S hl o z f c M
  let dW : RY.obj (A.stage.properPush.obj (A.stage.openExtension.obj W)).obj ⟶
      P.obj (R.obj (A.stage.openExtension.obj W).obj) :=
    ProjectionFactors.directReduction D C E n hn S hl o z f c
      (A.stage.openExtension.obj W)
  let jW := ProjectionFactors.openReduction D C E n hn S hl o z f c W
  let t := (Operations.shriek C.l E o c.i).map
    (Coordinates.inputReduction D C E S.higher hl o z f K L).inv
  have hj := integralProjectionOpenTensorCoordinates D C E n hn S hl o z f c K L hL
  have hs : dW ≫ P.map jW = RY.map r.hom ≫
      Coordinates.supportReduction D C E S.higher hl o z f c W :=
    integralProjectionSupportFactorCoordinates D C E n hn S hl o z f c W
  have hq : RY.map (A.stage.properPush.map q).hom ≫ dW = d ≫ P.map (R.map q.hom) :=
    directReduction_naturality D C E n hn S hl o z f c q
  have hf : ProjectionFactors.second A K L = A.stage.properPush.map q ≫ r :=
    ProjectionFactors.second_via_openMap A K L
  have hlocal : ProjectionFactors.middleMap D C E n hn S hl o z f c K L ≫
      ProjectionFactors.systemSecond D C E o z f c
        ((calculus C.l E X.obj.left).reduction.obj K.obj)
        ((calculus C.l E Y.obj.left).reduction.obj L.obj) =
      d ≫ P.map (R.map q.hom ≫ jW ≫ t) := by
    unfold ProjectionFactors.middleMap ProjectionFactors.systemSecond
    refine map_paste P d _ _ _ ?_
    simpa only [Functor.id_obj, Category.assoc] using hj
  refine hlocal.trans ?_
  unfold Coordinates.targetMap
  change d ≫ P.map (R.map q.hom ≫ jW ≫ t) =
    RY.map (ProjectionFactors.second A K L).hom ≫
      (Coordinates.supportReduction D C E S.higher hl o z f c W ≫ P.map t)
  calc
    d ≫ P.map (R.map q.hom ≫ jW ≫ t) =
        (d ≫ P.map (R.map q.hom)) ≫ (P.map jW ≫ P.map t) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (RY.map (A.stage.properPush.map q).hom ≫ dW) ≫
        (P.map jW ≫ P.map t) :=
      congrArg (fun a ↦ a ≫ (P.map jW ≫ P.map t)) hq.symm
    _ = RY.map (A.stage.properPush.map q).hom ≫
        ((dW ≫ P.map jW) ≫ P.map t) := by simp only [Category.assoc]
    _ = RY.map (A.stage.properPush.map q).hom ≫
        ((RY.map r.hom ≫ Coordinates.supportReduction D C E S.higher hl o z f c W) ≫
          P.map t) :=
      congrArg (fun a ↦ RY.map (A.stage.properPush.map q).hom ≫ (a ≫ P.map t)) hs
    _ = RY.map (ProjectionFactors.second A K L).hom ≫
        (Coordinates.supportReduction D C E S.higher hl o z f c W ≫ P.map t) := by
      have he := congrArg (fun a ↦ RY.map a.hom) hf
      have he' : RY.map (ProjectionFactors.second A K L).hom =
          RY.map (A.stage.properPush.map q).hom ≫ RY.map r.hom := by
        simpa only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] using he
      simpa only [Category.assoc] using
        congrArg (fun a ↦ a ≫ Coordinates.supportReduction D C E S.higher hl o z f c W ≫
          P.map t) he'.symm

end WeilConjectures.FixProjectionCompactification
