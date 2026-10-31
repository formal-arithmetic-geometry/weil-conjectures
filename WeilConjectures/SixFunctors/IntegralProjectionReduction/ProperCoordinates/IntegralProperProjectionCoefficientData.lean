/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.Coordinates.IntegralProjectionCoordinateData
public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates

/-! # Direct-image coordinates for the proper projection

Source: fix-prop-projection-formula.proof.md, compatibility under coefficient reduction.
All maps here are constructed from the actual tensor comparisons and adjunction mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Functor
namespace WeilConjectures.IntegralProjectionReduction.ProperCoordinates
open IntegralSystemRealization
open FixProjectionCompactification.Coordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E]

/-- Whole-system reduction restricted to the full constructible category.
Source: coefficient reduction (blueprint: def-sf-integral-proper-projection-coordinates). -/
abbrev reduce (W : SixFunctorSpace D) :=
  (sfIntegralConstructible C.l E W.obj.left).ι ⋙ (calculus C.l E W.obj.left).reduction

variable (H : SixFunctorHigherOperations D C E) (hl : IsUnit (C.l : D.k))
  (o : Operations C.l E) (z : Realizations C.l E D o)

/-- The natural reduction/tensor comparison, in curried notation.
Source: datumTensorReductionIso
(blueprint: def-sf-integral-proper-projection-coordinates). -/
def tensor (W : SixFunctorSpace D) :
    (postcompose₂.obj (reduce W)).obj (H.integralTensor W) ⟶
      (((whiskeringLeft₂ _).obj (reduce W)).obj (reduce W)).obj
        (Functor.curryObj (calculus C.l E W.obj.left).systemClosed.tensor) where
  app K :=
    { app := fun L ↦ (datumTensorReduction D C E H hl W K L).hom
      naturality := fun {L L'} b ↦ by
        simpa [datumTensorReduction, Functor.uncurry, Functor.curryObj] using
          (datumTensorReductionIso D C E H hl W).hom.naturality (Prod.mkHom (𝟙 K) b) }
  naturality := fun {K K'} a ↦ by
    ext L
    simpa [datumTensorReduction, Functor.uncurry, Functor.curryObj] using
      (datumTensorReductionIso D C E H hl W).hom.naturality (Prod.mkHom a (𝟙 L))

/-- The proper pullback/tensor comparison in the datum's own operation coordinates.
Source: the proper square of the supplied exchange data
(blueprint: def-sf-integral-proper-projection-coordinates). -/
def pullTensor {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left] :
    (postcompose₂.obj (H.integral.pull f)).obj (H.integralTensor Y) ≅
      (((whiskeringLeft₂ _).obj (H.integral.pull f)).obj (H.integral.pull f)).obj
        (H.integralTensor X) := by
  let A := H.integralExchange (compactSupportProperSquare f)
  exact eqToIso (by simp only [A.properPull, A.tensorY]; rfl) ≪≫ A.stage.tensorPullback ≪≫
    eqToIso (by simp only [A.properPull, A.tensorBar]; rfl)

/-- Naturality of the ambient pullback comparison. Source: reconstruction counit
(blueprint: def-sf-integral-proper-projection-coordinates). -/
theorem ambientPull_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : Integral C.l E Y} (a : K ⟶ L) :
    (calculus C.l E X).reduction.map ((integralDerivedPullback C.l E f).map a) ≫
        (pullReduction D C E o z f L).hom =
      (pullReduction D C E o z f K).hom ≫
        (pull C.l E f).map ((calculus C.l E Y).reduction.map a) := by
  let R := (calculus C.l E X).reduction
  let Q := (calculus C.l E Y).reduction ⋙ pull C.l E f
  let t := whiskerRight (pullbackTensorIntegralPullbackModel C.l E f).hom R ≫
    whiskerLeft Q (calculus C.l E X).adjunction.counit
  simpa only [t, R, Q, pullReduction, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Iso.app_hom, Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using t.naturality a

/-- The normalized pullback comparison as a natural isomorphism.
Source: the actual reconstruction counit and completed-pullback model
(blueprint: def-sf-integral-proper-projection-coordinates). -/
def pullComparison {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    H.integral.pull f ⋙ reduce X ≅ reduce Y ⋙ pull C.l E f.hom.left := by
  letI := residueUnits hl X
  letI := residueUnits hl Y
  let I := (sfIntegralConstructible C.l E X.obj.left).ι
  let h := congrArg (fun F ↦ F ⋙ I) (H.integralPullback f)
  let R := (calculus C.l E X.obj.left).reduction
  let e : integralDerivedPullback C.l E f.hom.left ⋙ R ≅
      (calculus C.l E Y.obj.left).reduction ⋙ pull C.l E f.hom.left :=
    NatIso.ofComponents (fun K ↦ pullReduction D C E o z f.hom.left K)
      (fun a ↦ ambientPull_naturality o z f.hom.left a)
  exact Functor.isoWhiskerRight (eqToIso h) R ≪≫
    Functor.isoWhiskerLeft (sfIntegralConstructible C.l E Y.obj.left).ι e

/-- The natural pullback comparison has exactly the previously specified components.
Source: its construction (blueprint: def-sf-integral-proper-projection-coordinates). -/
theorem pullComparison_hom_app {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (pullComparison H hl o z f).hom.app L =
      (calculus C.l E X.obj.left).reduction.map (pullValue D C E H hl f L).hom ≫
        (pullReduction D C E o z f.hom.left L.obj).hom := by
  let := residueUnits hl X
  let := residueUnits hl Y
  simp only [pullComparison, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatIso.ofComponents_hom_app, eqToIso.hom,
    eqToHom_app, pullValue]
  rw [eqToHom_map]
  rfl

/-- Direct-image comparison is the mate of inverse pullback comparison.
Source: the pull/direct adjunctions
(blueprint: def-sf-integral-proper-projection-coordinates). -/
def direct {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    H.integral.direct f ⋙ reduce Y ⟶ reduce X ⋙ Operations.push C.l E o f.hom.left :=
  (mateEquiv (H.integral.pullDirectAdjunction f) (o.direct f.hom.left).adj
    (TwoSquare.mk _ _ _ _ (pullComparison H hl o z f).inv)).natTrans

/-- Source comparison for the direct counit projection.
Source: tensor followed by the direct-image mate
(blueprint: def-sf-integral-proper-projection-coordinates). -/
def source {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :=
  ((tensor H hl Y).app ((H.integral.direct f).obj K)).app L ≫
    (calculus C.l E Y.obj.left).systemClosed.tensor.map
      (Prod.mkHom ((direct H hl o z f).app K) (𝟙 _))

/-- Target comparison for the direct counit projection.
Source: the direct-image mate followed by tensor/pullback reduction
(blueprint: def-sf-integral-proper-projection-coordinates). -/
def target {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :=
  (direct H hl o z f).app
      (((H.integralTensor X).obj K).obj ((H.integral.pull f).obj L)) ≫
    (Operations.push C.l E o f.hom.left).map (inputReduction D C E H hl o z f K L).inv

/-- Identity open extension, with its section-normalized comparison.
Source: the canonical bridge and exact identity open extension
(blueprint: def-sf-integral-proper-projection-coordinates). -/
def openIdentity (W : Scheme.{u}) : Operations.shriek C.l E o (𝟙 W) ≅ 𝟭 _ :=
  z.canonicalBridge.shriek C.l E (𝟙 W) ≪≫
    ProEtale.SemilinearProperOpen.jId (scalarRings C.l E) (scalarTransitions C.l E) W

end WeilConjectures.IntegralProjectionReduction.ProperCoordinates
