/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.Coordinates.IntegralProjectionCoordinateData

/-! # The coefficient map at the proper/open junction

Source: prop-sf-pf-coherence, the proper counit and open tensor factors.
(blueprint: def-sf-integral-projection-middle-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification.ProjectionFactors
open IntegralSystemRealization

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : Type u) [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
  (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
  (o : Operations C.l E) (z : Realizations C.l E D o)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)

/-- Tensor coordinates on the intermediate compactification scheme.
Source: completed tensor normalization (blueprint: def-sf-integral-projection-middle-map). -/
def barTensorReduction
    (M N : sfIntegralConstructibleCategory C.l E (identitySquare f c).Z.obj.left) :
    (calculus C.l E c.Z).reduction.obj
        ((((S.higher.integralExchange (identitySquare f c)).stage.tensorBar.obj M).obj N).obj) ≅
      (calculus C.l E c.Z).systemClosed.tensor.obj
        ((calculus C.l E c.Z).reduction.obj M.obj,
          (calculus C.l E c.Z).reduction.obj N.obj) :=
  (calculus C.l E c.Z).reduction.mapIso (eqToIso (by
    rw [(S.higher.integralExchange (identitySquare f c)).tensorBar]
    rfl)) ≪≫
    Coordinates.datumTensorReduction D C E S.higher hl (identitySquare f c).Z M N

/-- Pullback coordinates for the proper factor.
Source: quotient/pullback comparison (blueprint: def-sf-integral-projection-middle-map). -/
def properPullReduction (N : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (calculus C.l E c.Z).reduction.obj
        (((S.higher.integralExchange (identitySquare f c)).stage.properPull.obj N).obj) ≅
      (pull C.l E c.g).obj ((calculus C.l E Y.obj.left).reduction.obj N.obj) :=
  (calculus C.l E c.Z).reduction.mapIso (eqToIso (by
    rw [(S.higher.integralExchange (identitySquare f c)).properPull])) ≪≫
    (calculus C.l E c.Z).reduction.mapIso
      (Coordinates.pullValue D C E S.higher hl (identitySquare f c).p N) ≪≫
    Coordinates.pullReduction D C E o z c.g N.obj

/-- The direct-image coefficient map is the mate of inverse pullback reduction,
followed by reduction of the actual proper counit. It is constructed without an
invertibility assertion. Source: adjunction transposition
(blueprint: def-sf-integral-projection-middle-map). -/
def directReduction
    (M : sfIntegralConstructibleCategory C.l E (identitySquare f c).Z.obj.left) :=
  (o.direct c.g).adj.homEquiv _ _
    ((properPullReduction D C E n hn S hl o z f c
        ((S.higher.integralExchange (identitySquare f c)).stage.properPush.obj M)).inv ≫
      (calculus C.l E c.Z).reduction.map
        (((S.higher.integralExchange (identitySquare f c)).stage.properAdjunction.counit.app
          M).hom))

variable [QuasiCompact f.hom.left]

/-- The open coefficient map uses the datum's specified ordinary open realization
and the inverse whole-system open reduction mate, using its proved invertibility.
Source: open-unit scalar mate
(blueprint: def-sf-integral-projection-middle-map). -/
def openReduction (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (calculus C.l E c.Z).reduction.obj
        (((S.higher.integralExchange (identitySquare f c)).stage.openExtension.obj K).obj) ⟶
      (Operations.shriek C.l E o c.i).obj
        ((calculus C.l E X.obj.left).reduction.obj K.obj) := by
  letI := Coordinates.residueUnits hl X
  letI : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have hK : finiteTorConstructibleIntegral C.l E X.obj.left K.obj := by
    rw [← (integral_residue_tor D C.l C.different E X.obj.left).2]
    exact K.property
  obtain ⟨hred, _⟩ := GeneratorReduction.openReconstructionEffectivity C.l E o
    z.realizationModel c.i K.obj (Or.inl hK)
  letI := hred
  exact (calculus C.l E c.Z).reduction.map (eqToHom (by
      rw [(S.higher.integralExchange (identitySquare f c)).openExtension]
      rfl)) ≫
    (calculus C.l E c.Z).reduction.map
      ((S.integralNormalization.openRealization (identitySquare f c).i
        (identitySquare f c).open_i).hom.app K) ≫
    inv ((z.realizationModel.openReduction C.l E c.i).app K.obj)

/-- Explicit comparison at the junction of proper projection and open projection.
It uses only adjunction mates, tensor coordinates, and the specified open map;
neither compactification projection occurs in its definition.
Source: prop-sf-pf-coherence (blueprint: def-sf-integral-projection-middle-map). -/
def middleMap (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :=
  directReduction D C E n hn S hl o z f c
      (((S.higher.integralExchange (identitySquare f c)).stage.tensorBar.obj
        ((S.higher.integralExchange (identitySquare f c)).stage.openExtension.obj K)).obj
        ((S.higher.integralExchange (identitySquare f c)).stage.properPull.obj L)) ≫
    (Operations.push C.l E o c.g).map
      ((barTensorReduction D C E n hn S hl f c
          ((S.higher.integralExchange (identitySquare f c)).stage.openExtension.obj K)
          ((S.higher.integralExchange (identitySquare f c)).stage.properPull.obj L)).hom ≫
        (calculus C.l E c.Z).systemClosed.tensor.map
          (Prod.mkHom (openReduction D C E n hn S hl o z f c K)
            (properPullReduction D C E n hn S hl o z f c L).hom))

/-- The system proper factor with its uncurried source and target written explicitly.
This interface avoids expanding the postcomposition and whiskering functors in callers.
Source: compactificationProjection (blueprint: def-sf-integral-projection-middle-map). -/
def systemFirst (M : System C.l E X.obj.left) (N : System C.l E Y.obj.left) :
    (calculus C.l E Y.obj.left).systemClosed.tensor.obj
        ((Operations.push C.l E o c.g).obj ((Operations.shriek C.l E o c.i).obj M), N) ⟶
      (Operations.push C.l E o c.g).obj
        ((calculus C.l E c.Z).systemClosed.tensor.obj
          ((Operations.shriek C.l E o c.i).obj M, (pull C.l E c.g).obj N)) :=
  ((properProjection C.l E o c.g).app ((Operations.shriek C.l E o c.i).obj M)).app N

/-- The system open factor, including the inverse pullback compositor.
Source: compactificationProjection (blueprint: def-sf-integral-projection-middle-map). -/
def systemSecond (M : System C.l E X.obj.left) (N : System C.l E Y.obj.left) :=
  (Operations.push C.l E o c.g).map
    ((z.openComparisons.projection c.i).hom.app (M, (pull C.l E c.g).obj N) ≫
      (Operations.shriek C.l E o c.i).map
        ((calculus C.l E X.obj.left).systemClosed.tensor.map
          (Prod.mkHom (𝟙 M) ((z.compositors.pullComp c.i c.g).inv.app N ≫
            eqToHom (congrArg (fun g : X.obj.left ⟶ Y.obj.left ↦
              (pull C.l E g).obj N) c.comm.symm)))))

end WeilConjectures.FixProjectionCompactification.ProjectionFactors
