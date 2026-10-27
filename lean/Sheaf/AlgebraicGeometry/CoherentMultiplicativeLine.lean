/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Coherent multiplicative lines on a commutative group scheme

Source: BLR, Neron Models, 10.1 Proposition 7, printed p.292, primitive lines;
the coherent rigidified formulation in the DAG
(blueprint: def-sfb-coherent-multiplicative-line).

Coherence is tested on frames over arbitrary schemes. Locally one can frame all
finitely many line factors, so these tests are exactly the usual tensor diagrams.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.MultiplicativeLine

open Scheme.Modules

/-- The line, identity frame, and specified multiplication isomorphism.
Source: BLR 10.1 Proposition 7, p.292, with rigidification and coherence as in the DAG
(blueprint: def-sfb-coherent-multiplicative-line). -/
structure Raw {S : Scheme.{u}} (G : CommGrp (Over S)) where
  line : G.X.left.Modules
  invertible : line.IsInvertible
  unit : unit S ≅ (tensorPullback η[G.X].left).obj line
  multiplication : (tensorPullback (fst G.X G.X).left).obj line ⊗
      (tensorPullback (snd G.X G.X).left).obj line ≅
    (tensorPullback μ[G.X].left).obj line

/-- A point of the line with its zero section removed: a base point and a frame.
Source: BLR 10.1 Proposition 7, p.292; Stacks Tag 01M2
(blueprint: def-sfb-coherent-multiplicative-line). -/
abbrev Point {S : Scheme.{u}} {G : CommGrp (Over S)} (A : Raw G) (U : Over S) :=
  (x : U ⟶ G.X) × (unit U.left ≅ (tensorPullback x.left).obj A.line)

/-- Identify an iterated inverse image with the inverse image along an equal composite.
Source: Stacks Tag 0097, canonical tensor inverse image
(blueprint: def-sfb-coherent-multiplicative-line). -/
def composite {T X Y : Scheme.{u}} (a : T ⟶ X) (b : X ⟶ Y) (c : T ⟶ Y)
    (w : a ≫ b = c) (L : Y.Modules) :
    (tensorPullback a).obj ((tensorPullback b).obj L) ≅ (tensorPullback c).obj L :=
  ((tensorPullbackSectionComp a b).app L).symm ≪≫
    eqToIso (congrArg (fun f ↦ (tensorPullback f).obj L) w)

/-- Multiply frames by pulling back the specified tensor multiplication.
Source: BLR 10.1 Proposition 7, p.292; Stacks Tags 01CD and 0097
(blueprint: def-sfb-coherent-multiplicative-line). -/
def mul {S : Scheme.{u}} {G : CommGrp (Over S)} (A : Raw G) {U : Over S}
    (v w : Point A U) : Point A U :=
  ⟨v.1 * w.1,
    (λ_ (unit U.left)).symm ≪≫ (v.2 ⊗ᵢ w.2) ≪≫
      ((composite (lift v.1 w.1).left (fst G.X G.X).left v.1.left
          (by simp) A.line).symm ⊗ᵢ
        (composite (lift v.1 w.1).left (snd G.X G.X).left w.1.left
          (by simp) A.line).symm) ≪≫
      (boundaryPullbackTensorIso (lift v.1 w.1).left _ _).symm ≪≫
      (tensorPullback (lift v.1 w.1).left).mapIso A.multiplication ≪≫
      composite (lift v.1 w.1).left μ[G.X].left (v.1 * w.1).left rfl A.line⟩

/-- The identity frame on any test scheme, pulled back from the specified rigidification.
Source: BLR 10.1 Proposition 7, p.292
(blueprint: def-sfb-coherent-multiplicative-line). -/
def one {S : Scheme.{u}} {G : CommGrp (Over S)} (A : Raw G) (U : Over S) : Point A U :=
  ⟨1, SplitTorusFrames.pullFrame A.line η[G.X].left A.unit (toUnit U).left⟩

/-- Associativity, symmetry and both identity-axis identities for the specified maps.
Equality of these framed points is equality with the canonical tensor/pullback transports.
Source: BLR 10.1 Proposition 7, p.292, coherent rigidified formulation of the DAG
(blueprint: def-sfb-coherent-multiplicative-line). -/
structure Coherent {S : Scheme.{u}} (G : CommGrp (Over S)) extends Raw G where
  assoc (U : Over S) (v w z : Point toRaw U) :
    mul toRaw (mul toRaw v w) z = mul toRaw v (mul toRaw w z)
  comm (U : Over S) (v w : Point toRaw U) : mul toRaw v w = mul toRaw w v
  one_mul (U : Over S) (v : Point toRaw U) : mul toRaw (one toRaw U) v = v
  mul_one (U : Over S) (v : Point toRaw U) : mul toRaw v (one toRaw U) = v

end AlgebraicGeometry.MultiplicativeLine

namespace AlgebraicGeometry.MultiplicativeLine

open Scheme.Modules

/-- The canonical group scheme after changing the base.
Source: BLR 10.1 Proposition 7, p.292; fibre-product group operations
(blueprint: def-sfb-coherent-multiplicative-line). -/
abbrev changeBase {S T : Scheme.{u}} (G : CommGrp (Over S)) (b : T ⟶ S) :=
  (Over.pullback b).mapCommGrp.obj G

/-- The canonical base-change projection, given by the pullback adjunction counit.
Source: Stacks Tag 01JX (blueprint: def-sfb-coherent-multiplicative-line). -/
def projection {S T : Scheme.{u}} (G : CommGrp (Over S)) (b : T ⟶ S) :
    (Over.map b).obj (changeBase G b).X ⟶ G.X :=
  (Over.mapPullbackAdj b).counit.app G.X

/-- Project a point of the base-changed group to the original group.
Source: Stacks Tag 01JX (blueprint: def-sfb-coherent-multiplicative-line). -/
def projectPoint {S T : Scheme.{u}} (G : CommGrp (Over S)) (b : T ⟶ S)
    (U : Over T) (x : U ⟶ (changeBase G b).X) : (Over.map b).obj U ⟶ G.X :=
  (Over.map b).map x ≫ projection G b

/-- Transport a framed point using a specified identification of the pulled-back line.
Source: Stacks Tags 0097, 01CD (blueprint: def-sfb-coherent-multiplicative-line). -/
def identifyPoint {S T : Scheme.{u}} {G : CommGrp (Over S)} (b : T ⟶ S)
    (E : Raw G) (A : Raw (changeBase G b))
    (e : (tensorPullback ((projection G b).left)).obj E.line ≅ A.line)
    {U : Over T} (v : Point A U) : Point E ((Over.map b).obj U) :=
  ⟨projectPoint G b U v.1,
    v.2 ≪≫ (tensorPullback v.1.left).mapIso e.symm ≪≫
      composite v.1.left ((projection G b).left)
        (projectPoint G b U v.1).left rfl E.line⟩

/-- A specified generic identification recovers both the identity frame and multiplication.
Test on all frames; their local existence makes this exactly equality of the original maps.
Source: BLR 10.1 Proposition 7, p.292
(blueprint: def-sfb-coherent-multiplicative-line). -/
structure Identification {S T : Scheme.{u}} {G : CommGrp (Over S)} (b : T ⟶ S)
    (E : Coherent G) (A : Coherent (changeBase G b)) where
  lineIso : (tensorPullback ((projection G b).left)).obj E.line ≅ A.line
  unit_eq (U : Over T) :
    identifyPoint b E.toRaw A.toRaw lineIso (one A.toRaw U) =
      one E.toRaw ((Over.map b).obj U)
  mul_eq (U : Over T) (v w : Point A.toRaw U) :
    identifyPoint b E.toRaw A.toRaw lineIso (mul A.toRaw v w) =
      mul E.toRaw (identifyPoint b E.toRaw A.toRaw lineIso v)
        (identifyPoint b E.toRaw A.toRaw lineIso w)

end AlgebraicGeometry.MultiplicativeLine
