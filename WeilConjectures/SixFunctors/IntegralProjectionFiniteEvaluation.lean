/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CondensedProjectionScalarSquare
public import WeilConjectures.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
import WeilConjectures.AlgebraicGeometry.CondensedCtfSixFunctorStability

/-! # Finite quotient evaluation of the compact-support projection square

Source: latest blueprint, fix-prop-projection-formula.proof.md, compatibility under
successive coefficient reductions; Stacks Project, Tag 0E48, remark-compatible-with-diagram.
(blueprint: lem-sf-integral-projection-finite-evaluation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The bundled condensed map induced by the finite discrete quotient `A → A ⧸ J`.
Source: the finite case of `IsListedScalarCoefficientMap`.
(blueprint: lem-sf-integral-projection-finite-evaluation). -/
def finiteQuotientScalarMap
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] (J : Ideal A)
    [TopologicalSpace (A ⧸ J)] [IsTopologicalRing (A ⧸ J)]
    [DiscreteTopology (A ⧸ J)] [Finite (A ⧸ J)] :
    scalarSixTopologicalRing.{u} A ⟶ scalarSixTopologicalRing.{u} (A ⧸ J) :=
  scalarSixContinuousMap (Ideal.Quotient.mk J) continuous_of_discreteTopology

/-- The coordinate `v = (1 ⊗ a_L) e_X`, using the specified balanced tensorator
and the canonical scalar/pullback comparison, without a flatness assumption.
Source: the displayed coordinate v of the node
(blueprint: lem-sf-integral-projection-finite-evaluation). -/
def finiteProjectionTensorPullMap
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A]
    (J : Ideal A) [TopologicalSpace (A ⧸ J)] [IsTopologicalRing (A ⧸ J)]
    [DiscreteTopology (A ⧸ J)] [Finite (A ⧸ J)]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules (scalarSixTopologicalRing A).X X))
    (L : DerivedCategory
      (ModuleRingedComparison.internalModules (scalarSixTopologicalRing A).X Y)) :
    (scalarSixChange (finiteQuotientScalarMap A J) X).obj
        (K ⊗ ((upperStar (scalarSixTopologicalRing A).X f).leftDerivedFunctor).obj L) ⟶
      (scalarSixChange (finiteQuotientScalarMap A J) X).obj K ⊗
        ((upperStar (scalarSixTopologicalRing (A ⧸ J)).X f).leftDerivedFunctor).obj
          ((scalarSixChange (finiteQuotientScalarMap A J) Y).obj L) :=
  (scalarSixTensorIso (finiteQuotientScalarMap A J) X K
      (((upperStar (scalarSixTopologicalRing A).X f).leftDerivedFunctor).obj L)).hom ≫
    ((scalarSixChange (finiteQuotientScalarMap A J) X).obj K ◁
      (condensedScalarPullbackIso (finiteQuotientScalarMap A J) f).hom.app L)

/-- The source coordinate `s = (b_K ⊗ 1) e_Y`, with the same tensor comparison as v.
Source: the displayed endpoint map s of the node
(blueprint: lem-sf-integral-projection-finite-evaluation). -/
def finiteProjectionSourceMap
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A]
    (J : Ideal A) [TopologicalSpace (A ⧸ J)] [IsTopologicalRing (A ⧸ J)]
    [DiscreteTopology (A ⧸ J)] [Finite (A ⧸ J)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules (scalarSixTopologicalRing A).X X))
    (L : DerivedCategory
      (ModuleRingedComparison.internalModules (scalarSixTopologicalRing A).X Y)) :
    (scalarSixChange (finiteQuotientScalarMap A J) Y).obj
        ((rightDerivedLowerShriekOfCompactification (scalarSixTopologicalRing A).X c).obj K ⊗ L) ⟶
      (rightDerivedLowerShriekOfCompactification (scalarSixTopologicalRing (A ⧸ J)).X c).obj
          ((scalarSixChange (finiteQuotientScalarMap A J) X).obj K) ⊗
        (scalarSixChange (finiteQuotientScalarMap A J) Y).obj L :=
  (scalarSixTensorIso (finiteQuotientScalarMap A J) Y
      ((rightDerivedLowerShriekOfCompactification (scalarSixTopologicalRing A).X c).obj K) L).hom ≫
    ((scalarCompactSupportMap (finiteQuotientScalarMap A J) c.i c.g).app K ▷
      (scalarSixChange (finiteQuotientScalarMap A J) Y).obj L)

/-- The target coordinate `r = F_B(v) b_H`, for `H = K ⊗ Lf_A^* L`.
Source: the displayed endpoint map r of the node
(blueprint: lem-sf-integral-projection-finite-evaluation). -/
def finiteProjectionTargetMap
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A]
    (J : Ideal A) [TopologicalSpace (A ⧸ J)] [IsTopologicalRing (A ⧸ J)]
    [DiscreteTopology (A ⧸ J)] [Finite (A ⧸ J)]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules (scalarSixTopologicalRing A).X X))
    (L : DerivedCategory
      (ModuleRingedComparison.internalModules (scalarSixTopologicalRing A).X Y)) :
    (scalarSixChange (finiteQuotientScalarMap A J) Y).obj
        ((rightDerivedLowerShriekOfCompactification (scalarSixTopologicalRing A).X c).obj
          (K ⊗ ((upperStar (scalarSixTopologicalRing A).X f).leftDerivedFunctor).obj L)) ⟶
      (rightDerivedLowerShriekOfCompactification (scalarSixTopologicalRing (A ⧸ J)).X c).obj
        ((scalarSixChange (finiteQuotientScalarMap A J) X).obj K ⊗
          ((upperStar (scalarSixTopologicalRing (A ⧸ J)).X f).leftDerivedFunctor).obj
            ((scalarSixChange (finiteQuotientScalarMap A J) Y).obj L)) :=
  (scalarCompactSupportMap (finiteQuotientScalarMap A J) c.i c.g).app
      (K ⊗ ((upperStar (scalarSixTopologicalRing A).X f).leftDerivedFunctor).obj L) ≫
    (rightDerivedLowerShriekOfCompactification (scalarSixTopologicalRing (A ⧸ J)).X c).map
      (finiteProjectionTensorPullMap A J f K L)

/-- Finite quotient evaluation of the specified compactification projection map.

The first clause records the balanced tensor comparison on all ambient objects.
The following clauses give the compact-support comparisons, invertibility of v, s, r,
two-input naturality of s and r, and the commuting projection square.

Source: latest blueprint, fix-prop-projection-formula.proof.md, compatibility under
successive coefficient reductions; Stacks Project, Tag 0E48, remark-compatible-with-diagram.
(blueprint: lem-sf-integral-projection-finite-evaluation).

Proof:
1. The finite quotient is a listed coefficient map. Pullback and tensor stability put
   Lf_A^* L and H in Dctf; scalar change preserves these finite-Tor domains.
2. Take e from scalarSixTensorIso, a from condensedScalarPullbackIso, and b from
   scalarCompactSupportMap. The compact-support scalar theorem makes b_K and b_H
   invertible. Tensoring and functoriality therefore make v, s and r invertible.
3. For maps of K and L, naturality of e and a gives naturality of v. Naturality of b,
   followed by functoriality of F_B, gives the displayed two-input equations for s and r.
4. Apply condensedProjectionScalarSquare to the quotient map, c, K and L. Its left
   composite is s followed by the B projection; its right composite is the A projection
   after scalar change, followed by r. Symmetry gives exactly the last clause.
-/
theorem integralProjectionFiniteEvaluation
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (_hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell k)
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A]
    (J : Ideal A) [TopologicalSpace (A ⧸ J)] [IsTopologicalRing (A ⧸ J)]
    [DiscreteTopology (A ⧸ J)] [Finite (A ⧸ J)]
    (n : ℕ) (_hA : (ell : A) ^ n = 0)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (K : ConstantModelConstructibleFiniteTor
      (scalarSixTopologicalRing A).X X.left)
    (L : ConstantModelConstructibleFiniteTor
      (scalarSixTopologicalRing A).X Y.left) :
    (∀ (Z : Scheme.{u})
      (U V : DerivedCategory
        (ModuleRingedComparison.internalModules (scalarSixTopologicalRing A).X Z)),
      IsIso (scalarSixTensorIso (finiteQuotientScalarMap A J) Z U V).hom) ∧
    IsIso ((scalarCompactSupportMap (finiteQuotientScalarMap A J) c.i c.g).app K.obj) ∧
    IsIso ((scalarCompactSupportMap (finiteQuotientScalarMap A J) c.i c.g).app
      (K.obj ⊗ ((upperStar (scalarSixTopologicalRing A).X f.left).leftDerivedFunctor).obj L.obj)) ∧
    IsIso (finiteProjectionTensorPullMap A J f.left K.obj L.obj) ∧
    IsIso (finiteProjectionSourceMap A J c K.obj L.obj) ∧
    IsIso (finiteProjectionTargetMap A J c K.obj L.obj) ∧
    (∀ (K' : ConstantModelConstructibleFiniteTor (scalarSixTopologicalRing A).X X.left)
      (L' : ConstantModelConstructibleFiniteTor (scalarSixTopologicalRing A).X Y.left)
      (m : K.obj ⟶ K'.obj) (w : L.obj ⟶ L'.obj),
      (scalarSixChange (finiteQuotientScalarMap A J) Y.left).map
          ((rightDerivedLowerShriekOfCompactification (scalarSixTopologicalRing A).X c).map m ⊗ₘ
            w) ≫
        finiteProjectionSourceMap A J c K'.obj L'.obj =
      finiteProjectionSourceMap A J c K.obj L.obj ≫
        ((rightDerivedLowerShriekOfCompactification (scalarSixTopologicalRing (A ⧸ J)).X c).map
            ((scalarSixChange (finiteQuotientScalarMap A J) X.left).map m) ⊗ₘ
          (scalarSixChange (finiteQuotientScalarMap A J) Y.left).map w)) ∧
    (∀ (K' : ConstantModelConstructibleFiniteTor (scalarSixTopologicalRing A).X X.left)
      (L' : ConstantModelConstructibleFiniteTor (scalarSixTopologicalRing A).X Y.left)
      (m : K.obj ⟶ K'.obj) (w : L.obj ⟶ L'.obj),
      (scalarSixChange (finiteQuotientScalarMap A J) Y.left).map
          ((rightDerivedLowerShriekOfCompactification (scalarSixTopologicalRing A).X c).map
            (m ⊗ₘ ((upperStar (scalarSixTopologicalRing A).X f.left).leftDerivedFunctor).map w)) ≫
        finiteProjectionTargetMap A J c K'.obj L'.obj =
      finiteProjectionTargetMap A J c K.obj L.obj ≫
        (rightDerivedLowerShriekOfCompactification (scalarSixTopologicalRing (A ⧸ J)).X c).map
          ((scalarSixChange (finiteQuotientScalarMap A J) X.left).map m ⊗ₘ
            ((upperStar (scalarSixTopologicalRing (A ⧸ J)).X f.left).leftDerivedFunctor).map
              ((scalarSixChange (finiteQuotientScalarMap A J) Y.left).map w))) ∧
    (scalarSixChange (finiteQuotientScalarMap A J) Y.left).map
        (exceptionalProjectionMorphismOfCompactification (scalarSixTopologicalRing A).X c
          K.obj L.obj) ≫
      finiteProjectionTargetMap A J c K.obj L.obj =
    finiteProjectionSourceMap A J c K.obj L.obj ≫
      exceptionalProjectionMorphismOfCompactification (scalarSixTopologicalRing (A ⧸ J)).X c
        ((scalarSixChange (finiteQuotientScalarMap A J) X.left).obj K.obj)
        ((scalarSixChange (finiteQuotientScalarMap A J) Y.left).obj L.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
