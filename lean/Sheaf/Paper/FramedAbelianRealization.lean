module

public import Sheaf.Paper.PurityFrameKummer
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary

/-! # Supported Kummer realization of a framed line bundle

Source: Stacks Tags 03AJ, 03PL and 0A45; blueprint main-20261015,
lem-pur-divisor-class, first sentence and final paragraph
(blueprint: def-pur-framed-abelian-realization).

The integral torsor extension remembers the frame on the complementary open.
Scalar extension is performed on roots of unity, never on Gm as a Z/m-module.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
/-- The uniqueness predicate for a prescribed realization equation.
Source: integral derived adjunction, Stacks 03FD
(blueprint: def-pur-framed-abelian-realization). -/
def DivisorUniqueRealization {B : Type v} {X : Type w} (f : B → X) (x : X) : Prop :=
  ∃! b : B, f b = x

/-- Select the uniquely specified datum of the realization equation.
Source: integral derived adjunction, Stacks 03FD
(blueprint: def-pur-framed-abelian-realization). -/
def divisorChooseRealization {B : Type v} {X : Type w} (f : B → X) (x : X)
    (h : DivisorUniqueRealization f x) : B :=
  Classical.choose h

/-- Exact forgetting and precomposition, with its source and target fixed.
Source: Stacks 03FD (blueprint: def-pur-framed-abelian-realization). -/
@[irreducible] def divisorRealizeExact {C D : Type v}
    [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
    [HasExt.{w} C] [HasExt.{w} D] (U : C ⥤ D) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {S B : C} {I : D} (η : I ⟶ U.obj S) (c : Ext.{w} S B 2) :
    Ext.{w} I (U.obj B) 2 :=
  (Ext.mk₀ η).comp (c.mapExactFunctor U) (zero_add 2)

/-- Exact forgetting followed by the supported integral generator, in degree two.
Source: Stacks 03FD and the integral-to-module realization
(blueprint: def-pur-framed-abelian-realization). -/
@[irreducible] def divisorAbelianRealization (P : PurityFiniteSetting.{u}) {Z T : Scheme.{u}}
    (i : Z ⟶ T)
    (b : Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (P.constantEtale Z)) (P.frameTwistEtale T 1) 2) :=
  divisorRealizeExact (Etale.RawModuleScalarComparison.forget P.Coefficient T)
    (Etale.supportedIntegralGenerator P.Coefficient i) b



end WeilConjectures.PurityFiniteSetting
