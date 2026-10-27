/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.Paper.CondensedTateRealizationData
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.KFlatTelescopeClosure

/-! # Scalar extension of the integral Tate tensor powers

Source: Stacks 03EK, 06YU, 0G7E and 07A4; Bhatt--Scholze 6.8.4.
(blueprint: lem-pur-condensed-tate-scalar-power-isomorphism)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures WeilConjectures.CondensedERealization

namespace AlgebraicGeometry.ProEtale.CondensedTateRealization

variable (l : ℕ) [Fact l.Prime]

/-- The adjoint of the specified balanced tensor map is invertible before reconstruction.
Source: Stacks 03EK, 06YU, 0G7E and 07A4; Steps 5, 7 and 8 of the realization argument
(blueprint: lem-pur-condensed-tate-scalar-power-isomorphism).

Proof: The integral Tate limit is locally free of rank one over the integral
condensed coefficient ring. Its d-th tensor power is locally free, with degree zero
equal to the regular module. Therefore its degree-zero complex is K-flat: tensoring
an acyclic complex with it can be checked on its trivializing cover, where it is
the identity functor. Integral encoding is an exact equivalence preserving the
underlying sheaves and the normalized scalar actions. Compute derived extension
from the completed ring to rational coefficients on this K-flat single complex.
Change of rings preserves K-flatness, so the second derived extension to the
finite-extension-valued closure is again computed by ordinary tensor. The coefficient
square for integralComparison and integralToQbar_factor identify the composite
coefficient map with the actual integral-to-closure map in the Tate construction.
Thus the source of the adjoint map is represented by B tensor_R integralPower.
The ringed-topos tensor-pullback comparison, applied to the identity topos and
iterated d times, identifies this with (B tensor_R tateModule) tensor_B power d.
Its pure tensor map sends b tensor (z_1 tensor ... tensor z_d) to
(b tensor z_1) tensor (1 tensor z_2) tensor ... tensor (1 tensor z_d); the inverse
multiplies the B-coefficients. Balancing checks both inverse identities. At d=0
these are the multiplication and unit maps B tensor_R R = B. The target is
precisely tateTwistNat in degree zero. Under the ordinary extension/restriction
adjunction the comparison is the balanced family fixed by the same unit and
successor generator equations; balancedPower_existsUnique identifies it with
balancedPower. The section-normalization uniqueness of encodedBalancedPower and
the standard single-functor comparison identify its derived adjoint with the
particular homEquiv transpose displayed below. Hence this transpose is invertible.
This computation uses no derived-limit comparison, constructibility hypothesis,
or choice of a trivializing generator in the resulting global map. -/
theorem scalarBalancedPower_isIso (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] (T : Base k)
    (r : At l (LiftedQ.{u} l) T.scheme) (d : ℕ) :
    IsIso (((scalarAdjunction T.scheme l r).homEquiv
      ((DerivedCategory.singleFunctor _ 0).obj
        ((integralEncoding T.scheme l r).functor.obj (integralPower T.scheme l d)))
      (tateTwistDerived T.scheme l (d : ℤ))).symm
        (derivedBalancedPower T.scheme l r d)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedTateRealization
