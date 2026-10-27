/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.SixFunctors.RationalOperations
public import Sheaf.SixFunctors.VerdierExchangeData

/-! # Integral dualizing presentations and the exceptional coefficient unit

Source: blueprint prop-coef-integral-dualizing.proof.md, first paragraph, and
prop-functor-package.proof.md, clause (7).
(blueprint: lem-sf-integral-dualizing-exceptional-unit).

This compares objects only. It asserts no Verdier anti-equivalence or compatibility
of evaluation or biduality; those are separate coefficient-duality theorems.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.ConstructibleExceptionalCoefficients

namespace WeilConjectures

/-- A coherent integral dualizing presentation is the exceptional image of the
coefficient unit in any normalized constructible operation system.

Source: blueprint prop-coef-integral-dualizing.proof.md, first paragraph (exceptional
coefficient comparison and reconstruction), used by prop-functor-package.proof.md (7).
(blueprint: lem-sf-integral-dualizing-exceptional-unit).

Proof:
1. Put V = a_R^! U using S at integralDualizingCompactification D T. Its ambient
   realization is derived complete since V belongs to the integral finite-Tor
   category. The same is true of w.omega by its integral constructibility.
2. Reduce the given unit isomorphism modulo each positive power of the uniformizer.
   The constant-coefficient reduction comparison identifies this with the finite
   coefficient unit. The right-adjoint coefficient comparison of S, followed by
   S.ring.finiteRight, identifies each reduction of V with the prescribed finite
   dualizing term. The mate counit equations and the coefficient cocycle identify
   their restricted transition maps with integralDualizingExceptionalTransition.
3. The maps w.reduction identify the reductions of w.omega with those same finite
   terms. The equation w.coherent is exactly the transition square. Composing the
   inverse of the comparisons for V with w.reduction therefore gives isomorphisms
   between the two restricted reduction towers, commuting with every transition.
4. Use the canonical Roos triangles supplied by derived completeness for the two
   objects. The products of the isomorphisms in step 3 conjugate the two maps
   1 - shift. Rotate the triangles and complete that square to a morphism of
   distinguished triangles. Its two product components are isomorphisms, hence
   its remaining component is an isomorphism. Invert it if necessary to obtain
   the displayed isomorphism from the realization of V to w.omega.obj.

For the empty scheme both objects are zero. At the coefficient point this is the
identity-adjunction value of the regular module. No choice of an arbitrary lift of
finite objects is used, and no equality of integral arrows is inferred from reductions.
-/
theorem integral_dualizing_exceptional_unit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    (S : RationalOperations.structureSystem l T D hl Ω)
    (w : IntegralFiniteExtension.DualizingDatum l T D hl E)
    (U : ConstructibleExceptionalCoefficients.C l Ω
      (Spec (.of D.k)) (.integral { carrier := E }))
    (hU : Nonempty ((RingStage.inclusion l Ω (Spec (.of D.k))
      (.integral { carrier := E })).obj U ≅
        VerdierExchange.ringUnit l (Spec (.of D.k)) (.integral { carrier := E }))) :
    Nonempty ((RingStage.inclusion l Ω T (.integral { carrier := E })).obj
      ((S.ring.operation (integralDualizingCompactification D T)
        (.integral { carrier := E })).G.obj U) ≅ w.omega.obj) := by sorry

end WeilConjectures
