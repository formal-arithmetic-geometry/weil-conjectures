/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.DivisorModule
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.DivisorModuleLocal
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-! # Tensor compatibility of the explicit divisor module

Source: blueprint lem-sc-divisor-class-curve, proof of the homomorphism assertion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- Addition of arbitrary divisors corresponds to tensor product of their explicit modules.
Source: blueprint lem-sc-divisor-class-curve, proof of the homomorphism assertion;
Stacks Project, Divisors, Tag 02SL (blueprint: lem-sc-divisor-module-tensor-add).

Proof: On each open, multiply the locally constant rational functions representing sections.
For nonzero values the valuation is additive, so the bounds for A and B imply the bound for
A+B; a zero factor gives the permitted zero section. The resulting map is bilinear over
regular sections and commutes with restrictions. The universal property of the sheafified
presheaf tensor product therefore gives a module morphism O(A) tensor O(B) to O(A+B).
At a closed point P choose a uniformizer t. Apply Divisor.module_local to A, B and A+B,
using the same t, and intersect their neighbourhoods. These identify the three modules with
 t^(-A(P)) O, t^(-B(P)) O and t^(-A(P)-B(P)) O. In these coordinates the constructed morphism
is multiplication O tensor O to O, hence is an isomorphism. The neighbourhoods cover every
closed point; they also contain the generic point, which belongs to every nonempty open.
Every point is either closed or generic, and a closed point exists, by
Scheme.smooth_connected_curve_local_rings. Thus the morphism is an isomorphism on an open
cover, and hence globally. Zero divisors and negative coefficients require no exception:
the uniformizer powers are integer powers in the function field. Properness is never used. -/
theorem Divisor.nonempty_module_tensor_add_iso
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] (A B : C.Divisor) :
    Nonempty (A.moduleOfSmoothConnectedCurve k C f ⊗
      B.moduleOfSmoothConnectedCurve k C f ≅
        (A + B).moduleOfSmoothConnectedCurve k C f) := by sorry

end AlgebraicGeometry.Scheme
