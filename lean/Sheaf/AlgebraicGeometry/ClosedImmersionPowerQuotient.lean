/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient

/-! # The normalized quotient comparison for an ideal-power closed immersion

Source: Stacks Project, Lemma 087T and equation 0880.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The quotient by an ideal power is the pushforward of restriction, with its
projection identified with the unit of the supplied adjunction.
Source: Stacks Project, Lemma 087T (lemma-i-star-equivalence), equation 0880.
(blueprint: lem-weil-pbc-closed-immersion-power-quotient).

Proof: On each affine open, the image of the recursively defined ideal-sheaf power
has range J(U)^n, by induction using the affine tensor multiplication calculation.
Thus its product with F has the same image subobject as multiplication by (J^n).
The equality is checked on affine opens and glued by sheaf separatedness. Replace
J^n by the kernel of j. The closed-immersion unit quotient theorem identifies the
cokernel of this image inclusion with j_*j^*F, taking the projection to the canonical
adjunction unit. Equal image subobjects induce the unique quotient isomorphism
preserving projections. Finally compose with the pushforward of leftAdjointUniq
from the canonical adjunction to a; its unit equation gives the claimed equality.
The zero power is the unit ideal, so the closed subscheme and both quotient objects
are zero; zero ideals and zero modules give the same calculation. -/
theorem closedImmersion_power_quotient {X Z : Scheme.{v}} (J : X.IdealSheafData)
    (n : ℕ) (j : Z ⟶ X) [IsClosedImmersion j] (hj : j.ker = J ^ n)
    (a : Scheme.Modules.tensorPullback j ⊣ Scheme.Modules.pushforward j)
    (F : X.Modules) :
    ∃ e : formalModuleQuotient J n F ≅
        (Scheme.Modules.pushforward j).obj ((Scheme.Modules.tensorPullback j).obj F),
      formalModuleQuotientπ J n F ≫ e.hom = a.unit.app F := by sorry

end AlgebraicGeometry
