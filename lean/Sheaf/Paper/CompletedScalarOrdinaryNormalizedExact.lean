/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W5
-/
module

public import Sheaf.Paper.CompletedScalarShift

/-! # Exactness with the counit-normalized ordinary scalar shift

Source: Stacks Tags 06YY and 06YU, ordinary derived tensor exactness
(blueprint: lem-fd-ordinary-scalar-normalized-exact).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory
namespace WeilConjectures

/-- Ordinary derived tensor is exact with its counit-normalized shift.
Source: Stacks Tags 06YY and 06YU; normalized integral completion comparison,
proof step 5 (blueprint: lem-fd-ordinary-scalar-normalized-exact).

Proof: ordinary derived change of rings is the left derived functor of termwise
change of rings on the homotopy category. Its canonical triangulated structure
has shift comparisons induced by the termwise tensor shift and the universal
counit. On flat-term K-flat complexes its counit is invertible. The displayed
normalization therefore uniquely determines the shift component on those
complexes. Every derived object is isomorphic to the localization of such a
complex, so naturality identifies each component with the canonical derived
shift. Transfer the preservation of distinguished triangles along this equality
of shift structures. This includes negative shifts and the zero shift. -/
theorem completedScalarOrdinary_normalized_exact
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (T : AlgebraicGeometry.Scheme.{u})
    (e : (completedDerivedScalarExtension l E L ι T).CommShift ℤ)
    (he : completedScalarShiftOrdinaryNormalization ι T e) :
    (fun [_s : (completedDerivedScalarExtension l E L ι T).CommShift ℤ] ↦
      (completedDerivedScalarExtension l E L ι T).IsTriangulated) (_s := e) := by sorry

end WeilConjectures
