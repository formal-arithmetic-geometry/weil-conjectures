/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Lifting proper-support sections over a quasi-compact open of an affine base

Source: Stacks Project, Tags 096V, 09AG and 09AH; the specialization-localization
argument in Steps 3--8 of `lem-exc-proetale-proper-open-sheaf-comparison`.
(blueprint: lem-exc-proetale-proper-qc-open-counit-sections)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- For a quasi-compact open in an affine base, every global section of the proper
pushforward of an extension by zero lifts through the open counit.

Source: Stacks Project, Tags 096V, 09AG and 09AH; Steps 3--8 of the affine support
argument in `lem-exc-proetale-proper-open-sheaf-comparison`.
(blueprint: lem-exc-proetale-proper-qc-open-counit-sections).

Proof: express `O` as a finite union of principal opens, allowing the empty union.
Let `I` be the ideal they generate and localize at the elements invertible modulo `I`.
The principal opens together with this affine localization form a pro-etale cover of
`T`. On each principal open the counit is invertible by the open unit and its triangle
identity. Every point of the localization specializes to the closed complement.
Proper closedness implies that every point of its inverse image in `V` specializes to
the inverse image of that complement: the image of the closure of the point is closed.
Choose finitely many affine charts of this proper inverse image and closed-localize
each chart at that closed fibre. They cover, since opens contain the generalizations
of their points; affine intersections are quasi-compact by separatedness. Thus this is
a pro-etale cover. Tag 09AG makes the extension-by-zero sections zero on every chart,
and separatedness makes the target section zero on the whole inverse image. The
source section on the base localization is also zero by Tag 09AG. Lift by zero there
and by the inverse counit on the principal opens. The lifts agree on overlaps because
the open counit is monic (the presheaf zero-extension counit is monic and module
sheafification is exact). Glue by the sheaf axiom. Constant-coefficient realization
preserves these sections, maps and scalar actions, so the resulting map is exactly
the displayed intrinsic counit. Empty schemes and the zero ring use the same empty
cover and zero-section argument. -/
theorem sfProperQcOpenCounit_sections_surjective {V T : Scheme.{u}} [IsAffine T]
    (p : V ⟶ T) [IsProper p] (O : T.Opens) (hO : IsCompact (O : Set T))
    (M : proEtaleRingModules (pullback p O.ι)
      (proEtaleConstantRing (pullback p O.ι) A)) :
    let F := (sfIntrinsicExtensionByZero (pullback.fst p O.ι) A ⋙
      proEtaleConstantModuleDirectImage p A).obj M
    Function.Surjective
      (((sfIntrinsicExtensionByZeroAdjunction O.ι A).counit.app F).val.app
        (op (ProEt.mk (𝟙 T)))) := by
  sorry

end AlgebraicGeometry.Scheme
