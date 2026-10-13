/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition

/-! # Coordinate invariance of the stalk comparison

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
(blueprint: lem-pc-stalk-comparison-coordinate-invariance).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- Invertibility of the canonical stalk comparison is independent of coordinates.

Proof: the isomorphism c.e followed by d.e.inv identifies P_c and P_d in D(O_X).
Exact stalks and restriction to R carry it to D(R). Uniqueness of the universal
left-derived scalar-extension functor, and cohomologyIso_smul, induce an
A-tensor-R-B-linear isomorphism on the source cohomology objects. Extending to C
preserves this isomorphism. The isomorphism c.e' followed by d.e'.inv similarly
induces an isomorphism from H^i(N_c,z) to H^i(N_d,z), because stalks are exact.
K-flatness of the sheaf representatives gives K-flatness of their stalks by
lem-pc-kflat-stalk-criterion, so ordinary A-to-C extension of these representatives
computes derived pullback. The universal pullback counits and tensorStalkIso
identify its cohomology with the coordinate target before the chain map.
The represents equations express both coordinate maps as the same morphism phi.
After applying stalks, derived cohomology, the two model counit equations and
naturality of tensorStalkIso, they give a commuting square with stalkComparison c
and stalkComparison d as horizontal maps and these two isomorphisms as vertical
maps. Conjugating either horizontal map by the vertical isomorphisms gives the
other; composition with isomorphisms preserves and reflects invertibility.
This argument only uses derived isomorphisms; it does not assume a chain map
between the two coordinate complexes, or that ordinary pullback preserves
quasi-isomorphisms.
Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
(blueprint: lem-pc-stalk-comparison-coordinate-invariance). -/
theorem isIso_stalkComparison_iff_coordinates
    {K : schemeDerivedCategory X} {K' : schemeDerivedCategory X'}
    {φ : (derivedPullback g').obj K ⟶ K'}
    (c d : Coordinates g' K K' φ) (z : X') (i : ℤ) :
    IsIso (stalkComparison f f' g g' sq c z i) ↔
      IsIso (stalkComparison f f' g g' sq d z i) := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
