/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap

/-! # Scalar compatibility of resolution cohomology maps

Source: Stacks Project, Tags 01F8, 01F9 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-scalar-compatibility).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The resolution formula commutes with multiplication by global functions.
Source: Stacks Project, Cohomology of Sheaves, Equation 01F9 and Remark 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-scalar-compatibility).

Proof: apply global sections to D.β and D.lambda. These are maps of modules over
O_Y(Y), so their maps on cycles and boundaries, and hence homology, are linear.
The inverse section comparison D.a.inv is restriction along the equality
h⁻¹(Y) = X by D.sections and respects the O_Y(Y)-action induced by h.appTop.
Consequently D.a.hom and the vertical homology map are O_Y(Y)-linear when
the X-side modules are viewed by restriction of scalars. Its inverse is also
O_Y(Y)-linear: apply the bijective vertical map to the desired scalar identity
and use linearity and injectivity. No inverse of h.appTop is required.
Finally the resolution isomorphisms and the
forgetful homology isomorphisms in D.map come from module morphisms and preserve
scalar multiplication. Composing these scalar identities gives the equation.
This is clause (1) of the parent's argument before bundling a linear map. -/
theorem ModuleCohomologyFMapData.map_smul {X Y : Scheme.{u}} {h : X ⟶ Y}
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    {φ : G ⟶ (pushforward h).obj F} (D : ModuleCohomologyFMapData h G F φ) (p : ℕ)
    (r : Y.ringCatSheaf.obj.obj (op (⊤ : Y.Opens)))
    (x : (Y.toRingedSpace.moduleCohomology p).obj G) :
    (D.map p).hom (r • x) = h.appTop.hom r •
      (show (X.toRingedSpace.moduleCohomology p).obj F from (D.map p).hom x) := by sorry

end AlgebraicGeometry.Scheme.Modules
