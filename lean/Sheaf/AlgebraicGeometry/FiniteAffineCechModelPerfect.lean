/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.FiniteAffineCechModel
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-! # Perfection of the specified finite affine Čech complex

Source: Stacks Project, Tags 01XB, 01XD, 01FK, 0B91(2), and 0A1H.
(blueprint: lem-pc-finite-affine-cech-model-perfect).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit finite affine Čech model represents a perfect derived object.
This asserts only perfection of the already constructed complex, not existence,
termwise flatness, bounds, or any base-change comparison.
Source: Stacks Project, Tags 01XB, 01XD, 01FK, 0B91(2), and proof of 0A1H.
(blueprint: lem-pc-finite-affine-cech-model-perfect).

Proof: Put Y=f^{-1}(U), p=f|_U, and G=F|_Y. Restriction is base change by the
open immersion U -> T, so p is proper and of finite presentation, while G is
finitely presented and flat over U. Since U is affine and p is separated,
all nonempty finite intersections of the affine covering V are affine.
The augmented Čech resolution of G is exact. Each of its intersection terms
is acyclic for direct image to U: on each affine open of U this is affine
acyclicity (01XB), since the intersection-to-U map is affine. Hence its
section complex represents Rp_*G. The ordered comparison (01FK) identifies
this complex with the increasing-tuple section complex used in
finiteAffineCechModel. The canonical affine chart and scalar restriction in
that definition preserve this identification, producing a derived isomorphism
from Q(finiteAffineCechModel p G V) to Rp_*G. By 0B91(2), Rp_*G is perfect:
its proof 0A1H descends p and G to a Noetherian stage, applies proper coherence
and finite Tor dimension there, then pulls the perfect object back to U.
For each local strictly perfect witness, compose its derived isomorphism
with the restriction of the preceding comparison. This proves IsPerfect in
exactly the supplied derived localization and supplied open-site localization
family; it does not require globally supplied localizations for every scheme.
If the cover has no members, its covering condition forces Y empty, so the
specified complex and its direct image are zero, which is strictly perfect.
Zero rings and empty affine opens likewise cause no exception. -/
theorem finiteAffineCechModel_perfect
    {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation]
    (hF : F.IsFlatOver f) (U : T.Opens) (hU : IsAffine U.toScheme)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ W : U.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over W))]
    {r : ℕ} (V : Fin r → (f ⁻¹ᵁ U).toScheme.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcover : iSup V = ⊤) :
    U.toScheme.IsPerfect ((DerivedCategory.Q
      (C := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))).obj
        (finiteAffineCechModel (f ∣_ U) (F.restrict (f ⁻¹ᵁ U).ι) V)) := by sorry

end AlgebraicGeometry.Scheme.Modules
