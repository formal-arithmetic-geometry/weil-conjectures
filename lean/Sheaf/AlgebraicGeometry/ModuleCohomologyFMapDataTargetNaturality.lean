/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap

/-! # Target coefficient naturality for arbitrary resolution data

Source: Stacks Project, Tags 01F8, 01F9 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-data-target-naturality).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Changing the target module commutes with the resolution formula, even when
its two computations use different resolutions.
Source: Stacks Project, Cohomology of Sheaves, Lemma 01F8 and Remark 01FB;
Derived Categories, Lemmas 013P, 013S and 05TG
(blueprint: lem-weil-pbc-module-cohomology-fmap-data-target-naturality).

Proof: lift b to c : D.I -> E.I, and lift the identity of G to
v : D.J -> E.J, both commuting with augmentations. Since E.K is a bounded
below complex of injectives and D.lambda is a quasi-isomorphism, there is a
map e : D.K -> E.K with D.lambda followed by e homotopic to h_*c followed
by E.lambda. Extend the nonnegative complexes by zero to apply 05TG.
The maps D.beta followed by e and v followed by E.beta have homotopic
composites with the augmentation of D.J: use the two compatibility squares,
the augmentation equation for c, and the homotopy just constructed. Uniqueness
up to homotopy (013S) therefore identifies these two maps. Global sections
preserves homotopies, so both comparison squares commute on homology.
Write B_D and B_E for H(Gamma beta), and M_D and M_E for the invertible
vertical homology maps. The squares say B_D H(Gamma e) = H(Gamma v) B_E
and M_D H(Gamma e) = H(Gamma c) M_E, after the canonical section comparisons.
Multiply the second square by the two inverses and substitute the first.
The resulting equality is B_D M_D inverse H(Gamma c) =
H(Gamma v) B_E M_E inverse. Naturality of isoRightDerivedObj for c and v
and naturality of the forgetful homology isomorphisms give the displayed
formula. No invertibility of c, e or b is required. -/
theorem ModuleCohomologyFMapData.map_target_naturality {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf}
    {F F' : SheafOfModules.{u} X.ringCatSheaf}
    (φ : G ⟶ (pushforward h).obj F) (b : F ⟶ F')
    (D : ModuleCohomologyFMapData h G F φ)
    (E : ModuleCohomologyFMapData h G F' (φ ≫ (pushforward h).map b)) (p : ℕ) :
    D.map p ≫ (forget₂ _ AddCommGrpCat.{u}).map
        ((X.toRingedSpace.moduleCohomology p).map b) = E.map p := by sorry

end AlgebraicGeometry.Scheme.Modules
