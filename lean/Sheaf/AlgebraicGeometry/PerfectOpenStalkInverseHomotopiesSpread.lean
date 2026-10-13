/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor

/-! # Spreading two inverse homotopies

Source: Stacks Project, Tag 09RE, affine proof, and Tag 0BC7 (2).
(blueprint: lem-sc-perfect-open-stalk-inverse-homotopies-spread).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Two given inverse homotopies at a stalk spread after shrinking a lifted map.
Source: Stacks Project, Tag 09RE, affine proof's equality in the homotopy category;
Tag 0BC7 (2), finite-component homotopy calculation, and Tag 00CR.
(blueprint: lem-sc-perfect-open-stalk-inverse-homotopies-spread).

Proof: Work on the affine V. Restriction preserves the finite-free retractions
and the support bounds. For each of the two stalk homotopies only finitely many
reverse-degree components can be nonzero. Sandwich each component between the
restricted finite-free retractions, represent its finitely many matrix entries
by sections on principal opens containing x inside V, and intersect these opens.
Sandwich the resulting maps back to the complex terms. The two homotopy equations
in each of the finitely many relevant degrees hold at the stalk. Sandwich their
errors into the finite free terms and use the germ equality criterion to shrink
once more until every error entry vanishes. Outside the support intervals the
terms are zero and the equations hold uniquely. The reverse-degree support gives
Homotopy.zero. Restrict g to W and identify iterated restriction with restriction
from U to W through the canonical slice-site comparison; its naturality identifies
both composites with the stated maps. The same construction handles zero terms,
disjoint support intervals and arbitrary non-Noetherian rings. No quasi-isomorphism
hypothesis is used; the two specified homotopies are the input. -/
theorem exists_affine_perfect_open_stalk_inverse_homotopies_spread
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) (hU : IsAffineOpen U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) (hQ : IsStrictlyPerfect X U Q)
    (f : P ⟶ Q) (V : X.Opens) (hxV : x ∈ V) (hV : IsAffineOpen V) (hVU : V ≤ U)
    (g : ((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      ((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).obj P)
    (hfg : Nonempty (Homotopy
      (((openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)).map
        ((((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).map f) ≫ g)) (𝟙 _)))
    (hgf : Nonempty (Homotopy
      (((openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)).map
        (g ≫ (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).map f))) (𝟙 _))) :
    ∃ (W : X.Opens) (_hxW : x ∈ W) (_hW : IsAffineOpen W) (hWU : W ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)
      ∃ (gW : R.obj Q ⟶ R.obj P),
        Nonempty (Homotopy (R.map f ≫ gW) (𝟙 _)) ∧
        Nonempty (Homotopy (gW ≫ R.map f) (𝟙 _)) := by sorry

end
end AlgebraicGeometry.Scheme
