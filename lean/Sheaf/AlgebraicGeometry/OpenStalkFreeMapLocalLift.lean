/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Local lifting from a finite free open-site stalk

Source: Stacks Project, Tag 01CP, and Sheaves Tag 00A0 (3).
(blueprint: lem-sc-open-stalk-free-map-local-lift).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Restriction-stalk comparisons can be chosen independently of the modules, and
one map from a finite free stalk lifts on every sufficiently small neighbourhood.

Source: Stacks Project, Modules Tag 01CP, finite-generator lifting in
`lemma-stalk-internal-hom`; Sheaves Tag 00A0 (3), `lemma-restrict`, restriction and stalks.
(blueprint: lem-sc-open-stalk-free-map-local-lift).

Proof: Identify the slice site over U with the open subscheme U. For each W inside
U containing x, send a germ on W to the same germ on U, transporting scalars along
the open-immersion stalk-ring maps. Neighbourhoods contained in W are cofinal, so
this gives an isomorphism for every module. The germ formula commutes with every
module morphism, hence gives the natural isomorphism e W. These comparisons are
chosen before the source, target, and map. A finite free sheaf has finitely many
basis germs. Apply t to these germs and represent their images by sections of N
on neighbourhoods of x. Intersect the finitely many neighbourhoods with U to get
V. For any W contained in V, restrict these sections and use the free sheaf
universal property to define g on W. Its stalk has the prescribed images of all
basis germs; linearity then gives the displayed equality with the comparisons.
The comparison germ formula is unchanged upon further restriction, which proves
the assertion for every W below V. For rank zero take V=U and the zero morphism.
No finiteness of N or affineness of U is used. This is a single sheaf-map lifting
statement; it contains neither complexes nor an infinite family of maps. -/
theorem exists_open_stalk_free_map_local_lifts
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) :
    ∃ e : ∀ (W : X.Opens) (hxW : x ∈ W) (hWU : W ≤ U),
      SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hWU) ⋙
        openModuleStalkFunctor X W ⟨x, hxW⟩ ≅ openModuleStalkFunctor X U ⟨x, hxU⟩,
      ∀ (m : ℕ) (N : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (t : (openModuleStalkFunctor X U ⟨x, hxU⟩).obj
          (SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ⟶
          (openModuleStalkFunctor X U ⟨x, hxU⟩).obj N),
        ∃ (V : X.Opens) (_hxV : x ∈ V) (_hVU : V ≤ U),
          ∀ (W : X.Opens) (hxW : x ∈ W) (_hWV : W ≤ V) (hWU : W ≤ U),
            let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
              (homOfLE hWU)
            ∃ g : R.obj (SheafOfModules.free
                (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ⟶
                R.obj N,
              (openModuleStalkFunctor X W ⟨x, hxW⟩).map g =
                (e W hxW hWU).hom.app _ ≫ t ≫ (e W hxW hWU).inv.app N := by sorry

end
end AlgebraicGeometry.Scheme
