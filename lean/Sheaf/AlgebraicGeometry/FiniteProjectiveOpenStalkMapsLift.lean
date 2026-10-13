/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor
/-! # Finite-interval lifting for finite-projective open-site terms

Source: Stacks Project, Tags 09RE and 01CP.
(blueprint: lem-sc-finite-projective-open-stalk-maps-lift).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section
/-- Simultaneously lift a finite family of stalk maps with finite-projective sources.
Source: Stacks Project, Tag 01CP (lemma-stalk-internal-hom), and the finite
matrix calculation of Tags 09RE and 0BC7 (2).
(blueprint: lem-sc-finite-projective-open-stalk-maps-lift).

Proof: For each source choose its given retraction into a finite free module.
Precompose the stalk map with the stalk of the projection from that free module.
The resulting map is determined by the images of its finitely many basis vectors.
Represent those target-stalk vectors by sections on neighbourhoods of x inside T.
There are finitely many sources and basis vectors, so intersect all these opens.
The represented sections define maps from the restricted finite free modules;
precompose with the restricted inclusions to obtain the requested source maps.
The splitting identity proves agreement on stalks. The equivalence from the
slice site to the open subscheme, followed by the usual restriction-stalk
comparison and restriction of scalars, gives a natural isomorphism e on all
module sheaves. Naturality identifies the germ equalities with the displayed
conjugation formula. The empty index family or rank zero needs no sections:
use T and the zero maps. No boundedness or complex structure is involved. -/
theorem exists_finite_projective_open_stalk_maps_lift
    (X : Scheme.{u}) (V : X.Opens) (x : X) (hxV : x ∈ V)
    (T : X.Opens) (hTV : T ≤ V) (hxT : x ∈ T)
    (I : Type u) [Finite I]
    (M N : I → SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (hM : ∀ q, ∃ m : ℕ,
      ∃ (ι : M q ⟶ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin m)) ⟶ M q),
        ι ≫ π = 𝟙 (M q))
    (h : ∀ q, (openModuleStalkFunctor X V ⟨x, hxV⟩).obj (M q) ⟶
      (openModuleStalkFunctor X V ⟨x, hxV⟩).obj (N q)) :
    ∃ (Z : X.Opens) (hZT : Z ≤ T) (hxZ : x ∈ Z),
      let R := SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE (hZT.trans hTV))
      let S := openModuleStalkFunctor X Z ⟨x, hxZ⟩
      let F := openModuleStalkFunctor X V ⟨x, hxV⟩
      ∃ (e : R ⋙ S ≅ F) (k : ∀ q, R.obj (M q) ⟶ R.obj (N q)),
        ∀ q, S.map (k q) = (e.app (M q)).hom ≫ h q ≫ (e.app (N q)).inv := by
  sorry
end
end AlgebraicGeometry.Scheme
