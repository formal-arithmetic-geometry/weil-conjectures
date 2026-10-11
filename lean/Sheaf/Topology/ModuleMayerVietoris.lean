/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.Topology.OpenModuleCohomology
import Mathlib.Algebra.Exact.Basic

/-! # Mayer--Vietoris for modules on a ringed space

Source: Stacks Project, Cohomology, Lemma 20.8.2, Tag 01EB
(blueprint: lem-sc-mayer-vietoris-ringed-space).
-/

universe v

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- The Mayer--Vietoris long exact sequence for `O_X`-modules. We state it for every
pair of opens simultaneously, on their union; taking `U ⊔ V = ⊤` gives the sequence
on `X`. The connecting maps are natural transformations, hence natural in the module.
The last equality is compatibility with restriction to any open `W`. The remaining
squares commute by functoriality of cohomology restriction.

Source: Stacks Project, Cohomology, Lemma 20.8.2, Tag 01EB
(blueprint: lem-sc-mayer-vietoris-ringed-space).

Proof: Choose an injective resolution of the module
(`def-sc-ringed-space-module-cohomology`). Its restriction to every open remains an
injective resolution (`lem-sc-ringed-space-restrict-injective-resolution`). The sheaf
condition gives left exactness of sections on the two-open cover, and injectivity
makes the difference of restrictions surjective
(`lem-sc-ringed-space-injective-restriction-surjective`). This is a short exact
sequence of section complexes. Its long exact cohomology sequence
(`lem-weil-pbc-complex-ses-homology-long-exact`) has the indicated restriction maps.
For a module morphism, lift to injective resolutions
(`lem-weil-pbc-derived-functor-map-via-lift`) and restrict these lifts to the opens.
Naturality of the complex long exact sequence
(`lem-weil-pbc-complex-ses-long-exact-naturality`) gives natural connecting maps,
independent of the lift. Finally restrict the chosen resolution to `W`; it remains
injective, and restriction of sections is a morphism of the two short exact sequences
of complexes. The same long exact sequence naturality gives the last equality. -/
theorem module_mayerVietoris (X : RingedSpace.{v}) :
    let H := openModuleCohomology X
    let r : ∀ (p : ℕ) {U V : Opens X}, (V ⟶ U) → (H p U ⟶ H p V) :=
      fun p {_ _} i => openModuleCohomologyRestriction X p i
    ∃ δ : ∀ (U V : Opens X) (p : ℕ), H p (U ⊓ V) ⟶ H (p + 1) (U ⊔ V),
      (∀ (U V : Opens X) (F : SheafOfModules.{v} (moduleRings X)),
        Function.Injective (fun x : (H 0 (U ⊔ V)).obj F =>
          ((r 0 (homOfLE (show U ≤ U ⊔ V from le_sup_left))).app F x,
            (r 0 (homOfLE (show V ≤ U ⊔ V from le_sup_right))).app F x))) ∧
      (∀ (U V : Opens X) (F : SheafOfModules.{v} (moduleRings X)) (p : ℕ),
        Function.Exact
          (fun x : (H p (U ⊔ V)).obj F =>
            ((r p (homOfLE (show U ≤ U ⊔ V from le_sup_left))).app F x,
              (r p (homOfLE (show V ≤ U ⊔ V from le_sup_right))).app F x))
          (fun x : (H p U).obj F × (H p V).obj F =>
            (r p (homOfLE (show U ⊓ V ≤ U from inf_le_left))).app F x.1 -
              (r p (homOfLE (show U ⊓ V ≤ V from inf_le_right))).app F x.2) ∧
        Function.Exact
          (fun x : (H p U).obj F × (H p V).obj F =>
            (r p (homOfLE (show U ⊓ V ≤ U from inf_le_left))).app F x.1 -
              (r p (homOfLE (show U ⊓ V ≤ V from inf_le_right))).app F x.2)
          ((δ U V p).app F) ∧
        Function.Exact ((δ U V p).app F)
          (fun x : (H (p + 1) (U ⊔ V)).obj F =>
            ((r (p + 1) (homOfLE (show U ≤ U ⊔ V from le_sup_left))).app F x,
              (r (p + 1) (homOfLE (show V ≤ U ⊔ V from le_sup_right))).app F x))) ∧
      (∀ (U V W : Opens X) (p : ℕ),
        δ U V p ≫ r (p + 1) (homOfLE (sup_le_sup inf_le_left inf_le_left)) =
          r p (homOfLE (inf_le_inf inf_le_left inf_le_left)) ≫
            δ (U ⊓ W) (V ⊓ W) p) := by
  sorry

end AlgebraicGeometry.RingedSpace
