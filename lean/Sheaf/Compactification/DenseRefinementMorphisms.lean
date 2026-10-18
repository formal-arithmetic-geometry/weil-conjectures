/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import WeilConjectures.Compactification.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.Compactification.BoundaryRefinement
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.TensorPullback
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Topology.InverseImageModule
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Topology.Sheaves.Functors
import WeilConjectures.AlgebraicGeometry.Picard.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Morphisms out of a dense compactification

Source: blueprint main-20261015, sec-nagata-compactification,
`det-nagata-refinement-morphisms` (blueprint: det-nagata-refinement-morphisms).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism from a dense compactification to a compactification is proper, preserves
exactly the distinguished open, and is unique among morphisms satisfying the two
commuting triangles. Source: blueprint main-20261015, sec-nagata-compactification,
`det-nagata-refinement-morphisms` (blueprint: det-nagata-refinement-morphisms).

Proof (the five steps of the DAG node):
1. The structure maps are proper by `def-nagata-compactification`; the target structure
   map is separated by `def-weil-proper-morphism`. Apply
   `lem-weil-pbc-proper-over-separated` to `hS` (Stacks Tag 01W6).
2. Let `V` be the inverse image of `c.obj.i.opensRange`. The open immersion identifies
   `X` with its open image (`def-weil-open-immersion`), so `V` is the base change of `h`
   along `c.obj.i` (`def-pc-base-change`). Its projection `g` to `X` is proper by
   `lem-weil-pbc-proper-base-change`, hence separated. The equality `hj` constructs a
   section `s : X ⟶ V` with composite into the ambient scheme equal to `c'.obj.i`.
3. By `lem-weil-pbc-section-separated-closed-immersion`, `s` is a closed immersion.
   Its image is also open because `c'.obj.i` is open. Its complement `V''` in `V` is
   therefore open in the ambient scheme (`def-weil-closed-immersion`).
4. Density and quasi-compactness give an injective map from the ambient structure sheaf
   to the direct image from `X` (`def-nagata-dense-compactification` and
   `def-nagata-scheme-theoretically-dense-open`). Its restriction to `V''` has zero
   target, so the structure sheaf on `V''` is zero. Every affine open of `V''` then has
   zero coordinate ring and empty spectrum; hence `V''` is empty. Thus the inverse-image
   open equals `c'.obj.i.opensRange`, including its restricted structure sheaf. This is
   `det-nagata-definition-refinement` for the two triangles supplied by `hS` and `hj`.
5. For uniqueness, any competing `h'` agrees with `h` after `c'.obj.i` and over `S`.
   Apply `lemma-nagata-ext-scheme-theoretically-dominant-separated` using `hc'` and
   separatedness of the proper target structure map (Stacks Tag 01RH). -/
theorem denseCompactification_refinement_morphisms {X S : Scheme.{u}} {f : X ⟶ S}
    (c' c : Compactification.QuasiCompactObjects f)
    (hc' : IsSchemeTheoreticallyDominant c'.obj.i)
    (h : c'.obj.Z ⟶ c.obj.Z)
    (hS : h ≫ c.obj.g = c'.obj.g)
    (hj : c'.obj.i ≫ h = c.obj.i) :
    IsProper h ∧
      Compactification.boundaryRefinementProperty f
        (ObjectProperty.homMk (X := c') (Y := c) ⟨h, hj, hS⟩) ∧
      ∀ (h' : c'.obj.Z ⟶ c.obj.Z),
        h' ≫ c.obj.g = c'.obj.g → c'.obj.i ≫ h' = c.obj.i → h' = h := by
  sorry

end AlgebraicGeometry
