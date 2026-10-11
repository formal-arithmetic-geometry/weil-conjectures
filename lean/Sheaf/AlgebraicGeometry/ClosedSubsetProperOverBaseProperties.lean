/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Closed subsets proper over a base: structures, subsets, and images

Source: Stacks Project, Cohomology of Schemes, Lemmas 0CYL, 0CYN, and 0CYQ
(blueprint: lem-weil-pbc-closed-subset-proper-over-base-properties).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Closed subset properness is independent of the chosen closed subscheme structure,
passes to closed subsets, and is preserved by images under morphisms over the base.
Source: Stacks Project, Cohomology of Schemes, Lemmas 0CYL, 0CYN, and 0CYQ.
(blueprint: lem-weil-pbc-closed-subset-proper-over-base-properties)

Proof, following the six steps of the node:
1. The reduced induced closed subscheme is one structure on `Z`
   (lem-weil-pbc-reduced-induced-closed-subscheme). By the definition
   def-weil-pbc-closed-subset-proper-over-base, properness of every structure implies
   properness of the reduced one, and properness of the reduced one gives some structure.
2. Given two structures `Z'` and `Z''` with `Z'` proper over `S`, form their scheme-theoretic
   union `Z'''` (lem-weil-pbc-scheme-theoretic-union). All three have image `Z` in `X`;
   the closed immersions from `Z'` and `Z''` into the union are bijective, hence surjective
   (def-weil-surjective-morphism).
3. The union is locally of finite type over `S`, by closed immersion and composition
   permanence (lem-weil-pbc-proper-fp-permanence). The map from `Z'` to the union is
   universally closed (lem-weil-pbc-closed-immersion-integral-separated-uc) and surjective;
   separatedness descends from `Z'` by lem-weil-pbc-surjective-universally-closed-separated.
4. Properness of `Z'` implies universal closedness. Apply
   lem-weil-pbc-image-universally-closed to the surjection to the separated, locally
   finite type union to obtain properness, including quasi-compactness. Compose with
   the closed immersion from `Z''` (lem-weil-pbc-proper-fp-permanence) to prove its
   properness. Together with step 1 this proves both equivalences.
5. For `Y` closed in `Z`, pull it back to the reduced structure on `Z`, then give that
   preimage a closed subscheme structure (lem-weil-pbc-closed-subset-closed-subscheme).
   Compose closed immersions (lem-weil-pbc-closed-immersion-comp), whose image is `Y`.
   The composite to `S` is proper by lem-weil-pbc-proper-fp-permanence. Apply part (1).
6. For `Z` proper over `S`, apply lem-weil-pbc-scheme-theoretic-image-proper to the map
   from its reduced structure to the separated, locally finite type `X'` over `S`.
   The image subscheme is proper over `S` and has underlying closed set `g(Z)`.
   Apply part (1) for `f'` to identify this with closed subset properness.
-/
theorem closed_subset_proper_over_base_properties
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (Z : TopologicalSpace.Closeds X) :
    (IsClosedSubsetProperOver f Z ↔
        ∃ (Z' : Scheme.{u}) (i' : Z' ⟶ X) (_ : IsClosedImmersion i'),
          Set.range i'.base = (Z : Set X) ∧ IsProper (i' ≫ f)) ∧
    (IsClosedSubsetProperOver f Z ↔
      ∀ (Z' : Scheme.{u}) (i' : Z' ⟶ X) [IsClosedImmersion i'],
        Set.range i'.base = (Z : Set X) → IsProper (i' ≫ f)) ∧
    (∀ (Y : TopologicalSpace.Closeds X), Y ≤ Z →
      IsClosedSubsetProperOver f Z → IsClosedSubsetProperOver f Y) ∧
    (∀ {X' : Scheme.{u}} (g : X ⟶ X') (f' : X' ⟶ S)
      [LocallyOfFiniteType f'] [IsSeparated f'],
      g ≫ f' = f → IsClosedSubsetProperOver f Z →
      ∃ W : TopologicalSpace.Closeds X',
        (W : Set X') = g '' (Z : Set X) ∧ IsClosedSubsetProperOver f' W) := by
  sorry

end AlgebraicGeometry.Scheme
