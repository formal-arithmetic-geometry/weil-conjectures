/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.FiberDegreeBound

/-!
# Finite fibre degrees under base change

Source: Stacks Project, Morphisms, proof of Tag 03J5 and Tag 03J7
(blueprint: lem-weil-pbc-fibre-degree-base-change).

## Main statements

* `AlgebraicGeometry.Scheme.Hom.finite_fiber_degree_pullback`: a finite fibre remains finite
  with the same degree after base change.
* `AlgebraicGeometry.Scheme.Hom.boundsFiberDegrees_pullback_snd`: the same bound works after
  base change.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite fibre remains finite with the same degree after arbitrary base change.
Source: Stacks Project, Morphisms, proof of Tag 03J5
(blueprint: lem-weil-pbc-fibre-degree-base-change).

Proof, following the node's steps:
1. By `lem-weil-pbc-fibre-of-base-change`, the new fibre is the base change of the old one
   along the residue-field map induced by `g` at `t`.
2. By `lem-weil-pbc-finite-over-field-affine-finite-dim`, the old finite fibre is `Spec B`
   over its residue field, where `B` is its finite-dimensional ring of global sections.
3. Replace the old fibre by `Spec B` in the pullback using the universal property
   (`def-pc-fibre-product`); the isomorphism respects the structure morphisms.
4. By `lem-weil-pbc-fibre-product-affine-spectra`, the new fibre is the spectrum of the
   tensor product of `B` with the new residue field, over that new field.
5. A basis of `B` extends to a basis of this tensor product
   (`def-weil-vector-space-scalar-extension`); its dimension is unchanged and it is finite
   as a module (`def-weil-finitely-generated-module`).
6. The spectrum map is finite by `lem-weil-pbc-spec-finite-ring-map-finite`. Transport across
   the isomorphism using `lem-weil-pbc-isomorphism-finite` and
   `lem-weil-pbc-finite-composition` to obtain finiteness of the new fibre.
7. By `lem-weil-pbc-spec-map-global-sections`, the induced isomorphism on global sections
   respects the new field action. Thus its dimension is the tensor-product dimension,
   which is the old degree (`def-weil-pbc-fibre-degree-bound`). -/
lemma finite_fiber_degree_pullback {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (t : T) (hf : IsFinite (f.fiberToSpecResidueField (g t))) :
    IsFinite ((pullback.snd f g).fiberToSpecResidueField t) ∧
      ((pullback.snd f g).fiberToSpecResidueField t).finrankΓ =
        (f.fiberToSpecResidueField (g t)).finrankΓ := by
  sorry

/-- A bound on all finite fibre degrees is preserved by arbitrary base change.
Source: Stacks Project, Morphisms, Tag 03J7
(blueprint: lem-weil-pbc-fibre-degree-base-change).

Proof (step 8 of the node): for each `t`, apply steps 1--7, recorded in
`finite_fiber_degree_pullback`, to the finite fibre at `g t`. Its degree is at most `n`
by `hf`, and the new fibre is finite of that same degree. This gives both clauses of
`BoundsFiberDegrees` at every `t` (`def-weil-pbc-fibre-degree-bound`). -/
lemma boundsFiberDegrees_pullback_snd {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (n : ℕ) (hf : BoundsFiberDegrees f n) : BoundsFiberDegrees (pullback.snd f g) n := by
  sorry

end AlgebraicGeometry.Scheme.Hom
