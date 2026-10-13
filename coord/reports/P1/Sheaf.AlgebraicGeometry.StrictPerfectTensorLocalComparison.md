## What changed

Changed `lean/Sheaf/AlgebraicGeometry/StrictPerfectTensorLocalComparison.lean`:
`AlgebraicGeometry.strictPerfect_tensor_localComparison` now composes an open-restriction
comparison with a proved local tensor invariance argument. Its signature and docstring are
unchanged. Two private helpers are proved: `strictPerfect_isKFlat_local` (finite-free
retracts and the bounded-flat theorem) and `local_kFlat_tensor_invariance` (mapping cones,
signed tensor symmetry, and two ordinary localization functors). The existing hypothesis
on B is retained; it is redundant for this fixed-factor proof, so the unused-variable
linter is disabled only for the original theorem.

Added proof import `Sheaf.AlgebraicGeometry.LocalizedOpenKFlatTensorRestriction`, together
with proof imports for flatness, tensor cones, total symmetry, and the cone criterion.
Added the new restriction module and its node, and updated the original node's proof,
proof dependencies, and proof origin. No definitions or existing statement interfaces changed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.strictPerfect_tensor_localComparison`
(node `lem-sc-strict-perfect-tensor-local-comparison`). No sorry remains in the item.
Both private helpers have complete proofs.

Added one hole: `AlgebraicGeometry.localizedOpen_kFlat_tensor_restriction`
(node `lem-sc-localized-open-kflat-tensor-restriction`) in the new module
`Sheaf.AlgebraicGeometry.LocalizedOpenKFlatTensorRestriction`.

This is a decomposition: one upper hole closed and one lower hole added, net zero holes.
The remaining statement is only the restriction step, with no local strictly perfect
models, prescribed input isomorphisms, or local tensor invariance argument.

## No longer needed

No original imports were removed: the two public imports support the unchanged signature.

The proof no longer needs `lem-pc-kflat-derived-tensor-comparison` or module
`Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison`, including its natural bifunctor
comparison and derived monoidal structure. It also no longer needs
`lem-pc-bounded-above-flat-kflat` or module
`Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`: the strictly perfect localized
complex is handled directly by the proved categorical bounded-flat theorem.

`lem-pc-open-restriction-kflat-model` and `lem-pc-open-restriction-total-tensor` remain in
the new restriction node's plan. Their modules are not imported by the original item.
No part of the unit's realized statement or steps is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned scheme-level restriction declarations end in modules on `U.toScheme`;
the target's local models instead lie in modules on the localized site over U.
Their signatures do not directly supply the required local-carrier comparison.
The new restriction node isolates precisely this remaining transport.

The full derived monoidal comparison is unnecessary: tensor cones show that each
fixed K-flat factor gives a functor through Q. Those two lifted functors transport
the given input isomorphisms directly. No flat-resolution data is chosen.

Edge cases checked in the mathematical argument: empty U, rank-zero free sheaves,
zero complexes, and arbitrary unbounded global complexes. Finite-free retracts are
flat even when their rank is zero; bounded-flat K-flatness and localization handle
these cases uniformly. The remaining restriction lemma includes the empty-open case
in its complete natural-language proof.

The local literature snapshot and unit Markdown file are absent; the unit JSON was
read. Primary sources read online: https://stacks.math.columbia.edu/tag/06YC,
https://stacks.math.columbia.edu/tag/06YH, and https://stacks.math.columbia.edu/tag/08DX.
LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle, and source
searches were completed.

## New nodes

`lem-sc-localized-open-kflat-tensor-restriction`, in
`dag/nodes/sec-picard-framework/lem-sc-localized-open-kflat-tensor-restriction.json`:
exact open restriction preserves K-flatness of the two global complexes and compares
their total tensor with the total tensor of their termwise restrictions on the
localized carrier. Source: Stacks 06YC, 01CD and 08DX. Searches found the existing
scheme-carrier components but no theorem on the displayed localized carrier. The
statement is a strict part of the original argument and has a full proof in words.
No change record is needed: existing statements, definitions and public imports stay
unchanged.

## Second reading by P1

1. Compared both delivered modules against the repository versions. The existing target signature and all existing declaration signatures are byte-for-byte unchanged; the new module adds only the split-off restriction theorem.
2. Compiled both modules with `lcompile.py`; the item compiles successfully (the local compile takes about 69 seconds), and the only remaining `sorry` is the named split theorem `AlgebraicGeometry.localizedOpen_kFlat_tensor_restriction`. No forbidden axioms, unsafe declarations, or hollow definitions were found.
3. Checked the split-off statement against the restriction argument and edge cases (empty opens, zero complexes, and rank-zero terms). It is a strict, true reduction and has its own node and complete proof sketch; no duplicate library theorem was found.
4. The proof follows the shortest available route for the target: strict perfect terms are shown K-flat directly, and the tensor comparison is handled by the localized restriction lemma. The original K-flat derived-comparison imports are no longer used and are listed above; the unit route is retained.
5. Checked the DAG node proof, dependencies, origin, and realized unit route against the Lean proof. They agree, with the remaining restriction theorem recorded as a split node.

Changed only the report by adding this second-reading record. No statement or definition was changed during review.
