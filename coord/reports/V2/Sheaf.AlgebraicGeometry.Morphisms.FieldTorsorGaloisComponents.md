## What changed

Replaced the whole proof of
`AlgebraicGeometry.Scheme.field_torsor_galois_components` with a complete Lean reduction.
The original statement, universes, visibility, and public imports are unchanged.

The proof constructs the finite field decomposition of the coordinate algebra with
`Algebra.Etale.iff_exists_algEquiv_prod`, constructs the scheme isomorphism from
`isoSpec` and `sigmaSpec`, proves its compatibility with the actual structure map using
algebra-map compatibility and the Gamma-Spec triangle identity, and reindexes the
finite family by `Fin r`. Each component inclusion is an open immersion over K.
The component theorem below gives a Galois group isomorphic to a subgroup of G;
`IsGalois.card_aut_eq_finrank`, `Nat.card_congr`, and Lagrange prove degree divisibility.

Added the new module
`Sheaf.AlgebraicGeometry.Morphisms.FieldTorsorComponentGaloisGroup` for the remaining
local component calculation. Its theorem applies to a specified open immersion
`Spec E -> T.P` over K, and asserts Galoisness and a subgroup description of `Aut_K(E)`.
It constructs no family of fields and no scheme decomposition, and asserts no degree
bound. It is strictly the Galois-action step of the argument, not a restatement of
the original existential decomposition theorem.

Added proof imports of `Mathlib.RingTheory.Etale.Field`,
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`, and the new component module.
Updated both DAG records to match the implementation and remaining proof plan.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.field_torsor_galois_components`
(node `lem-sbc-field-torsor-galois-components`). No `sorry` remains in the item's module.

Added exactly one hole:
`AlgebraicGeometry.Scheme.field_torsor_component_galois_group`
(node `lem-sbc-field-torsor-component-galois-group`), in its own module, with a source and
complete proof in words. Its whole proof is `:= by sorry`.

This is a decomposition: one upper hole closed, one strictly smaller hole added,
net zero holes removed. The affine decomposition, structural-map compatibility,
finite reindexing, and degree-divisibility assembly are proved without additional holes.
There are no changed definitions, no new axioms, and no forced adaptations.

Local compilation of both modules succeeds without warnings. The item's proof also
compiles without any file-level option changes. The delivery dry run checks both
modules again with the project's declaration and axiom probes.

## No longer needed

Removed the direct proof import of
`Sheaf.FieldTheory.EtaleFieldGaloisClassification` from the item. That module and node
`lem-exc-etale-field-galois-classification` remain needed by the new component theorem,
which imports it and cites it in its proof plan. This moves the dependency to the step
that actually needs it; it does not prune that module from the target closure.

No other imports, nodes, or modules are pruned. No blueprint unit statement or realized
proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No defect in the original theorem statement was found. The original DAG's first step
had no named dependency for the affine decomposition; Mathlib's etale-algebra product
classification and the existing Gamma-algebra API close that step directly.

The `sigmaSpec` isomorphism instance uses the same universe for the index and rings.
Thus applying it immediately to `Fin r` fails at general universe u. The proof keeps the
original index `I : Type u` until after constructing the isomorphism, then uses the
categorical coproduct reindexing isomorphism. No library interface needs changing.

For the remaining component lemma, checked the trivial group, a split torsor, and
multiple Galois orbits. An open immersion from the spectrum of a field is nonempty
and selects a single component. In the geometric-point argument, right translations
reverse composition; taking inverses gives the homomorphism into G. This convention is
made explicit in the new docstring and node. The entire torsor need not be connected.

Searches used LeanFinder, Loogle, Mathlib/library/DAG text searches and blueprint search.
LeanSearch was attempted but returned Internal Server Error. LeanFinder found
`Algebra.Etale.iff_exists_algEquiv_prod` and the field-action `IsGaloisGroup` API,
but no theorem taking a scheme torsor and its open field component. The blueprint search
for "torsor component" returned no matches. The nearby affine stabilizer descent nodes
require a pre-existing field action and do not provide this component interface.

Sources read: https://stacks.math.columbia.edu/tag/03SF and
https://stacks.math.columbia.edu/tag/03QR. The new component proof follows their
Galois-cover and finite-separable-field correspondence, with the commuting torsor-action
argument written explicitly. The original unit route is retained.

## New nodes

`lem-sbc-field-torsor-component-galois-group`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-field-torsor-component-galois-group.json`,
states the remaining Galois-group calculation for a specified field component. Its
module is `Sheaf.AlgebraicGeometry.Morphisms.FieldTorsorComponentGaloisGroup`; its source
is Stacks 03SF and 03QR; its proof dependency is
`lem-exc-etale-field-galois-classification`. It inherits the original chapter and unit.
There are no interface-change records because no existing interface changed.

## Second reading by V2

1. **Statements unchanged.** Compared the delivered item module with the repository version; the existing target declaration has identical parameters, instances, conclusion, and visibility. The new component declaration is a strictly smaller specified-component result and does not alter existing declarations. Verdict: pass.
2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py --all`; the target proof is complete and the only remaining `sorry` is the named component theorem. No forbidden declarations occur. The target depends only on the permitted kernel axioms plus `sorryAx` through that explicitly split theorem. Verdict: pass.
3. **New statement.** Checked the component theorem against trivial, split, and disconnected torsors. Its hypotheses identify a nonempty field component and its conclusion gives precisely Galoisness and an automorphism subgroup, with no decomposition or degree claim. The node, source, docstring, and Lean statement agree. Verdict: pass.
4. **Pruning and route.** The affine product decomposition, structural-map compatibility, finite reindexing, and component application follow the unit route. Removed the old direct classification import from the item; the new component module retains the dependency where it is used. Verdict: pass.
5. **DAG agreement.** Updated proof steps and dependencies match the Lean code, and the new node records the split theorem, module, source, proof plan, and unit/chapter. Verdict: pass.

No changes were needed during this second reading beyond this report section; the delivered proofs and DAG records were retained unchanged.
