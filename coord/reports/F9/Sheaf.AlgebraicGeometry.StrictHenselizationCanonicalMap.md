## What changed

Proved the two original theorems in
`Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`, preserving every existing
signature, definition body, visibility, and docstring. Added the plain proof import
`Sheaf.Paper.StrictHenselizationPointEvaluationPointed` and a proved private helper
`evaluation_eq_of_pointed`.

The proof follows the existing docstring and the functoriality node. Install the
geometric-point residue embeddings as algebra structures, apply
`AlgebraicGeometry.strictHenselizationResidue` twice, and apply
`AlgebraicGeometry.strictHenselizationFunctoriality` to the resulting uniquely
characterized residue identifications. The private helper uses limit
extensionality and `strictHenselizationPointEvaluation_pointed` to identify their
composites into Omega with the actual evaluation maps. The spectrum of the
functorial ring map satisfies both equations. Conversely, use `Spec.preimage` on
any competing map; its pointed equation makes the composite with evaluation
local, and `isLocalHom_of_comp` makes the ring map local. The existing
functoriality uniqueness clause then proves equality. Finally project the
structural equation from the uniquely chosen witness to prove the over lemma.

The module compiled cleanly through lcompile.py (6.3 seconds). The normal delivery
probe also checks the axioms. No target, definition, public import, statement, or
consumer changes. The route of `lem-weil-pbc-strict-henselization-functoriality`
and the unit `sk-thm-p1` remains unchanged, so no DAG file is changed.

## Proved and sorry left

Closed 2 original holes:

- `AlgebraicGeometry.Scheme.strictHenselizationMap_existsUnique`.
- `AlgebraicGeometry.Scheme.strictHenselizationMap_over`.

There are zero remaining `sorry`s in the item and zero holes added elsewhere.
There are zero split-offs. The private evaluation-comparison helper is proved.
`strictHenselizationMap` retains its original definition as the choice from the
uniquely characterized witness; no data is chosen from mere existence.

## No longer needed

None. Both original public imports are used: functoriality supplies the local
structures and unique ring map, and evaluation occurs in the unchanged statements.
The additional pointed-evaluation import is used by the private limit
extensionality argument. No declared dependency or module is bypassed or withdrawn;
no module is claimed to leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found. The docstrings cite
`lem-weil-pbc-strict-henselization-functoriality`, whose recorded Lean module is
`Sheaf.Paper.StrictHenselizationFunctoriality`; no DAG node has this item's own
module as its primary `lean.module`. This packaging module is nevertheless on the
targets' import closure, as reflected by its two holes in the sorry ledger.

The semantic LeanFinder search for a canonical unique pointed strict-local
morphism returned the general `SpecToEquivOfField` and residue-field API, not a
strict-henselization map. Local searches found the already proved functoriality,
pointed-evaluation, and spectrum API, which supply the intended argument. No new
mathematical statements or new nodes are necessary.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
