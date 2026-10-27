## What changed

Filled `Module.exists_basis_mem_submodule_of_semilocal` in
`Sheaf.RingTheory.SemilocalSubmoduleBasis` from its three declared proof dependencies.
For each maximal ideal, the given principal cover supplies a local trivialization
and the residue dimension. The Jacobson hypothesis factors the base ring map
through its residue field. Restricting the canonical quotient maps to `N` gives
the semilinear maps required by simultaneous residue bases; their images span by
span induction using the original generation hypothesis. The resulting tuple is
a global basis by the maximal-residue-bases criterion and the inverse of its
bijective coordinate map. All vectors belong to `N` by construction.

The statement, public imports, and existing documentation are unchanged.
Only the item module is edited; there are no new declarations or nodes.

Validation: `lcompile.py` compiled the final file cleanly in 3.6 seconds, with
no errors or warnings. All three proof imports pass `import_direction.py may`.
A textual check confirms that the theorem signature and docstrings are unchanged,
there are no `sorry` tokens, and every Lean line is at most 100 characters.

## Proved and sorry left

Closed the one original hole in
`Module.exists_basis_mem_submodule_of_semilocal`
(node `lem-a1-semilocal-submodule-basis`). No holes remain in the item, and no
holes are added or split off. The proof uses the already stated declarations
`Module.local_trivialization_residue_rank`,
`IsLocalRing.exists_simultaneous_residue_bases`, and
`Module.bijective_linearCombination_of_maximal_residue_bases`.
Their pre-existing holes belong to their own items.

## No longer needed

Removed the direct proof imports
`Mathlib.RingTheory.Localization.AtPrime.Basic`,
`Mathlib.LinearAlgebra.Dimension.Finrank`,
`Mathlib.RingTheory.OrzechProperty`,
`Mathlib.RingTheory.LocalProperties.Exactness`, and
`WeilConjectures.Mathlib.GroupTheory.CosetCover`.
The three declared proof dependencies encapsulate the local rank, avoidance,
Nakayama, and localization arguments. All three dependency nodes are used; no
DAG dependency or unit step is pruned. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

None. The proof follows all four steps of the current node without a signature
or definition repair. The rank bound `hr` is unnecessary for this argument;
the signature is preserved. The empty maximal spectrum (the zero ring case)
is covered by the same three dependency statements without extra assumptions.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
