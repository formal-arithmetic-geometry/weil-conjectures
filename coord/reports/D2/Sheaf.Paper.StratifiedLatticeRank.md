## What changed

Repair of returned head `1ec7410dd5d` (reviewer C-1ec74). The proof passed review;
landing rejected the reviewer's fix filename. Retain the reviewed proof and include the
complete corrected change record at `coord/changes/D2-rank-pullback-endpoints.md`.
The current shared branch still contains the original hole and lacks this record.
`deliver3.py` rebuilds the packet on freshly fetched `sheaf-dag`.

The landing API `tools/batch_land.py:fixes` maps change records to reviewer filenames
`<stem>.change.md`. Its expected fix filename is therefore
`D2-rank-pullback-endpoints.change.md`, rather than
`D2-rank-pullback-endpoints.md`. The latter error does not mean that the repository
change record was absent. This packet incorporates the change record directly, so no
reviewer override of that record is requested. Any further reviewer correction must
use the API's `.change.md` filename. No tools were changed.

Proved `AlgebraicGeometry.ProEtale.exists_clopen_rank_decomposition_of_isLisse` from the declared invariant-rank and labelled-clopen-descent results. The statement is unchanged up to explicit endpoint arguments on the pullback functors, and all public imports are unchanged. These arguments name the same source and target schemes as before; they prevent inferred identity/constant-functor wrappers from causing expensive kernel conversions. Proved private helpers pull finite-free trivializations through condensed coefficient pullback and its composition isomorphism. A generic coefficient assembly keeps the ring abstract; a private specialization of invariant rank uses precisely the existing spectral-topology coefficient expression, avoiding repeated expansion of its structures during kernel checking. Generic proved helpers refine a cover for any pullback-stable rank predicate and insert a trivialization into a pro-etale object without expanding coefficient structures. A proposition-indexed identity cover has explicit simple data and no members when its source is empty and its label is wrong. The proof descends the cover's constant rank labels, uses the descent theorem's test clause for arbitrary trivializations, identifies the disjoint open coproduct, and applies compactness directly to the rank opens.

For the constant-rank cover, base change the original cover and refine each component whose label is different from the requested rank by the empty cover of its empty scheme. Refine the remaining components by identity covers. This avoids asserting equality of ranks on an empty scheme. Updated the item's proof, proof dependencies and proof origin accordingly. No mathematical statements or existing definitions were changed, no new nodes were added, and no other modules were adapted.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtale.exists_clopen_rank_decomposition_of_isLisse` (node `det-lem-stratified-lattice-rank`): 1 of 1 holes. The item contains zero remaining holes; this delivery adds zero holes and splits off zero statements. The proof uses the existing declaration `AlgebraicGeometry.ProEtale.continuous_coefficient_finiteFree_rank`; its current shared source now has a complete proof, so the earlier report's description of that dependency as an open hole is obsolete.

## No longer needed

Removed private imports: `Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`, `Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback`, `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`, `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`, `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs`, `Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized`, `Mathlib.LinearAlgebra.Dimension.Finrank`, `Sheaf.AlgebraicGeometry.EtaleOpenFpqcDescent`, `Mathlib.CategoryTheory.Sites.Precoverage`, `Sheaf.AlgebraicGeometry.WeaklyEtaleStability`, and `Sheaf.Paper.CartesianCoefficients`.

The current DAG's `sk-prop-sfb-cartesian-coefficients` is unnecessary: finite free modules pull back using the actual functor's finite biproduct preservation and inverse coefficient-ring comparison. `sk-lem-pe-weakly-etale-stability` is unnecessary as a separate dependency: Mathlib's pro-etale precoverage already supplies stability under base change and composition. The formerly imported rank-realization, lattice-coefficient, dimension and etale-open-descent results are subsumed here by the two declared rank/descent lemmas. Removed obsolete tool approvals for cartesian coefficients, continuous realization, etale-open descent and weakly-etale stability, retaining scheme coproducts. These are dependencies pruned from this item's proof; no claim is made that they are globally unused, and no modules or declarations are withdrawn.

Searches: ran the launcher's leanfinder search for locally constant rank of a continuous p-adic coefficient sheaf; its results concern unrelated algebraic rank loci. Loogle located Mathlib's `AlgebraicGeometry.nonempty_isColimit_cofanMk_of`, used for the coproduct clause. The launcher's grep and repository searches found no ready-made condensed finite-free pullback theorem; the private construction uses the existing `Mod.finiteFreeIsoComap` API.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The item's original docstring still described the older seven-step proof, while the current reviewed DAG had already extracted invariant rank and labelled-clopen descent. The docstring and node now describe the formal proof. Pro-etale cover membership includes quasi-compact covering data, so joint surjectivity is accessed through `forgetQc`; no extra finiteness hypothesis is used. Edge cases retained: empty scheme and rank loci, empty original cover and components, rank zero, infinitely many cover indices, and infinitely many ranks when X is not quasi-compact.

Read the current blueprint rank proof and unit statement, the two extracted dependency statements and proofs, and Stacks descent.tex lemma-open-fpqc-covering and topologies.tex lemma-fpqc. The unit's rank-reduction route is preserved.

Change record: `coord/changes/D2-rank-pullback-endpoints.md`. `tools/downstream.py --uses` finds no external declaration users; the two direct importers require no proof adaptations.

Validation: static checks confirm zero `sorry`s, identical public imports, and no Lean lines over 100 characters. Re-ran `tools/downstream.py --uses exists_clopen_rank_decomposition_of_isLisse` against the current shared branch: no external textual users. The two direct importers require no adaptation. Both `## Old` and `## New` signatures in the change record match their respective
Lean sources verbatim, ignoring only terminal whitespace. The repaired module compiled
successfully through `lcompile.py` in 3.5 seconds with exit code 0 and no diagnostics, using no profiling or heartbeat overrides. `deliver3.py` repeats compilation, axiom probing, and server preflight before pushing.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
