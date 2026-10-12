## What changed

Proved `Module.prime_mem_localized_iff` in
`Sheaf.RingTheory.AffineFiniteProjectivePrimeMembership`, with its signature and visibility
unchanged. Added proof-only imports `Mathlib.RingTheory.Finiteness.Projective` and
`Mathlib.RingTheory.Localization.Module`. Mathlib supplies a split finite-free presentation;
the localized inclusion transfers membership to the existing free-module criterion, and the
original projection transfers it back. The converse is induction on ideal-module products.
Updated the existing node's proof to describe the maps and Lean lemmas actually used.
The unit's route and all proof dependencies stay intact.

Local single-file compilation passes without warnings. The import-cycle check passes.
The cited local Stacks TeX is absent on this machine; checked the direct-summand argument in
[Stacks Tag 00NX](https://stacks.math.columbia.edu/tag/00NX) and
[Tag 05CF](https://stacks.math.columbia.edu/tag/05CF) on the official site.

## Proved and sorry left

Closed the one original hole: `Module.prime_mem_localized_iff`
(node `lem-sc-affine-finite-projective-prime-membership`). No holes were added or split off.
No `sorry` remains in the delivered module.

The proof uses the existing open theorem `Module.free_prime_mem_localized_iff`
(node `lem-sc-free-prime-membership`, module `Sheaf.RingTheory.FreePrimeMembership`).
Thus this closes the assigned declaration from its planned dependency; it does not claim
that the transitive proof has only the three accepted axioms.

## No longer needed

None: every original import and every planned proof dependency is retained and used.
No nodes or modules are pruned. The localized projection and its splitting identity are
unnecessary constructions, so only the inclusion is localized. A trial explicit import of
`Mathlib.RingTheory.Ideal.Operations` was removed as its lemmas are already available.

## Where the brief, the DAG or earlier work was wrong

No statement or interface faults found. The DAG's localized projection is valid but
unnecessary: after the free criterion, the original projection suffices. The proof handles
zero modules and zero-length free presentations without special cases; primality is used
by the existing free-module criterion. No forced adaptations or new nodes.

## Second reading by Q3

1. **Visible changes and statements.** Compared the delivered module and node with the repository versions. The theorem signature is byte-for-byte unchanged; only the proof, proof-only imports, and DAG proof text changed. No definitions or target statements changed.
2. **Compilation and axioms.** Compiled the module successfully with `lcompile.py`; there are no `sorry`s in the delivered module and no forbidden declarations. The theorem's transitive `sorryAx` comes only from the existing `Module.free_prime_mem_localized_iff` dependency, as documented by the worker.
3. **Statement and proof validity.** Checked the direct-summand construction from `Module.Finite.exists_comp_eq_id_of_projective`, the localized map and scalar extension, both ideal-submodule inclusions, and the converse `Submodule.smul_induction_on`. The edge cases (including zero and free modules) are covered without extra hypotheses. No new statement or node was added.
4. **Pruning and imports.** The two added Mathlib imports are proof-only (`Mathlib.RingTheory.Finiteness.Projective` and `Mathlib.RingTheory.Localization.Module`) and are needed by the proof. Existing public imports remain needed for the theorem's interface. No proof dependency or unit route was removed; the unit's localized direct-summand route is retained.
5. **DAG agreement.** The node proof text now matches the Lean route and its proof dependencies remain the planned declarations. The unit route and statement are unchanged.

I changed only the report by adding this second-reading record; the delivered proof and DAG proof metadata require no repair.
