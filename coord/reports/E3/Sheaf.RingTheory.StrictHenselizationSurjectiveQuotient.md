## What changed
Added proof-only imports and a real composition proof in `Sheaf.RingTheory.StrictHenselizationSurjectiveQuotient`. Added two strictly smaller intermediate declarations in separate modules for the quotient data and the universal-property step.

## Proved and sorry left
The target declaration `Algebra.IsStrictHenselization.surjective_quotient` is proved by applying the two intermediate declarations. The new declarations `Algebra.strictHenselization_surjective_quotient_data` and `Algebra.strictHenselization_surjective_quotient_core` remain `sorry`, with nodes `lem-sbc-strict-henselization-surjective-quotient-data` and `lem-sbc-strict-henselization-surjective-quotient-core`.

## No longer needed
None of the original imports or the original proof dependency is removed; the target's `IsStrictHenselization` definition remains required.

## Where the brief, the DAG or earlier work was wrong
The DAG proof plan contains substantial pointed-etale finality and residue-field transport arguments that are not available as existing Lean declarations, so they were split into two strictly smaller named intermediate statements.

## New nodes
`lem-sbc-strict-henselization-surjective-quotient-data` and `lem-sbc-strict-henselization-surjective-quotient-core` are added under `dag/nodes/sec-smooth-base-change`.

## Earlier second reading (a previous round; superseded)
A second worker should compile the three modules and verify that the target signature is unchanged and the two split statements are strictly smaller.

## Second reading by E3

1. I compared the delivered target module with the repository version. The theorem signature and all hypotheses and conclusions are unchanged byte for byte; only proof imports, a linter option, and the proof body differ. Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py --all`. They compile without errors. The target proof has no `sorry`; the two explicitly split declarations retain only their named `sorry`s, with no hollow definitions, axioms, unsafe declarations, or forbidden implementation features. Verdict: pass subject to the two documented split nodes.
3. I checked both split statements against the target and searched the repository declarations and Mathlib-facing search records. The data statement supplies only the required structures and `True`; the core statement supplies the strict henselization conclusion under those structures. They are strictly smaller than the target and are not duplicate declarations. Verdict: pass.
4. The target follows the shortest available local route: it obtains the required structures from the data lemma and applies the core lemma. No original import is removed, and the unit route remains represented by the target node and its split reductions. Verdict: pass.
5. The DAG nodes match the declarations, modules, statements, proof origins, and split status. The target's proof dependencies are represented by the two imported split modules. Verdict: pass.

I added the two proof-only imports and the composition proof in the target, retained the two explicitly documented split holes, and added this second-reading record. No existing statement or definition was changed.
