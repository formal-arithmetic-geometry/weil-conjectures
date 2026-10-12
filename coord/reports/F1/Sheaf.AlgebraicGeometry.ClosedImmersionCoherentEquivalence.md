## What changed

Added two strict component theorems in new modules, one for the termwise formal-module
 equivalence and one for the completion comparison. The target theorem now combines these
 two components by conjunction. The new component proofs remain named public obligations.

## Proved and sorry left

`closedImmersion_coherentFormal_equivalence` is proved by applying the two component
 statements. The new declarations `closedImmersion_coherentFormal_equivalence_termwise`
and `closedImmersion_coherentFormal_equivalence_completion` retain one `sorry` each, with
nodes `lem-weil-pbc-closed-immersion-coherent-formal-equivalence-termwise` and
`lem-weil-pbc-closed-immersion-coherent-formal-equivalence-completion`.

## No longer needed

None of the original proof dependencies can be pruned: they are needed by the component
statements and remain in their imports.

## Where the brief, the DAG or earlier work was wrong

The original module grouped two long independent constructions into one unresolved theorem.
No mathematical statement was changed; the DAG was refined into the two strict conjuncts.

## New nodes

`lem-weil-pbc-closed-immersion-coherent-formal-equivalence-termwise` and
`lem-weil-pbc-closed-immersion-coherent-formal-equivalence-completion` are new split nodes.

## Earlier second reading (a previous round; superseded)

A second worker should verify that the conjunction proof applies exactly the two strict
component statements, that both statements match their declarations, and that the original
unit route is preserved through the existing dependency modules.

## Second reading by F1

1. Compared the delivered main module with the repository version. The existing declaration
signatures and definitions are unchanged byte for byte; only the two proof imports and the
target proof body differ. Verdict: pass.
2. Compiled all three delivered modules with the prescribed lcompile command. The only
remaining sorries are the two named split-off component theorems, with no forbidden
declarations or hollow definitions. Verdict: pass.
3. Checked both split-off statements against the target's two conjuncts and their DAG nodes.
They are true, strictly simpler component obligations, and each has a source, proof
description, and matching Lean declaration. Verdict: pass.
4. The formal equivalence target is proved by conjunction from exactly the termwise and
completion components. The existing unit route remains represented by the original
dependencies and the component nodes. Verdict: pass.
5. Checked node metadata and proof dependencies against the imports and proof. The target
node now records the two component uses; the component nodes record their declarations and
sources. Verdict: pass.

Changed only this report by adding the second-reading record required for delivery.
