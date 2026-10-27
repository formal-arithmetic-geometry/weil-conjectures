## What changed

In `Sheaf.Paper.CompletedPrimitiveCounitComparison`, filled the existence and
uniqueness proofs for ordinary inverse-image evaluation, without changing any
existing declaration signature or public import. The identity tensor bridge
`finiteTensorBridge` identifies its two definitionally equal scalar-extension
functors before transporting that equality through complexes, tensor, and
restriction. Functors preserve identities, so the bridge retains its identity map.

Existence applies the proved
`SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso` to the actual
sequence and finite coefficient ring maps and the existing direct-evaluation
identity. Inverting its canonical mate gives the desired comparison. Mathlib's
`unit_mateEquiv_symm` proves its required unit normalization by inverse
cancellation. The new import of
`Sheaf.CategoryTheory.SequenceModulePullbackEvaluation` is proof-only.

Uniqueness uses the proved private helper `unitNormalizedIso_unique`: under a
fixed adjunction, each inverse comparison has the same transpose, namely the
evaluated system unit followed by direct evaluation. Injectivity of the
adjunction hom-equivalence proves equality of the inverses. Inverting again and
natural-transformation extensionality give the required equality. The private
`unitNormalizedNatIso_unique` packages this componentwise argument, and
`inverseMate_exists` constructs the normalized mate in general categories.
All three private helpers are proved, with no new public declarations. The finite-adjunction unfolding
settings are scoped to the two evaluation proofs, and the chosen
`inverseEvaluation` and its system functors are kept folded downstream.

Strengthened the existing, unclaimed sequence-module evaluation theorem by
removing its unnecessary identity-on-sections premise. Its coextension mate is
pointwise bijective for every comparison isomorphism. Updated that node's
statement, proof, Lean signature and statement-change citer audit. No target
statement changes. The two pre-existing consumers still obtain exactly the same
conclusions; the explicit redundant argument in `AmbientPullbackTensorCoherence`
is removed as a forced proof adaptation. In `SemilinearOperationsExistence`, removed the three redundant `all_goals`
lines: the stronger theorem already closes their goal. The unchanged source
compiled with unused/unreachable-tactic warnings before this cleanup.

Updated the two existing evaluation nodes' proof records to match these
arguments. No new nodes are needed. The proof-context change record is
`coord/changes/K6-primitive-evaluation-proof-context.md`; the dependency repair
record is `coord/changes/K6-sequence-evaluation-arbitrary-comparison.md`.
The unit record has no
realized statement or proof steps; no unit route is bypassed. The existing
sequence-module evaluation theorem is used as a categorical tool, since the
original evaluation-calculus dependencies do not directly state invertibility
of this geometric mate.

## Proved and sorry left

Closed 2 of the module's original 4 holes:

- `WeilConjectures.PrimitiveCounit.inverseEvaluation_exists`
  (`lem-pur-completed-primitive-counit-evaluation-existence`).
- `WeilConjectures.PrimitiveCounit.inverseEvaluation_unique`
  (`lem-pur-completed-primitive-counit-evaluation-uniqueness`).

Added 0 holes and split off 0 statements. The following two pre-existing named
holes remain unchanged:

- `WeilConjectures.completedPrimitiveCounit_roos_exists`
  (`lem-pur-completed-primitive-counit-roos-realization-existence`).
- `WeilConjectures.completedPrimitiveCounit_comparisons_exists`
  (`lem-pur-completed-primitive-counit-comparisons-existence`).

This is a partial proof delivery, not a decomposition. Neither new proof uses
these two remaining existence theorems. The top-level comparison theorem's
existing complete assembly proof is retained.

## No longer needed

No imports removed and no complete modules withdrawn or pruned.

The uniqueness node no longer needs
`lem-coef-derived-system-evaluation-calculus` as a proof dependency: the
adjunction hom-bijection and category axioms suffice. Its statement dependencies
are retained.

The existence node no longer uses
`lem-coef-derived-system-evaluation-calculus` or
`lem-coef-semilinear-derived-sections` as proof dependencies. It instead uses
the existing sequence-module evaluation theorem and the sequence-site
construction underlying the current module's actual direct image. The public
imports of the original dependencies remain necessary for existing statements,
definitions, and other proofs. No whole-library pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The previous evaluation-existence plan proposed rebuilding a sectionwise
free-presentation argument. The library already proves the precise canonical
mate's invertibility through the sequence-module coextension argument.
The identity-on-sections premise of the sequence-module evaluation lemma was
stronger than necessary. On a coextension, its mate acts pointwise by the
comparison's section bijection conjugated by evaluation of functions on the
singleton `PLift (n ≤ n)`. Function spaces over an empty index type are also
singletons, so no boundary case requires the removed premise.
The uniqueness proof needs no geometric construction: inverse cancellation
turns the unit equations into equality of adjoint transposes.

The canonical tower Roos comparison was also inspected. Its public theorem
only states projection compatibility; it does not expose the precise
arbitrary-resolution normalization required here. No equality of derived maps
has been inferred from their finite evaluations, and the two larger existence
holes are reported honestly above.

## Forced adaptations

`Sheaf.Paper.AmbientPullbackTensorCoherence` is held by Y9. Its original source
was compiled against the strengthened dependency and failed at line 410:

```text
Function expected at sequenceModulePullbackEvaluation_isIso ...
but this term has type IsIso ((mateEquiv ...).symm ...).natTrans.
Expected a function because this term is being applied to the argument
(by intros; unfold sequencePushEvaluation; rfl).
```

The result is recorded in compile result `039a9bb3b7f1439ed5cecd82`:
the dependency compiled in 15.9 seconds; the unchanged consumer produced the
error above. Remove only the final identity-on-sections proof argument at
original lines 417–420. The existing comparison isomorphism is now the final
argument. Every declaration signature, visibility, import and other proof line
is unchanged. This adaptation is forced by removing the dependency's redundant
premise; it obtains the same mate invertibility and comparison as before.
The independent reader should repeat the original-fails/adapted-passes check.

The unchanged `Sheaf.Paper.SemilinearOperationsExistence` consumer also compiled
in the same set (15.9 seconds), with warnings that its trailing `all_goals`
tactics had no goals and were unreachable. This module is unclaimed. The only
cleanup removes original lines 178–180; its theorem conclusions and all other
lines remain unchanged. The stronger dependency already proves the goal.

The complete set compiled as result `201926c76ef53f94595da930`; the final profiling
run of the assigned module, `bfd8bc39851f3c1a9509ba8a`, compiled in 50.5 seconds.
All profiling options and diagnostic commands have been removed for delivery.

## Forced adaptations

### Sheaf.Paper.AmbientPullbackTensorCoherence
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
