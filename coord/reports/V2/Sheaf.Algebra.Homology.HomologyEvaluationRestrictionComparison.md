## What changed

In `Sheaf.Algebra.Homology.HomologyEvaluationRestrictionComparison`, replaced the
single sorry by a proof from one new comparison lemma. The public statement and
its docstring are unchanged. Added proof-only imports of
`Sheaf.Algebra.Homology.HomologyEvaluationRestrictionDiagrams` and
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`.

The proved private helpers construct the ambient cycle pairing using the Hom
differential formula, the tensor-Hom equivalence, and the kernel universal
property. They then use `IsHomologyEvaluation` to prove its homology equation:
evaluate at the identity slice, restrict the Hom cycle to any smaller slice,
and apply naturality and extensionality. No pointwise surjectivity of a sheaf
homology quotient is assumed.

The proved generic helper `transport_cycle_pairing` transports the pairing and
evaluation along six isomorphisms and five comparison squares. It checks both
pairing equations and the final square by functoriality, associativity, and
inverse cancellation. This categorical calculation is abstracted over the
categories and functor, avoiding expensive repeated unfolding of concrete
sheaf Hom types. All helper proofs are complete. Monoidal instances are introduced only by anonymous `let` inside private helper proofs.
No exported definition or interface is changed and neither compile nor
heartbeat limits were raised. The final application uses a declaration-scoped
elaboration setting only.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.homologyEvaluation_restriction_comparison`
(node `new-e3-homology-evaluation-restriction-comparison`). Its module has no
remaining sorry.

Added one hole, the whole proof of the new public theorem
`CategoryTheory.homologyEvaluation_restriction_diagrams`
(node `new-v2-homology-evaluation-restriction-diagrams`, module
`Sheaf.Algebra.Homology.HomologyEvaluationRestrictionDiagrams`). This is a
**decomposition**, with one hole closed and one added, net zero holes; it is
not a claim of a sorry-free proof of the target closure.

The remaining theorem has no evaluation morphism `e` and no
`IsHomologyEvaluation` assumption. It asserts the comparison isomorphisms and
five universal-property naturality squares only. In particular it neither
constructs the cycle pairing nor proves that evaluation of homology classes
agrees with that pairing. Those two substantive arguments are proved here.
This is the restriction-comparison subargument (steps 1 and 2) of the original
plan, rather than the original statement under another name.

Local compilation passed with no warnings. The final delivery dry run supplies
its own per-file compile and axiom/sorry probes. Edge cases of the new statement
were checked mathematically: for zero complexes, the unique zero-object
comparisons satisfy all squares; empty V or W uses the same restriction,
product, kernel, and cokernel universal properties; no nonempty or boundedness
hypothesis was introduced. The generic transport proof works in arbitrary
categories with no zero, exactness, or sheaf assumptions.

## No longer needed

No import from the original module was removed: its sole public import,
`Sheaf.Algebra.Homology.HomologyEvaluationDefinitions`, is required by the
unchanged statement.

The revised route no longer uses the abstract chain-isomorphism statements
`lem-sc-hom-complex-restrict-open`
(`Sheaf.Algebra.Homology.HomComplexRestrictOpen`) or
`lem-sc-hom-complex-restrict-scheme`
(`Sheaf.AlgebraicGeometry.HomComplexRestrictScheme`). These two planned proof
dependencies have been pruned. The new comparison lemma instead constructs a
projection-compatible chain isomorphism from the fixed limiting fans.
This is pruning of this proof's planned dependencies, not a claim that no
other target imports these modules.

The direct dependencies on `lem-sc-internal-hom-over-equiv` and
`lem-sc-derived-hom-mayer-vietoris` move to the new comparison node, rather than
being globally pruned. Only the latter node's already-proved restriction
exactness helpers are needed; its Mayer-Vietoris conclusion is not used.
The ambient argument imports the narrower `MonoidalClosed` module and needs
neither `MonoidalFree` nor `Mathlib.CategoryTheory.Monoidal.Closed.Braided`.
No roof, K-injectivity, finite-free model, or zero-differential model theorem is
used. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The two planned restriction lemmas state only `Nonempty` of an abstract chain
isomorphism. Their statements do not expose compatibility with the chosen
Hom-product projections, so they cannot directly justify the evaluation
identification in step 1. The new node records that missing stronger interface.
`lem-sc-derived-hom-mayer-vietoris` is used by the plan for exactness helpers
in its module, not for its final Mayer-Vietoris statement; the new node's proof
makes that distinction explicit.

The kernel-lift and tensor-Hom calculations were adapted from the already
proved private helpers in `HomologyEvaluationCycleExistence`; their private
visibility prevents importing them directly. The slice-naturality argument
follows the corresponding pattern in `HomologyEvaluationUniquenessExt`, but
proves a different equation and assumes no local-lift hypothesis: the ambient
kernel lift constructed in this module supplies the target cycle itself.

The first concrete transport proof exhausted elaboration heartbeats while
unpacking large sheaf comparison types. Profiling identified repeated
normalization of the restricted ring sheaf and Hom-complex types. The abstract
categorical helper fixes the issue without changing any library definition,
splitting a slow file, or raising a limit.

## New nodes

`new-v2-homology-evaluation-restriction-diagrams` is in
`dag/nodes/sec-picard-framework/` and states the remaining comparison subargument
in `lean/Sheaf/Algebra/Homology/HomologyEvaluationRestrictionDiagrams.lean`.
Its complete proof in words explains construction from products and natural
internal-Hom comparisons, exact cycle/homology transport, and each of the five
squares. Its source is Stacks Tags 0A8X and 08DL, with the omitted
universal-property details expanded from the parent plan. Searches of the
whole blueprint and the Lean library found no existing statement exposing
these five squares; the abstract restriction isomorphisms are insufficient.
LeanFinder, Loogle and Mathlib grep were run; LeanSearch returned Internal
Server Error and is recorded as unavailable. The parent node's `proof`,
`proof_deps` and `proof_origin` now match the implemented reduction.

No change record is needed: no existing statement, definition, public import,
or exported instance was changed; no other module was adapted.

## Second reading by V2

1. **Statements and interfaces.** I compared both delivered modules and the
repository versions byte for byte at every pre-existing declaration. The target
statement and all existing signatures are unchanged; the new theorem is a
strictly smaller restriction-diagram statement and has no evaluation hypothesis.
Verdict: pass.

2. **Proof and axioms.** I compiled both files with `lcompile.py`; compilation
is clean. The comparison theorem has no `sorry`, `axiom`, `unsafe`, `opaque`,
`extern`, or `implemented_by`. The only remaining `sorry` is the named new
diagram theorem, with its node and complete proof description. The helper
proofs use only ordinary categorical and sheaf extensionality arguments.
Verdict: pass.

3. **Truth and strength of split statement.** I checked zero complexes, empty
opens, and arbitrary categories in the transport helper. The split theorem
asserts exactly the five comparison squares needed by the parent proof and
does not restate the parent target or weaken it by adding assumptions.
Verdict: pass.

4. **Shortest route and pruning.** The proof uses the direct kernel lift and
the generic categorical transport helper. The old abstract restriction-chain
imports are absent from the delivered module and are recorded under
`## No longer needed`; the narrower monoidal-closed import is sufficient.
Verdict: pass.

5. **DAG and unit route.** The parent and split node `proof`, `proof_deps`,
`proof_origin`, Lean records, chapter, and unit agree with the implemented
proof. The unit's realized route is preserved, and the new node records its
source, searches, statement, and decomposition status.
Verdict: pass.

I changed only this report by adding this second-reading record; no Lean source,
statement, definition, or DAG metadata was changed during the review.
