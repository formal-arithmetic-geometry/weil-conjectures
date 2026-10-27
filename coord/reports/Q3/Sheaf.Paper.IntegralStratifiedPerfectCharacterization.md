## What changed

Prove `AlgebraicGeometry.Scheme.integralStratifiedPerfectDetailed` by combining
`WeilConjectures.purDetailedTransport_complete_iff`,
`AlgebraicGeometry.Scheme.integralDetailedFiniteReduction`, and the existing
`pbcUniformReductionCriterion`. The interval is normalized to `[min a b,b]` in
the reverse implication, so the ordered-interval clause also holds for zero complexes
and empty schemes. The characterization, closure theorem and all existing signatures
are preserved.

Factor the existing seven normalized coefficient constructors into
`Sheaf.Paper.IntegralCompletedCoefficientTransport`, publicly reexported by the item.
Factor the existing coefficient equivalence and completeness comparison prefix of
`CompletedCoefficientPresentationTransport` into
`IntegralCoefficientCompletenessTransport`, publicly reexported by its old module.
The remaining presentation-transport proofs import the same private equivalence
helpers from their new location. No public definition body changes. The ordinary
round-trip existence proof now constructs its identity restriction comparison directly.

`CompletedCoefficientCompletionRoosTransport` imports the independent constructors
instead of the characterization. Its existing theorem and hole are unchanged. Its
DAG reference now identifies the actual constructor-owning definition node. All DAG
citers continue to use exactly the same theorem signature. The change record
`coord/changes/Q3-integral-coefficient-comparison-factorization.md` records the complete
old blocks, new locations and the 2027-module consumer audit. Both adapted existing
modules were unclaimed; no forced adaptation of another group's item is made.

Validation: lcompile.py --all compiled all six delivered modules in import order
with no errors or warnings. A declaration-table comparison confirms that every moved
definition and instance retains exactly its original signature and body.

The finite-level proof explicitly constructs the quotient comparison using the existing
normalized derived restriction square, identifies derived extensions by uniqueness of
left adjoints, and compares homology, zero objects and constructible local models.
The completeness proof reuses the existing normalized completion Roos theorem and
completion reflector. It compares rotated distinguished triangles to identify the
input object with its completion; it does not claim uniqueness of a lift from product
projections. All new intermediate statements have complete proofs.

## Proved and sorry left

Closed the item's one existing hole:
`AlgebraicGeometry.Scheme.integralStratifiedPerfectDetailed`
(node `lem-weil-pbc-integral-stratified-perfect-characterization`).
The item has zero holes left. Added zero holes and split off zero unproved statements.
The two new comparison theorems, all moved coefficient constructors, and the moved
completeness theorem are proved.

The adapted dependency retains its one pre-existing hole, unchanged:
`WeilConjectures.completedCoefficientCompletionRoosTransport`
(node `lem-pur-completed-coefficient-completion-roos-transport`). This is an existing
stated proof dependency used by the completeness argument. It is not a new hole or a
newly split statement. The other five delivered Lean modules contain zero holes.

## No longer needed

Removed the proof imports `CompletedCoefficientCompletionRoosTransport`,
`SfDerivedCompleteLegacyComparison`, and `Mathlib.Data.Nat.Prime.Infinite` from
`CompletedCoefficientPresentationTransport`; these serve its extracted completeness
prefix and now occur in that prefix's independent module.

Replaced the public import of `IntegralStratifiedPerfectCharacterization` in the Roos
module by `IntegralCompletedCoefficientTransport`: only the unchanged coefficient
constructors are needed there. The original sole direct consumer of the Roos module
explicitly imports the characterization, so no downstream public declaration is lost.

At the characterization node, step 5 now directly uses the completeness and finite-level
comparison nodes and the uniform-reduction criterion. The former direct dependencies
on `lem-weil-pbc-integral-coefficient-presentation-comparison`,
`def-weil-derived-complete-integral-detailed`, `def-weil-derived-complete`,
`def-weil-finite-torsion-constructibility`, `def-weil-proetale-constructible-sheaf`,
`lem-weil-pbc-constant-completion-equivalence`,
`lem-weil-pbc-completed-koszul-reduction-roos-triangle`, and
`lem-weil-pbc-ringed-koszul-completion-reflector` are factored through the comparison
nodes or remain statement dependencies. None is claimed globally unnecessary: the
existing Roos transport and other consumers still require their mathematical content.
No entire module or unit-route node is withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

The original Lean import placement made the already-proved completeness comparison
unavailable to its parent without a cycle: the same module also contained the bounded
comparison proved from that parent. The DAG's independent coefficient-definition node
already separated these notions. Factoring the Lean modules implements that separation.
The Roos node cited the characterization for a constructor it did not need the theorem
to obtain; its reference-only correction retains all mathematical hypotheses and
conclusions, with a `statement_change` citer audit.

The fixed-coefficient constructibility comparison and the detailed small-coefficient
comparison use different encodings, so equality by notation would be insufficient.
The finite-level lemma proves the encoding comparison using sheafification naturality
and identity-on-sections module isomorphisms. Empty intervals, the zero complex,
the empty scheme and the first positive quotient level are all covered by the statements.

The latest blueprint unit files were read. Their refreshed classical proper-base-change
route does not replace this still-attached integral-category prerequisite. No blueprint
unit statement or realized step is bypassed. A dependency-closure audit found unrelated
pre-existing ring-differential cycles; no changed or new node has a path back to itself.

## New nodes

`lem-weil-pbc-integral-coefficient-completeness-transport` records the complete proof of
completeness invariance for an arbitrary input complex, without geometric finiteness or
bounded constructibility. It also owns the extracted independent equivalence declarations.

`lem-weil-pbc-integral-detailed-finite-reduction` records the complete proof comparing one
positive finite reduction, its constructibility and an arbitrary specified interval.
It imposes no completeness condition and is strictly a finite-level part of the argument.
Searches using LeanSearch, LeanFinder, Loogle and grep are recorded in the nodes; the
existing coefficient-presentation and constructibility interfaces are reused.

The new completeness node uses the existing normalized completion Roos theorem from
the smooth-purity unit as a tool: it is the exact comparison of the two completion
objects and units that the integral detailed argument needs. It is reused with its
unchanged signature; no new off-unit approval is added by this delivery.

The change record is `coord/changes/Q3-integral-coefficient-comparison-factorization.md`.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
