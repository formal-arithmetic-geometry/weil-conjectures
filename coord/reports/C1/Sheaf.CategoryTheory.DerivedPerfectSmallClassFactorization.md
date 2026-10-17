## What changed

Marked `CategoryTheory.derived_factor_through_small_subcoproduct` as
`STATEMENT-DISPUTED`: its finite-support conclusion is false for an arbitrary
regular cardinal. The signature and existing hole are preserved. No target,
definition, consumer signature or visibility changes.

The sandbox also preserves complete scratch proofs of the corrected cardinal
support theorem and of a concrete derived-category counterexample. The corrected
result factors through a subcoproduct of cardinality less than α. Its proof uses
Mathlib's α-filtered poset `HasCardinalLT.Set I α`, constructs its coproduct
colimit cocone, and applies `IsCardinalPresentable.exists_hom_of_isColimit`.
Changing the false interface breaks the sole consumer's finite-biproduct proof;
preflight prohibits reopening that previously proved declaration. No unsupported
PG2 lemma is introduced to bypass that prohibition.

## Proved and sorry left

Zero of the original one holes is proved: the original statement is false.
`CategoryTheory.derived_factor_through_small_subcoproduct`, node
`new-sfb-derived-perfect-small-class-factorization`, remains the sole hole.
No holes are added and no split statements are delivered.

The scratch theorems `CategoryTheory.derived_factor_through_small_subcoproduct`
(with corrected signature) and `Diagnostic.finite_support_counterexample`
compile, and their axiom checks list only `propext`, `Classical.choice`, and
`Quot.sound`. The counterexample proves that a countable free object in degree
zero of D(k) is ℵ₁-presentable but its coproduct isomorphism does not factor
through any finite subcoproduct. The ℵ₀ specialization of the existing consumer
proof also compiles, showing exactly where finite support is legitimate.

## No longer needed

No imports or nodes are removed in this diagnostic delivery. The proposed repair
uses the cardinal-small subset poset in place of finite subsets, but its consumer
needs a separate perfectness argument; no finite-biproduct proof is claimed for
an infinite subcoproduct.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the node asserts that α-presentability forces finite support.
The poset of finite subsets is filtered, but it is not ℵ₁-filtered: countably
many singleton subsets have no finite upper bound. A morphism from the countable
free object of D(k) can have countably infinite support. Projecting onto a
summand outside a proposed finite image would make the identity of a nonzero
summand zero. This obstruction and the presentability hypothesis were both
verified in Lean using only the permitted axioms.

The sole consumer `DerivedPerfectSmallClassProperties` uses finite support to
apply `derived_finite_coproduct_surjective`. Replacing that support by the correct
cardinal bound invalidates its PG2 proof. Krause §§6.2–6.3 and Proposition 6.8.1
separate perfectness from small support. The upstream
`DerivedPerfectSmallClassCoreAlpha` identifies triangulated compactness with
ordinary categorical presentability and needs review with this consumer.

The delivery tool also repeatedly rejects its own temporary worktree as dirty:
it modifies `tools/stage3_gate.py` and `tools/stage3_delivery.py` after making the
delivery commit, then preflight reports uncommitted changes. This worker did not
edit any project tool or work around the gate. All proof and counterexample
artifacts remain in the sandbox for a later interface repair.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
