## What changed

Proved `AlgebraicGeometry.ProEtale.condensedField_geometric_regular_coefficient` from the
existing proved `geometric_scalar_value`, unfolding only the private `coefficientValue`.
Its public signature, hypotheses, conclusion and visibility are unchanged.

Repaired `AlgebraicGeometry.ProEtale.condensedFieldPullbackRealization` in the unclaimed
module `Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix`: its new implementation
chooses the unique morphism equal to the existing explicit composite. The new fully proved
`existsUnique_condensedFieldPullbackRealization` supplies that unique specification, and
`condensedFieldPullbackRealization_eq` gives the exact equality to the original construction.
The existing IsIso and IsMonHom instance proofs and the item's private
`realization_conjugate` use the equation API. No arbitrary witness or postponed data is used.

The two delivered modules and all four unchanged downstream textual consumers compile
cleanly in import order. The freshly landed fifth consumer,
`Sheaf.Paper.IntegralMatrixPointwiseRank`, uses the changed definition only in private
`exists_small_evaluation`; that complete original proof also compiles unchanged. Its
whole-module compile currently stops at the unpublished compiled import
`Sheaf.Paper.IntegralMatrixCoefficientTransport`. The affected-proof scratch check omits
that unrelated import and later declarations; no consumer modification is delivered.
Axiom probes for the target theorem, the definition and its new API
show only `propext`, `Classical.choice` and `Quot.sound`. Updated the two existing DAG nodes
so their proof descriptions and recorded declarations match the implementation.

Change record: `coord/changes/A4-condensed-field-pullback-realization-evaluation.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.condensedField_geometric_regular_coefficient`
(node `lem-weil-pbc-condensed-field-geometric-regular-coefficient`).

Added 0 holes. No `sorry` remains in either delivered module. The new
`AlgebraicGeometry.ProEtale.existsUnique_condensedFieldPullbackRealization` and
`AlgebraicGeometry.ProEtale.condensedFieldPullbackRealization_eq` are fully proved and belong
to the existing definition node `def-weil-pbc-condensed-field-presentation-matrix`.
This closes the coefficient theorem outright, rather than decomposing it into new holes.

## No longer needed

None. All five existing imports are used: the two public imports supply the statement's
coefficient constructions, while the three proof imports supply the adjoint-test identity,
chart mate identity and generic conjugated-morphism square. No node or module is pruned.
The existing unit `sk-thm-properbasechange` has no realized statement or step at this helper;
its prescribed route is retained.

## Where the brief, the DAG or earlier work was wrong

The earlier report correctly isolated a kernel deterministic timeout at the final raw
coefficient conversion. That conversion becomes a short proof after repairing the
computation interface of the realization, without changing the mathematical coefficient.
Repeated direct unfolding, abstract evaluation equations, explicit terminal-object proof
arguments, expanded coefficient-sheaf types and an irreducibility-only repair all reproduced
the timeout. The unique specification with an exact equation prevents uncontrolled
reduction; the final theorem compiles in about nine seconds. The former DAG description of
the raw conversion as open is now replaced by its completed proof.

No false statement was found. Searches through the source library, Mathlib, Loogle and
LeanFinder found ordinary evaluation and naturality APIs; the needed specialized argument
was already proved by the private helpers in the item. No new node is needed.

## Second reading by A4

1. **Existing declarations and signatures — pass.** I compared both delivered Lean modules
with the shared repository versions. The target theorem's hypotheses, conclusion, and
visibility are unchanged byte-for-byte. The repaired pullback-realization definition has
the same type and the change record declares its implementation change; its equation API
preserves the old explicit morphism exactly. No target statement or definition was altered.

2. **Proofs and constructed data — pass.** Both delivered modules compile in import order
with `lcompile.py --all`, without errors or warnings. There are no `sorry`s, axioms,
`unsafe`, `opaque`, `extern`, or `implemented_by` declarations, and no `sorry` occurs in a
definition. The realization is selected from a fully proved unique-existence proposition
whose equality fixes it to the displayed composite; no arbitrary witness is used. Axiom
probes for the target, definition, and equation API contain only `propext`,
`Classical.choice`, and `Quot.sound`.

3. **Statements and edge cases — pass.** The coefficient theorem is the original geometric
pullback statement and is proved by the existing `geometric_scalar_value` reduction,
followed only by unfolding the private evaluation wrapper. The two added realization API
theorems are true by reflexivity and equality elimination, are strictly auxiliary, and do
not restate the target. Identity, zero, and identity-endomorphism cases retain the old
values; no empty-scheme case is introduced. Searches found no existing declaration with
the same specialized API.

4. **Route and pruning — pass.** The proof keeps the unit's prescribed geometric
pullback route through regular conjugation, realization naturality, scalar naturality,
and the existing evaluation-functor lemma. All five imports are used: the two public
imports support the statement and the three proof-only imports support the proof. No
unused import, proof dependency, or target-reachable module was pruned.

5. **DAG and Lean agreement — pass.** The target and definition nodes record the actual
proof steps, declarations, and proof dependencies, including the equation API used by
`realization_conjugate`. The change record lists the unclaimed matrix module and all
textual downstream users, with exact preservation of the old morphism and forced adaptation
limited to the item's private proof. The unit record and realized route remain unchanged.

This second reading changed only this report section. No Lean statement, proof, definition,
node statement, or import was changed during review.

Independent verification: compared all 21 existing declaration signatures programmatically
and found no byte changes. Recompiled both delivery modules and the four unchanged direct
consumers in a fresh scratch overlay. Reproduced the reported missing
`IntegralMatrixCoefficientTransport.olean` for the fifth consumer, then compiled its entire
unchanged affected private proof in that overlay. Separate axiom probes for the target,
definition, unique specification, equation, and both instances all show exactly the three
permitted axioms. Additional LeanFinder and Loogle searches found smooth-sheaf evaluation
results and generic `existsUnique_eq`, respectively; neither replaces the specialized
coefficient argument or its reduction barrier. The required dry run printed OK.
