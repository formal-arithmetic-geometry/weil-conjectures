## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-diagonalizable-hom-family-rigidity.json`: statement, split; no Mathlib match for the full item. The original statement, prior searches, provenance, and imported metadata are retained. Added four proof steps and the searches actually run by Q18.
- `citations.json`: verbatim statement quotations for every citation of all four steps.
- `report.md`: this report. No new nodes and no new Mathlib leaves.

## Attachments

None for the item. Searching the project source under `lean/WeilConjectures/` by the exact blueprint id and by diagonalizable/diagonalisable terminology found no declaration of this item. `AlgebraicGeometry.Scheme.connectedSpace_iff_isIdempotentElem` already belongs to `lem-pc-scheme-connected-iff-idempotents`; its node records the declaration as closed, and its source at `WeilConjectures/Mathlib/AlgebraicGeometry/Scheme.lean:244` states exactly the criterion used here.

## Wanted literature

None. Read Milne, Algebraic Groups (2017), Theorem 12.36 on printed pp.243--244 and Remark 12.43 on p.245, directly from the supplied PDF. Read the connectedness/idempotent paragraph of Stacks Tag 0BUG, `varieties.tex`, label `lemma-proper-geometrically-reduced-global-sections`, proof of (2), lines 1961--1971. No SGA source used.

## Problems found and decisions

The item is correct as written, including its nonreduced clause. There was no existing sandbox node, report or logged search to continue. No statement dispute and no statement correction.

Milne gives two routes: finite torsion and density in Theorem 12.36, and the coordinate/idempotent route in Remark 12.43. The split follows the latter and explicitly supplies its coefficient argument. This choice is below the unit level: it proves the identical supporting rigidity input, without replacing any unit step. Its expanded argument is marked agent-written. The inherited blueprint ancestor is null (`blueprint_refs.py ancestor` printed None); its detailed `from.place` and `via` are preserved. Read the current `literature/blueprint/latest/` unit and its direct-images proof, rather than an older snapshot. This supporting item is not the unit's key theorem, so no unit realization fields are changed.

Mathlib searches were run only through the required msearch command and read. The first Loogle pattern was invalid because `Bialgebra.IsGrouplike` is not a name; the subsequent `IsGroupLikeElem, AddMonoidAlgebra` query corrected it. Read `Mathlib/RingTheory/Bialgebra/MonoidAlgebra.lean:232--253`: `AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one` requires `IsDomain R`. The second LeanFinder phrasing similarly returns independence results over a domain. These cannot be applied to the parameter ring, which may be nonreduced or reducible. The field-only existing leaf `lem-sfb-group-algebra-group-like-basis` has the same limitation. No match was claimed. All query texts, results and verdicts are retained in the item and searches.jsonl, including the invalid query.

## Not duplicates

No new nodes. Searched the whole DAG by group-like, idempotent, connectedness, Hopf morphism and affine correspondence terminology, and the whole imported blueprint using `blueprint_refs.py search` for diagonalizable, group-like, idempotents and rigidity. The usual proper/reduced rigidity lemma has different hypotheses and is not used. The group-algebra field leaf is insufficient over B. The existing connectedness criterion is reused, and the spectrum/tensor leaves supply the affine correspondence and product algebra. The coefficient comparison, finite-sum argument and evaluation at x0 are elementary steps with their calculations written out, not new nodes that repackage clauses of this item.

## Review by Q18

I checked delivery-errors B--E against the statement and all four proof steps with the sources and cited node statements open. There are no new statement-only nodes whose data, notation, searches or hypotheses could hide a missing construction. No cited proof, definition-only theorem, or reference tag is being used in place of a stated result.

Step 1 uses `def-weil-affine-spectrum` precisely for its existence and uniqueness of the map on coordinate rings, and `lem-weil-pbc-algebra-tensor-pushout-universal-property` for the product algebra. Their statements supply the required morphism correspondence and universal property, respectively. Their universal properties identify Spec(B tensor F[M1]) as the product by a bijection on maps from every affine spectrum. The two explicit inverse maps identify the tensor algebra with finite formal sums over B. Taking the allowed F-algebra A=B[M1 direct-sum M1] supplies the two universal group elements and the common X-point; the group-homomorphism hypothesis then gives the displayed coefficient identity. Taking A=B and its identity X-point gives the counit identity. This is a direct substitution into the hypothesis, not an unproved relative-Hopf equivalence or a Yoneda theorem invoked without a citation. This step is elementary relative to the two cited universal properties and the supplied group-algebra formulas.

Step 2 compares the finite-support function values on (m,l), separately for equal and unequal indices. Its orthogonal-idempotent equations follow from the actual written universal identity, over an arbitrary B. It cites no theorem and is elementary. In particular it does not misuse linear independence of group-like elements over a field as linear independence over B.

Step 3 uses exactly the statement of `lem-pc-scheme-connected-iff-idempotents`: connected, nonempty X has only 0 and 1 as idempotent global sections. X is nonempty because x0 exists. Also b0:B to F implies 1_B is not 0_B. The finite sum and orthogonality then prove existence and uniqueness of a coefficient equal to 1, in two elementary inferences written in the step. This generic criterion is already Lean-closed; the tool use is declared for completeness. No properness, geometric connectedness, reducedness or domain condition is imported from other statements.

Step 4 applies b0 to each already computed image of e_n, then includes F back into B. Both maps fix the coefficient 1, so the two algebra maps agree on every finite formal sum. The final citation of `def-weil-affine-spectrum` uses its uniqueness clause, not merely the definition of a spectrum. There is no unstated descent or comparison theorem at this point.

I tested the proof on M1=0, M2=0, on B=F[epsilon]/(epsilon squared), on a connected reducible affine ring, and in characteristic p with diagonalizable p-torsion such as mu_p. It uses no reduced-points argument and works in all these cases. If connectedness is omitted, orthogonal coefficients on B=F times F really do allow different characters on the two components, confirming the precise role of the hypothesis. Finite generation and algebraic closedness are not needed by this coordinate proof, but remain in the unchanged statement. No step exceeds 2000 characters; each contains a single direct calculation or application, with no hidden non-elementary sublemma. citations.json was generated from the actual cited statements, and proof_deps is exactly the union of uses. No cycles are introduced by the three reused nodes, whose statements/dependencies were read.

## Unfinished work

None in the stage-1 split. No Lean file was written and no compiler, Lake or build tool was run. Delivery remains subject to the required server dry run and independent maintainer review.
