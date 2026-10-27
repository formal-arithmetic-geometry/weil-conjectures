## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-strict-support-horizontal-exchange.json`: statement; split in four steps. Mathlib does not state the full normalized strict-tower result. Existing generic Mathlib mate laws are used through `lem-weil-pbc-mate-pasting`.
- No new nodes; no new Mathlib leaves. `citations.json` contains a verbatim statement quotation for every step/node citation. `searches.jsonl` retains the actual search results.

## Attachments

None. I searched the project source for the exact blueprint tag, strict/horizontal combinations, and compact-support exchange. `AlgebraicGeometry.CompactSupportFormalism.shriekBaseChange_id` and `.shriekBaseChange_paste_horiz` in `lean/WeilConjectures/SixFunctors/LowerShriek/Formalism/BaseChange.lean` (lines 383 and 411) are generic formalism laws, not declarations instantiating all the normalized constant-B strict-tower operations in this item. Finite-coefficient derived compact-support declarations have a different coefficient category and do not attach this arbitrary-B, arbitrary-unbounded-tower statement.

## WANTED

None.

## Faults and corrections

No statement dispute and no statement change. The item was statement-only; it required a proof of the actual two-factor transformation equality. Its original searches were retained and five searches actually run for Q86 were appended, including a second semantic phrasing. The Loogle mate hits and the second LeanFinder query identify the general mate laws already represented by the existing Mathlib leaf, not the complete item. I read `Mathlib/CategoryTheory/Adjunction/Mates.lean` at `mateEquiv_vcomp` (line 170) and `mateEquiv_hcomp` (line 209); the former has exactly the three-adjunction/non-adjoint-side pasting needed here.

The Stacks source omits verification of horizontal pasting. Step 1 supplies its strict-tower specialization through two existing lemmas; step 3 spells out the naturality calculation combining it with open base change. No assertion about derived evaluation being faithful is substituted for equality in the tower category.

## Unfinished work

None in this one-level split. Its cited existing nodes retain their own proof obligations.

## Not duplicates

No new nodes. Before writing the proof I searched all DAG nodes and the imported blueprint for horizontal pasting, mates, strict towers and the cited Stacks tag. This found `lem-cbc-strict-tower-pullback-square-pasting`, `lem-cbc-tower-open-beta-normalization`, `lem-cbc-strict-tower-proper-open-calculus` and `lem-weil-pbc-mate-pasting`; the proof reuses existing statements. The bounded-below etale statement `lem-weil-pbc-exchange-identity-pasting` is not applied to the different category here. No new abstraction or single-clause restatement was introduced.

## Review by Q86

I read the chapter `sec-smooth-purity`, the unit `sk-prop-sf-cbc`, the item and all six statement dependencies. I read the current blueprint `main-20261015` proof of `thm-cbc-complete-proetale`, whose final sentence requests coherence of the two factors; the split realizes its identity/horizontal part at the strict-tower stage. I read Stacks `sites-cohomology.tex`, Tag 07A7 (`remark-base-change`, lines 4033ff.) and Tag 0E47 (`remark-compose-base-change-horizontal`, lines 4094ff.). The former defines the actual unbounded exchange as the adjunction transpose of the counit after the pullback square, and the latter states composition along base changes. The strict-tower specialization is marked agent-written. No SGA source is used.

Step 1 uses the actual statement of `lem-cbc-strict-tower-pullback-square-pasting`, not an inference from its proof: substituting p,p',p'' for its vertical maps gives exactly the equation for the inverse pullback squares with their gComp comparisons. Its arbitrary-map hypotheses include these proper maps. The normalized compositor definition in `def-cbc-strict-constant-tower-operations` supplies the chosen identifications. Clause 1 of `lem-weil-pbc-mate-pasting` says that the mate of that paste is the composite of the mates, with L1=G_p, L2=G_p', L3=G_p''. This gives the displayed E equation with R_p'' of the ambient compositor on the output and the inverse base compositor on the input. Clause 3 of the same generic statement also supports changing from composite transverse functors to their specified isomorphic ones. The square lemma and the mate lemma require neither boundedness nor finite coefficients. I did not cite the etale-only exchange-coherence node as a general strict-tower theorem.

Step 2 uses the first open-square assertion of `lem-cbc-strict-tower-proper-open-calculus`, which I read in full: it explicitly states that the inverse beta is the open-unit transpose, that successive base changes compose with canonical pullback compositors, and that these assertions hold for arbitrary B. The finite-origin assumptions in the later proper/open gamma assertion are not used. The open squares here are cartesian by the supplied base-changed compactifications, so this application preserves all hypotheses. Writing that existing pasting assertion with both endpoint compositors gives exactly the additional beta equation requested by the item; it is not a new lemma.

Step 3 is elementary assembly from the preceding two equations. I checked the cancellation order: R_p'' of the inverse ambient compositor immediately precedes R_p'' of the forward ambient compositor after substitution. I checked the only interchange at an arbitrary M: naturality of E_h is applied to beta_(j,gbar), whose source is G_gbar J_j M and whose target is J_j' G_g' M, both objects of D(T_V'). It therefore gives precisely the displayed equality and places E_h J_j' next to R_p'' beta_(j',hbar). Grouping produces e_h and G_h e_g, with the open-side compositor left at the output. This is a finite naturality/functoriality calculation, not a hidden theorem about compactification independence or proper base-change invertibility.

Step 4 uses the definition of a mate as a natural transformation, the explicit naturality and identity clauses of the strict-tower open calculus, the normalized identity comparisons of the operations definition, and clause 4 of the mate-pasting statement. These cited statements say exactly what is used: under identity comparisons the underlying square is identity, its mate is identity, and beta is identity. Composition then yields the identity law and naturality for e. Every step citation has a verbatim statement quote in `citations.json`.

I checked edge cases on the argument: an identity g or h reduces to the other factor; an identity open j removes beta and reduces to proper exchange pasting; an identity proper p removes E and reduces to open comparison pasting. The zero coefficient ring and zero input give identities on the zero objects. Infinite B and unbounded towers do not affect any categorical calculation, and no resolution or evaluation detection is used. There are no new statements requiring small-case testing. All four proof steps are under 2000 characters, and none hides a new comparison lemma. B1-B10, C1-C8, D1-D5 and E1-E7 were checked against these actual statements: no new nodes, no unmatched source clauses, no undeclared non-elementary step, no relabelling of the item, and no added coefficient or boundedness hypothesis. The generic mate citation is a pre-existing Mathlib leaf and the remaining tool statements lie in this unit.
