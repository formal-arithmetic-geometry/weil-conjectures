# Stage-1 delivery: lem-trf-charted-log-map-local-right-inverse

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-charted-log-map-local-right-inverse.json`: statement, split into four steps using two existing nodes; no Mathlib match.
- `citations.json`: verbatim statement excerpts for every step/node citation, checked against the live node text.
- `report.md`: this report. `searches.jsonl` is the unmodified log written by the required msearch command.

New nodes: 0. New Mathlib leaves: 0. The statement, statement dependencies, source, title and all maintainer-owned fields remain as received. The item is not the unit's key statement, so no unit realization record was written.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint id, LogStructure, PrelogStructure, associated-log, charted-log, local-right-inverse and logarithmic-chart notions found no declaration stating this item. The broad logarithmic search returned only logarithms of power series and number-theoretic constructions, not log structures. No sorried or partial declaration is treated as finished.

## WANTED

WANTED: K. Kato, “Logarithmic structures of Fontaine–Illusie” (1988), section 1, for the associated-log construction underlying `lem-trf-associated-log-universal-stalks` and the conventions recalled in ILO VI 1.1. The present split uses the existing node's complete statement as its interface; it does not claim to have read this missing reference. The proof is marked agent-written.

## What was wrong or incomplete

The received item had no proof. Its statement is consistent with the cited source's chart-extension intent; no correction or STATEMENT-DISPUTED change was needed. ILO VI 3.7(a) ends with extension of the splitting on a sharp chart, but does not state the present general right-inverse lemma separately. I have made that extraction explicit and retained `proof_origin.by = agent`.

It would be unjustified to lift just the generators and assume their relations hold, or to assume finite generation of the unit sheaf. The already existing finite-monoid stalk-data node gives a homomorphism on all of Q, with all relations, even for a nonintegral finitely generated commutative monoid. It also supplies equality after one affine pointed refinement. No additional presentation node was needed here. Structure compatibility requires no extra shrinking: it follows from alpha_N = alpha_M f and fk=q.

The separate assertion gf=id on a neighbourhood is not asserted by this item or used in this proof. The parent spreading node establishes that later using its finite chart on N. The present result only needs fg=id and the inverse at the specified stalk.

## What could not be finished

Nothing in the requested split remains unfinished. Its child statements may themselves still require work, as allowed for a one-level stage-1 split. No Lean files, compiler, Lake, or build commands were used. No agents were started. Only the assigned sandbox was written; the sanctioned delivery tool constructs its own temporary delivery tree.

## Not duplicates

No new nodes were created, so there are no new/existing tag pairs. Whole-DAG keyword searches found `lem-trf-finite-monoid-stalk-data-spreading` and `lem-trf-associated-log-universal-stalks`; these are reused rather than re-created. The related `lem-trf-prelog-pushout-hom-extension` and `lem-trf-commutative-monoid-sheafification` provide lower-level inputs already packaged into the associated-log node and are not added as redundant direct citations. The parent `lem-trf-fine-log-stalk-chart-spreading` depends on this item and is not cited by it.

Whole-blueprint searches with `tools/blueprint_refs.py search` for “log chart”, “right inverse”, “logarithm”, and “log structure” found no equivalent blueprint statement (the right-inverse hits concern idempotent splittings). `ancestor` returned `lem-trf-local-term-locality`. The item's existing precise from.place and ancestry are retained; same_as is the searched empty list. I read the current main-20261015 local-term proof and the chapter/unit records. This is a supporting lemma on the already recorded monoidal-resolution ancestry, and makes no change to the unit or chapter route.

## Mathlib searches

The five searches logged for this item on 2026-10-23 are recorded verbatim, with their actual tool names and query strings, in mathlib_searches. They include LeanFinder in two different phrasings, Loogle, LeanSearch and the prescribed grep. All services answered; none was marked unavailable. The original 2026-10-22 search records remain intact as historical records.

The first LeanFinder phrasing returned locality and inverse-stalk-map results for ordinary locally ringed spaces, whose hypotheses concern isomorphisms or localness rather than logarithmic structures with monoid charts. The second phrasing returned number-field log embeddings and a manifold-sheaf result. Loogle and grep returned zero log-structure hits. LeanSearch returned PresentedMonoid.lift and ordinary monoid algebra/localization universal properties. I read PresentedMonoid.lift and its surrounding hypotheses and uniqueness theorem in Mathlib/Algebra/PresentedMonoid/Basic.lean:118–144: this extends a function respecting a prescribed presentation, and does not lift anything through a geometric stalk or construct a log sheaf map. None is an exact match or one-line specialization of the item.

## Review by ND

I read ILO Expose VI 1.1 (printed p. 69, PDF p. 75) and 3.7(a) (printed p. 75, PDF p. 81), including the final sentence on extending the restriction of the splitting to a chart near x. I also read the Stacks text in etale-cohomology.tex at lemma-cofinal-etale (Tag 03PQ), definition-stalk (Tag 040R), and the following description of equal germs, which explains the refinement mechanism. I read the complete statements of both proof dependencies, the log/chart definition and the geometric-stalk definition, rather than relying on their titles. There are no new-node sources to review.

For step 1, the finite-monoid node explicitly says that a specified monoid homomorphism into a geometric stalk lifts on an affine pointed refinement. I checked that Q is commutative and finitely generated, N is a sheaf of commutative monoids because it is a log structure, X is locally Noetherian, and (X,x) is an allowed initial neighbourhood. The composite h=f_x^{-1}q_x is a monoid homomorphism since f_x is an isomorphism. The same node explicitly supplies restriction-stalk identifications. No integrality, saturation, finite chart on N, or finite generation of N(U) is introduced.

For step 2, that node's equality clause applies to the two homomorphisms fk_0 and q into M(U), not to arbitrary sections of unrelated stalks. Their germs are equal by the inverse identity for f_x. Its affine-refinement and local-Noetherian clauses give the required final V and justify using the associated-log theorem on V later. Restriction preserves the specified germ of k. I checked the structure-map equation directly: alpha_N k = alpha_M f k = alpha_M q. This is the substantive simplification from an approach that would unnecessarily descend structure-map equalities independently.

For step 3, the associated-log node states both compatibility with etale restriction and that any chart identifies its target with the associated log structure, so it applies to q restricted to V. Its actual universal-property bijection has exactly the hypothesis alpha_N k=beta established in step 2 and exactly the conclusion of unique extension over the identity. I did not cite the mere chart definition as if it supplied this theorem. Units are fixed by the log-morphism statement; their sheaf need not have finitely many generators.

For step 4, the same bijection is injective when the target log structure is M|_V. Both fg and identity are log homomorphisms over V and their composites with q|_V are equal by fk=q. This proves equality of sheaf morphisms on all of V, not merely equality of their marked stalks. Taking the marked stalk gives f_x g_v=id; composing on the left with the given inverse of f_x yields g_v=f_x^{-1}. The canonical identifications and the germ of k were already fixed in step 1 and preserved in step 2. The citations.json excerpts contain the literal universal-property, restriction, chart and spreading sentences used here.

I tested the statement on the trivial monoid Q with empty generating tuple: its only homomorphism lifts, and a chart by Q is the trivial log structure, so the extension fixes precisely units. For Q=N the construction lifts one generator; for Q with an idempotent generator e^2=e the finite-monoid lemma includes that relation, and no cancellation is used. For a finitely generated group chart all chart elements are units, and the forced unit lift agrees with the log universal property. Identity f gives the expected local right inverse. A completely arbitrary source log structure N introduces no further hypothesis anywhere. These checks rule out the common mistaken integral-monoid or finite-unit assumptions.

Against delivery-errors B–E: there are no new statement-only nodes to hide a clause or to duplicate existing results; no external notation is used as a substitute for a statement. Every non-elementary step cites a node whose statement supplies the invoked fact, and proof_deps is exactly the union of uses. I marked all four steps non-elementary because they invoke spreading or a universal-property theorem; the short algebraic equalities within them are written out. No step exceeds 2000 characters, and the complete assembly proof is under 3000 characters. I checked the two cited nodes do not require this item: the finite-data node is a separate general spreading fact, and the associated-log node's dependencies concern logification and sheafification, not chart spreading. The source contains references elsewhere to SGA, but this split uses no SGA result and follows the existing ILO/chart route.
