# Stage-1 report: lem-a1-finite-locally-free-principal-basis-cover

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-finite-locally-free-principal-basis-cover.json: item, statement unchanged, four proof steps, status split; no exact Mathlib match.
- citations.json: eleven verbatim statement quotations covering every step citation.
- report.md: this report. searches.jsonl was produced by the prescribed search command.

No new nodes and no new Mathlib leaves.

## Attachments

None for the item. The source-library rank theorem covers only the first clause, not the finite principal basis cover and the canonical fraction maps. It is already attached to lem-pc-flf-properties, which this split reuses. FiniteFlatNorm.lean's exists_isAffineOpen_mem_free_app gives local freeness without this whole fixed-rank, finite principal-cover and section-formula conclusion. I searched WeilConjectures by the blueprint tag, finite locally free, locallyFree, principal basis and their variants; no declaration states every clause of this item.

## WANTED

None.

## Corrections and route

The statement is retained verbatim. The old source locator 04MH concerns decomposition by rank and does not provide the principal refinement; I replaced that locator with the actual sources of the argument. No chapter or unit changes. I read the chapter and sk-p-real-rankin unit records and the current latest blueprint's lem-a1-affine-hc0 proof. This node is a historical auxiliary affine-groupoid/norm-polynomial branch beneath that ancestor, as its existing blueprint.from.place and via record explicitly explain. This proof supplies the principal-chart preparation used by the parent norm construction; it introduces no different route for the unit.

The basic-open section-localization lemma from sk-thm-p1 is a generic tool: it applies to any quasi-coherent module on an affine open, and no lemma in the item's unit supplies it. It is declared in split_report.tool_uses. The rank lemma is already Lean-closed. The remaining statement tools are Mathlib leaves, and the other citations are definitions.

## Mathlib searches

Retained all four inherited 2026-10-22 searches. Ran the four prescribed tools for the item itself, with exact queries recorded in searches.jsonl and appended unchanged to mathlib_searches. The scheme phrasing returned IsFinite.finite_app and affineBasisCoverOfAffine; these give finite sections and an unrestricted basic-open cover, not the required finite fixed-rank trivializations. The second, module-theoretic phrasing returned exists_basis_localizedModule_powers, which assumes an already supplied basis after localization and finite presentation. I read Mathlib/RingTheory/Localization/Free.lean:41-94 and the relevant cover source. The promising nonempty_basis_of_flat_of_finrank_eq in LocalRing/Module.lean:395 assumes Finite (MaximalSpectrum R), explicitly visible at line 389; our ring need not be semilocal. None is an exact or one-line match for this whole item. Loogle and grep supplied consistent candidates. No searches for new nodes are needed because there are no new nodes.

## Not duplicates

No new nodes. In particular, reused lem-pc-flf-properties, lem-weil-pbc-affine-module-basic-open-localization, lem-weil-pbc-spec-localization-away-basic-open, lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact, and lem-weil-pbc-affine-open-section-vanishing-prime. Whole-DAG title/statement searches and blueprint_refs searches for finite locally free and principal found these ingredients rather than a duplicate of the entire assertion.

## Review by Q124

I read Stacks morphisms.tex definition-finite-locally-free and lemma-finite-flat (02KB), schemes.tex lemma-spec-sheaves (01HV), lemma-standard-open-affine (01I3), and lemma-quasi-coherent-affine (01IA), and algebra.tex lemma-Zariski-topology (00E0) and lemma-quasi-compact (00E8). The sources apply to arbitrary commutative rings. I checked the module basis and localization definitions in the cited DAG statements. There are no new-node sources to audit.

Step 1 uses lem-pc-flf-properties exactly for the assertion that p_*O is locally free of rank r; its statement explicitly has our degree hypothesis. I checked its existing closed Lean attachment in Modules/FinitePushforward.lean, and did not claim its proof supplies the other clauses. def-pc-finite-locally-free specifies degree by fibre dimension, so the degree convention is not silently changed to sheaf rank. def-amb-finite-locally-free-module explicitly gives both the rank-r open trivializations and quasi-coherence. The latter is a recorded assertion of the cited definition node, not an unstated claim that arbitrary sheaves are quasi-coherent.

Step 2 uses the ring-localization clause (b) of lem-weil-pbc-affine-open-section-vanishing-prime for A_f. For E the cited affine-module-basic-open-localization statement gives precisely two conditions: a power multiple of any section extends, and a section restricting to zero is killed by a power. I wrote out why these yield surjectivity and injectivity, rather than citing the definition of localization as if it were that theorem. Pushforward global sections are B by definition. The quotient relation, scalar action, multiplication and the two algebra-localization fraction formulas are checked from the cited ring/module localization definitions. This step is elementary assembly from those statements, not an uncited affine equivalence theorem. In particular, it needs quasi-coherence, which was obtained in step 1, and it uses the whole affine Spec A, not an unjustified affine intersection.

Step 3 uses the exact neighbourhood-basis clause of spec-localization-away-basic-open, not merely a homeomorphism of spectra. It refines each chosen trivializing neighbourhood. The compactness and unit-ideal clauses of spec-basic-opens-unit-ideal-quasi-compact then give a finite subcover and the desired ideal equality. Nonemptiness is built into the initial choice of a point in each open. If A=0 the ring-map identity forces B=0, and the empty ideal equals A; all the cover assertions then hold with m=0.

Step 4 uses only the definition of a basis and the trivializations already constructed. Taking sections of a finite direct sum is explicitly coordinatewise; transporting its coordinate vectors through the canonical isomorphism gives an r-element module basis. I wrote its value on every subopen to check that the original sheaf trivialization is exactly the basis-induced one. Thus I did not assume a new fully faithful sheafification theorem. The empty basis works when r=0; for example A nonzero and B=0 still has valid nonempty base charts and zero local modules. When A is disconnected the fixed degree r is used everywhere; no global freeness is asserted. Nilpotents and zero divisors do not affect the power-kernel localization argument. No finiteness of the maximal spectrum or Noetherian assumption is used.

I checked delivery-errors B through E: no statement-only child hides a proof, no new node restates a clause, no unintroduced hypotheses or duplicate nodes, and no unsupported cited conclusion. Each citation was read as a statement; citations.json copies the full statements verbatim. All four steps are below 2000 characters. The source-tag correction changes only provenance, not mathematics. No SGA source is used.

## Unfinished

No mathematical part of the split is unfinished. Stage-1 delivery still requires the prescribed dry run and push; their outputs are the delivery record.
