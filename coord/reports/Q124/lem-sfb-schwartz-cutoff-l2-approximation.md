## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-schwartz-cutoff-l2-approximation.json — item, statement unchanged, split into six explicit steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-real-dominated-integral-convergence.json — statement, Mathlib leaf: MeasureTheory.tendsto_integral_of_dominated_convergence, Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:57.
- citations.json — one verbatim statement quotation for every dependency of every proof step.

## Attachments

None. Searching lean/WeilConjectures for the exact blueprint tag, Schwartz and analytic cutoff concepts found no project declaration stating the item. No Lean file was written, and no compiler, Lake or build was run.

## WANTED

WANTED: Jean-Pierre Demailly, Complex Analytic and Differential Geometry, VI §2, weak-derivative Sobolev setup before (2.1), printed p.289, for lem-sfb-schwartz-cutoff-l2-approximation. The cited PDF is absent locally. An attempted online open timed out. The proof is explicitly agent-written; it is not presented as text read in Demailly or as a numbered theorem of his book.

## Problems found and repaired

The item previously had only a statement. Its earlier Mathlib search correctly distinguished approximation of a function in Lp from simultaneous approximation of its derivatives; I retained those searches and read the relevant candidates, then added actual recorded searches under Q124. No statement dispute or change of hypotheses was necessary.

The current blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This is a supporting analytic prerequisite far below proof (3), along the inherited alteration/GAGA/Kodaira/Sobolev chain, not a new route for the chapter or unit. The ancestor tool prints blueprint.from.node = None for this inherited chain; this existing null anchor and its complete via chain have been retained, with a precise additional place for the new leaf. No invented blueprint ancestor was substituted.

## Not duplicates

lem-sfb-real-dominated-integral-convergence vs lem-sfb-normal-series-interval-integration: the former concerns sequential almost-everywhere convergence of real functions on Euclidean space with an integrable varying pointwise bound; the latter concerns normally summable continuous series on a compact interval. The latter cannot supply this proof's convergence on all of Euclidean space. Both cite the same Mathlib file but different declarations.

No Stacks tag is claimed for this analytic input. Whole-DAG statement/concept searches for dominated convergence and its Mathlib declaration found no existing equivalent node. Whole-blueprint searches for dominated, dominated convergence, Schwartz, cutoff and Leibniz found no equivalent analytic assertion; the cutoff hits were unrelated weight/truncation nodes. Searches of Lean project sources found no project attachment for the new input. The three reused analytic nodes were opened and their actual statements read.

## Review by Q124

I checked the item against its self-contained Schwartz definition and the current unit and chapter records. The local Demailly source is missing, so the source status is WANTED and the actual argument is signed as an agent proof. For the new leaf I read Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:38-64: its theorem assumes almost-everywhere strong measurability of each term, integrability of the bound, the pointwise norm bound almost everywhere for every index, and almost-everywhere convergence. Specializing the domain to Euclidean space and codomain to real numbers gives exactly the new statement, with no finite-total-measure hypothesis. Lebesgue-measurable real functions are almost everywhere strongly measurable relative to volume; equivalently the completed Lebesgue measure has the same integrals and almost-everywhere statements. Semantic search and Loogle both returned this declaration; source grep fixed its line as 57. The leaf is a statement only, with empty proof and proof dependencies.

Step 1 cites lem-sfb-euclidean-smooth-ball-bump for all required clauses, including 0 ≤ χ ≤ 1, equality on the unit closed ball and compact support on the radius-two closed ball. It cites lem-sfb-schwartz-test-inclusion-integrability only for inclusion of a smooth compact test into Schwartz space, not for a derivative bound that its statement does not contain. The iterated coordinate closure and L2 assertions are precisely the two appropriate clauses of lem-sfb-schwartz-l2-coordinate-calculus. Its repeated application yields every multi-index derivative; the zero-weight bound of the Schwartz definition supplies each Bγ. I also read SchwartzSpace/Basic.lean:550-567,1308-1325 and SchwartzSpace/Deriv.lean:90-105 to check the reused Mathlib facts.

Step 2 gives one explicit sequence with R_n = n+1, so dilation never divides by zero. Smooth composition and multiplication, containment of the product's closed support in a compact dilation image, and compactness of that image are elementary operations. Its two cited statements then give Schwartz inclusion and L2 membership of all derivatives of the approximants. It does not assume the approximants converge merely because they are Schwartz.

Step 3 carries its own short induction for the multi-index Leibniz and dilation formulas: the base case, differentiation of the two factors, reindexing and Pascal's identity are all written. No separate node is made for these routine calculus consequences. Step 4 uses that each fixed point lies in the open unit plateau of the rescaled cutoff for all large n; this also makes all positive-order cutoff derivatives zero there. This is stronger than simply claiming χ_n tends to 1. The squared difference is integrable by the explicit inequality 2|a|²+2|b|² and the preceding L2 conclusions.

Step 5 cites the coordinate-calculus node exactly for square integrability of the finitely many Schwartz derivatives. The elementary finite-sum inequality gives the displayed Gβ, independent of n; R_n≥1 is essential here. Its finite nonnegative combination is integrable. This avoids assuming integrability of a constant bound on the infinite-measure Euclidean space. Continuity proves the measurability required by the convergence theorem.

Step 6 cites only the new dominated-convergence leaf, whose statement explicitly gives integral convergence under the verified hypotheses. Its input is the nonnegative real function |E_n,β|², the limit is zero, and the bound is Gβ. Taking square roots is justified by the ε² estimate. The sequence is independent of β and s, so no inconsistent selection of separate approximants occurs. Every dependency quotation in citations.json is copied verbatim from the cited statement, not from its proof or a definition with a different assertion.

I checked delivery-errors B–E against the files: the new statement introduces every object, uses single TeX escaping, records only searches actually made by msearch.py with exact query text, and gives the Mathlib declaration, path and line. Its blueprint fields explain the inherited analytic prerequisite. The one new leaf is a general integration theorem, not a clause or restatement of the approximation item. All reused statements are actually adequate (C4); no unrecorded non-elementary analytic convergence result remains (C1). The chain/product rule induction, finite-sum algebra, compact dilation and square-root limit are the elementary argument itself. Every step is below 900 characters, so none hides a long unreviewed lemma.

Edge cases checked: ψ=0 gives identically zero approximants; β=0 has the singleton index set and no positive-order terms; s=0 is therefore covered; n=0 uses radius one; m=1 is unchanged. Empty support of ψ causes no problem because only compactness containment is used. Integrability is asserted for every derivative appearing, rather than treating the totalized Bochner integral as an L2 norm without proof. No assertion is made in dimension zero because the given item assumes m≥1.

## Unfinished work

None in this one-level split. The sole new dependency is already a Mathlib leaf. Independent mathematical acceptance remains the maintainer's review after delivery.
