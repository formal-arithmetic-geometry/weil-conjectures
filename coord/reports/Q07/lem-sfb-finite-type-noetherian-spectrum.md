## Worker report

Q07, stage 1, 2026-10-17. Item: lem-sfb-finite-type-noetherian-spectrum. Statement unchanged. The final split has seven proof steps using five existing nodes and creates no new nodes or Mathlib leaves. No Lean writing, compilation, Lake or build command, push, or live-project edit was performed.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-type-noetherian-spectrum.json`: assigned statement, status split; no Mathlib match for the whole theorem.
- `citations.json`: six entries, covering every node cited in every numbered proof step; quotes are the full verbatim cited statements.
- `report.md`: this report. `searches.jsonl` is the actual search-command audit log; `split_q07.py` is a sandbox-only editing script.

## Attachments

None. Searches under slopmaster2 `WeilConjectures/` by the exact blueprint tag and by Noetherian spectrum, polynomial-spectrum Noetherianity, finite type and the theorem's title found only results with stronger Noetherian-ring or field hypotheses. In particular, `WeilConjectures/Mathlib/RingTheory/Spectrum/Prime/Noetherian.lean` proves the finite-type-over-a-field result, not the assigned assertion. The upstream master was checked as reference only; no sorry declaration is treated as an attachment.

## Literature wanted

WANTED: J. Ohm and R. L. Pendleton, “Rings with Noetherian spectrum,” Duke Mathematical Journal 35 (1968), pp. 631–639, Theorem 2.5 and Corollary 2.6, for lem-sfb-finite-type-noetherian-spectrum. The cited original paper is absent from the local literature collection and was not downloaded or claimed to have been read. Accordingly the proof is explicitly agent-written. The missing paper does not leave a gap: the item's seven steps supply an independent proof, down to existing Mathlib facts.

## What needed repair

The imported node was an unsplit statement with a WANTED original source. An initial sandbox draft incorrectly retained that statement-only state and described it as ready; self-review rejected it because the assigned item must have a complete proof. The final draft supplies the argument rather than moving the assertion into an equivalent child. No statement dispute or change of hypotheses was necessary. Ring-theoretic Noetherianity is never inferred from topological Noetherianity.

## Not duplicates

No new nodes are created. The nearby existing nodes were read: `lem-weil-pbc-finite-type-noetherian-finite-presentation` assumes a Noetherian base ring and concludes finite presentation; `lem-wf-affine-noetherian-components` assumes a finite-type algebra over a field. Neither states this theorem. Whole-DAG and blueprint searches for Noetherian spectra, finite-type Noetherianity, polynomial extension, Ohm and Pendleton found no duplicate theorem. Searches for monic division found the already existing `lem-weil-pbc-monic-quotient-free`, which was reused instead of creating a division-algorithm node.

## Review by Q07

I read the item, the `sk-lem-coefficient-heart` unit, the `sec-six-functors-basics` chapter, the main-20261015 ancestor `det-lem-coefficient-heart-closure` and its proof, and the full statements of all five proof dependencies. This proof supplies the affine-chart topological-Noetherianity tool needed within the prescribed Bhatt–Scholze monodromy route. It does not replace that unit route. The ancestor and intermediate parent in `blueprint.from` are preserved and `same_as=[]` is confirmed by blueprint-wide searches.

For the local sources, I read Stacks `topology.tex`, definition-noetherian and lemma-Noetherian (0052), including the minimal-counterexample proof; and `algebra.tex`, lemma-Zariski-topology (00E0), lemma-standard-open (00E4), lemma-spec-closed (00E5), lemma-irreducible (00ES). These prove exactly the spectrum facts used below. For the monic-quotient input, I read the existing node and Mathlib `RingTheory/AdjoinRoot.lean` at `AdjoinRoot.powerBasis'` (633), which gives a basis of powers of the polynomial root for a monic polynomial. Its basis statement gives the remainder representative used in step 4; a bare freeness assertion would not suffice.

Step 1 proves the topological facts rather than hiding them behind a definition: complements convert ACC into DCC; closed subspaces inherit closed-chain stabilization; two Noetherian subspaces give stabilization on their union by taking the maximum of two indices. The recursive strictly descending chain proves validity of induction on closed subsets. These are elementary consequences of the stated chain condition, including the empty space.

Step 2 states the induction claim precisely, for the inverse image of every closed base subset under contraction. Continuity is checked by the formula on zero loci. The empty and reducible cases are proved using step 1; both closed subsets in a reducible decomposition are proper and closed in the original base. No induction on dimension or ring ideals is substituted for induction on closed subsets.

Step 3 uses only the statements of `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus` and `lem-weil-pbc-spec-irreducible-components-minimal-primes`. The former identifies Spec(R/J) with the irreducible closed set, and the latter identifies its whole-space irreducible component with V(q) for a minimal prime. The quotient correspondence pulls q back to a prime p of R. This avoids taking the irreducible-closed-set clause from the cited node's proof: its actual statement is about components, and it is applied to the entire irreducible quotient spectrum. The coefficientwise quotient map has precisely pR[T] as kernel, as the text proves. Thus its domain reduction is justified even when R is nonreduced.

Step 4 uses `def-weil-ring-localization-away` for the explicit fraction relation and `lem-weil-pbc-monic-quotient-free` for the actual power basis in the monic quotient. The coefficient ring C is a nonzero integral domain and the leading coefficient a is nonzero. Inverting a makes f monic; its quotient power basis represents a remainder of degree less than deg f. A common power a^N clears the finite number of denominators, and the displayed equation puts that remainder in the original ideal after multiplication. Domain injectivity ensures that a nonzero remainder stays nonzero and retains its degree, contradicting minimality. These hypotheses would fail if the argument were applied before passage to a domain. The degree-zero case is explicitly covered by the empty basis. The generic-principality argument is proved within this step and is not introduced as a new node.

Step 5 uses `lem-weil-pbc-spec-localization-away-basic-open` clause (ii), which explicitly gives the required homeomorphism onto D(a). Increasing vanishing ideals I_i are constructed from the closed chain; their equality of zero loci is proved without using an uncited radical-ideal correspondence. Their union is an ideal and f lies at a finite stage. Only finitely many polynomial coefficients are involved in the coefficient-localization isomorphism. The extended ideals then coincide with the principal ideal on that open, giving the claimed chain stabilization. No uniform denominators for infinitely many polynomials are assumed.

Step 6 uses the induction hypothesis already stated in step 2 and the quotient identifications already proved in step 3. The zero prime omits a, so the base closed complement is proper. It is closed in the original base, not merely in an open. The restricted chain stabilizes there by induction and on D(a) by step 5; taking their union proves stabilization everywhere. This is elementary assembly of the established argument, with no additional theorem input.

Step 7 uses the quotient-spectrum node again, now with the actual finite-type presentation from the hypothesis. Ordinary induction on the finite number of variables uses the one-variable result just proved, and the closed-subspace argument proves the conclusion for its quotient. This retains every clause of the item, including unital maps and zero rings.

I checked delivery-errors B–E against these final files. There are no new nodes, hence no clause restatements or unsearched auxiliary results. The five cited nodes were opened and each use is supported by the verbatim quote in citations.json. Their dependency closures do not refer back to the item. They are already Mathlib leaves, so no non-Mathlib off-unit tool declaration is needed. The absence of the original paper is disclosed, all source attributions separate the agent argument from sourced subfacts, and no SGA source is used.

Mathlib searches were performed only through `msearch.py` and are recorded verbatim from its JSONL log. Both semantic phrasings returned `Algebra.FiniteType.isNoetherianRing`, `PrimeSpectrum.instNoetherianSpace` and related stronger results. I read `Spectrum/Prime/Noetherian.lean:28–31` and `FiniteType.lean:187–194`: both require `IsNoetherianRing R`, which is absent here. The initial unqualified Loogle queries were invalid and are recorded as unavailable/inconclusive; a corrected quoted-name query returned the same stronger spectrum instance. No failed service is counted as proof of absence.

Small cases: R or B zero; d=0; nonreduced rings with a one-point spectrum (including non-Noetherian square-zero thickenings); a field and unit leading coefficient; I=0; I the unit ideal; constant least-degree f (n=0); empty closed sets; and reducible bases. The min-degree argument is also checked on an ideal generated by arbitrarily many nonzero multiples of T: after one selected leading coefficient is inverted it becomes (T), so no finite-generation assumption on the ideal has slipped in. Every test is consistent with the original statement.

## What remains

The required server dry run must print OK before this sandbox is handed to the second reader. No push is authorized for this worker.

## Second reading by Q07

- Item statement: checked against the imported target and the stated Ohm--Pendleton Theorem 2.5/Corollary 2.6 source description; hypotheses (unital finite type map, topological Noetherianity only, zero rings) and conclusion agree; the original paper is unavailable locally and remains marked WANTED.
- Step 1: checked against Stacks Tags 0052 and the definitions; complement equivalence, closed-subspace and finite-union arguments, and Noetherian induction are elementary and correctly cover the empty space.
- Step 2: checked the contraction continuity formula and the induction claim on every proper closed subset; empty and reducible cases use only Step 1 and have the required properness hypotheses.
- Step 3: checked both cited quotient-spectrum and minimal-prime component statements verbatim; the quotient kernel, prime pullback, domain reduction, and contraction compatibility are explicitly proved and do not use a cited node's proof.
- Step 4: checked the localization fraction relation and monic-quotient power-basis statement; denominator clearing is finite, injectivity uses the domain hypothesis, and the degree-zero case is covered.
- Step 5: checked the increasing ideals, zero-locus equalities, coefficientwise localization, and the cited basic-open homeomorphism; stabilization on the open is justified without a uniform-denominator assumption.
- Step 6: checked that the zero prime makes the complementary closed subset proper and that the induction hypothesis applies in the original base; the two stabilized restrictions assemble over the stated cover.
- Step 7: checked finite-variable induction, the finite-type polynomial quotient, and the cited closed-subspace homeomorphism; zero-variable, zero-ring, and zero-algebra cases are included.
- New nodes: none. Therefore B1--B7, duplicate-node checks, Mathlib-leaf searches, and per-node edge-case checks are vacuous; all five proof dependencies were opened and their quoted statements in `citations.json` match verbatim.
- Small cases rechecked: field and zero rings, $d=0$, constant polynomial, empty closed sets, reducible and one-point spectra, nonreduced square-zero examples, unit leading coefficient, and the unit/zero ideals.

Changes made: no mathematical or citation changes were needed. I added this second-reading section and ran the required server dry run, which printed `OK (not pushed)`.
