# Q29 — lem-per-qe-rotthaus-finite-boundary

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-qe-rotthaus-finite-boundary.json`: item split into six steps, with the contextual quotient G-ring hypothesis restored.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-bounded-formal-singular-primes-stabilize.json`: statement-only lemma, not in Mathlib.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-bounded-normalization-limit-finite.json`: statement-only lemma, not in Mathlib.
- `citations.json`: a verbatim statement quote for every step-node pair.

## Attachments

None. I searched the live project under lean/WeilConjectures for the item tag, Rotthaus, Nishimura, bounded prime sequences and normalization limits. No declaration states the item. The broader Sheaf.RingTheory.QuasiExcellentCompletePair declaration is sorried and does not constitute an attachment. No Lean source was written and no compiler was run.

## Literature wanted

WANTED: Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber), Theorem 5.3 printed p.11 and the surrounding proof of Theorem 5.1, for lem-per-qe-rotthaus-finite-boundary; author copy https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf . Its inherited source field refers to an earlier worker's sandbox copy, which I have not treated as an archived project source.

WANTED: J. Nishimura and T. Nishimura, Ideal-adic Completion of Noetherian Rings II, Algebraic Geometry and Commutative Algebra II (1988), pp.453–467, especially Definitions 1.1–1.6, Theorem 1.9, Lemmas 1.10–1.17 and Proposition 1.18, for both new nodes and the item. DOI https://doi.org/10.1016/B978-0-12-348032-3.50006-2 ; searchable primary preview https://books.google.com/books?id=W7biBQAAQBAJ . I read available primary-source preview passages, not an unobtained full PDF; later preview requests were rate limited. Bibliographic integration and full-page checking of these two statement-only source lemmas remain for their future splits. I have not claimed to reproduce a full source proof: the item has proof_origin.by = agent.

WANTED: C. Rotthaus, Rings with approximation property, Math. Ann. 253 (1980), pp.213–226, Hilfssatz and proof pp.214–220, for comparison with the earlier form of the criterion (digitized original at https://gdz.sub.uni-goettingen.de/id/PPN235181684_0253 ). I read those scanned pages online. They impose universal catenarity and a simple (good and bounded) prime sequence. The present proof uses Nishimura–Nishimura's later route, not an unsupported application of that earlier theorem.

## Statement corrected

STATEMENT-DISPUTED: the standalone imported criterion omits the quotient hypothesis needed by its own cited stabilization route. Proposition 1.18 assumes (in its condition (1.18.3)) that A/xA is a Nagata P-ring, as well as the local lifting theorem for P. For P = regularity this means a Nagata G-ring. Merely declaring B to be Nagata and x-complete does not provide the premise “B/xB is a G-ring” of that application. This is the explicit failed hypothesis check; I am not asserting a counterexample to the unqualified conclusion of Kurano–Shimomoto Theorem 5.3, which states the compressed criterion without this contextual condition.

I added “B/xB is a G-ring” to the item and its definition dependency. B/xB is Nagata because B is Nagata (the definition tests all prime quotients, unchanged after passing to a quotient). This repairs the referenced proof route faithfully to its use in the quasi-excellence argument. Neither the conclusion nor the definition of Delta was altered. The item is an auxiliary node, not a target statement or the unit's key node.

Both current citers continue to satisfy the added hypothesis: lem-per-qe-complete-pair-lifting uses B from lem-per-qe-normal-counterexample-reduction, whose statement explicitly gives B/xB quasi-excellent; lem-per-gabber-adic-quasi-excellence uses its corresponding gabber reduction, also with quasi-excellent quotient. Quasi-excellent includes G-ring. Their final application steps should mention that premise explicitly when next maintained. No citer was edited.

## Proof and genuine new content

The first new node says that a bounded contracted minimal-singular-prime family becomes extended on a cofinal set of finite semilocalizations. It does not assert positive height, nonzero contraction, or the item's conclusion. The second node concerns arbitrary good prime families over a complete Nagata domain: it constructs a finite normalization limit and controls its principal boundary contractions. It has no singularity hypothesis or height conclusion. Together they expose the two different substantive parts of the original proof; neither is a renamed clause of the item.

The assembly assumes zero contraction and hence reduces to a domain. It deals with x=0 directly, proves x is a nonunit, applies the two source lemmas, and then uses lying-over to produce a normalized boundary over a prime minimal over xB. The adic quotient identity identifies the contracted boundary prime in D_gamma as minimal over xD_gamma. Krull's principal ideal theorem bounds its height by one, whereas the strictly smaller positive-height s_gamma gives a chain of length two. This avoids importing universal catenarity from Rotthaus's older formulation.

## Not duplicates

lem-per-bounded-formal-singular-primes-stabilize vs lem-per-qe-rotthaus-finite-boundary: eventual extension of the family, without any height or nonzero-contraction conclusion, is the intermediate Proposition 1.18 input, not the Hilfssatz itself.

lem-per-bounded-formal-singular-primes-stabilize vs lem-per-formal-singular-ideal-patching: the latter patches one radical ideal in a maximal-ideal completion of a fixed semilocal ring under regular completed comparison maps; it neither varies finite semilocalizations of a nonsemilocal ring nor proves eventual extension of the contracted prime family.

lem-per-bounded-formal-singular-primes-stabilize vs lem-per-compatible-formal-ideal-adic-descent: that node descends ideals modulo powers from a fixed semilocal maximal-ideal completion under faithful-flatness and radicality hypotheses; it gives no good prime sequence or finite-boundary stabilization theorem.

lem-per-bounded-normalization-limit-finite vs lem-per-qe-rotthaus-finite-boundary: finiteness and boundary control for the explicitly defined normalization limit of an arbitrary good bounded family precede the final height argument; there is no singular-prime or positive-height hypothesis and no nonzero-contraction conclusion.

lem-per-bounded-normalization-limit-finite vs lem-per-compatible-formal-ideal-adic-descent: a module-finite inverse limit of normalized prime quotients is a different object and conclusion from extension of a fixed ideal modulo powers.

Whole-DAG key-word searches included Rotthaus, Nishimura, prime ideal sequence, normalization/normalisation limit, bounded formal prime and singular-prime stabilization. Whole imported blueprint searches for Rotthaus, prime ideal sequence, normalization inverse limit, normalization limit and singular primes found no node stating either new lemma. I read the current latest blueprint ancestor, chapter and unit. Ancestry follows the item's existing regular-model/completion route, and same_as is empty.

## Mathlib searches

All searches were executed with the prescribed msearch.py command and are preserved in searches.jsonl. Each node records its exact queries and returned summaries. Each new node has semantic LeanFinder and LeanSearch queries, Loogle and source grep, and a second wording. The item also has two original wordings plus a new search with the restored G-ring quotient premise. No unavailable query was counted as a negative result. LeanFinder returned generic completion, finite-prime, Henselian and unrelated good-product results; LeanSearch returned basic adic-completion constructions. Loogle returned IsIntegralClosure.isNoetherianRing, about finite field extensions over a Dedekind domain, not the normalization limit. Its source-file grep was also read. The results do not yield a one-line specialization to either new statement. There are zero new Mathlib leaves.

## Review by Q29

I checked the node files against delivery-errors B–E with their statements open. Kurano–Shimomoto Theorem 5.3 supplies the original formulation; Nishimura–Nishimura's available primary preview supplies the good/bounded definitions, Proposition 1.18 stabilization hypothesis, Lemma 1.17 module finiteness, and Lemma 1.11 boundary contractions. The first new node specializes P to regularity and restricts to the zero-contraction, nonzero-x case actually needed; its local lifting prerequisite is the known G-ring lifting theorem, separately already present as lem-per-local-g-ring-adic-lifting. The second new node states precisely the normalization system used by the source: the map for gamma subset delta is D_delta to D_gamma, with inverse image p_delta of p_gamma. I corrected an initially ambiguous contraction notation so it states that orientation explicitly. Both new files have empty proof and proof_deps; their statements introduce every ring, indexing set and map, with definitions cited or inline meanings. They contain no proof sketch.

Step 1 uses only the Jacobson-radical conclusion of lem-weil-pbc-adic-complete-jacobson-radical; the domain and x=0 calculations are written out and need no flatness theorem. A maximal ideal is given, so the zero ring and unit x cases are impossible. Positive height is used only to contradict the zero prime in the x=0 case.

Step 2 uses exactly the eventual-extension conclusion of the first new node. All its hypotheses are explicitly checked: its singular prime, normalization and finite boundary set are the same objects, and zero contraction was established in Step 1. Step 3 uses exactly injectivity, module finiteness and the minimal-boundary assertion of the second node. Its family is cofinal after gamma_0 and is both compatible and extended. I opened lem-weil-pbc-finite-algebra-is-integral and the Stacks 00GK lemma; it supplies integrality from module finiteness, rather than silently treating that as a definition.

Step 4 uses three different existing statements: existence of a minimal prime over a proper ideal, integral injective lying-over, and existence of a minimal prime below a specified prime. I read each statement. The finiteness-only minimal-primes node was deliberately not used as an existence theorem. The normalization-limit lemma supplies exactly the final contraction into Delta. Every ideal's properness or prime status is checked where used.

Step 5 takes only the surjectivity and kernel formula at N=1 from lem-weil-pbc-adic-completion-mod-power. The quotient and localization prime correspondences are written by inverse images and the fraction test; inclusion reflection and minimality follow in a few lines. No flatness, dimension formula or catenarity is hidden here. Step 6 cites the actual Noetherian-localization and Noetherian-completion statements before applying the principal-ideal height bound. I read Stacks 0316 (lemma-completion-Noetherian-Noetherian), 00FN and 00KV (lemma-minimal-over-1); their assumptions and conclusions agree with the cited nodes. The height contradiction uses the definition as a supremum of finite chain lengths, so works without finite dimension or a saturated-chain assumption.

Small-case checks: if A is local, the indexing set has one member; eventual extension is tautological and the limit lemma reduces to finiteness of normalization of a prime quotient of a complete Nagata domain, with the asserted boundary contraction tautological. For p_gamma=0 in a normal complete domain, the normalization system specializes to the expected completed semilocal rings. x=0 and a unit are excluded in the new limit theorem and resolved explicitly before applying it. Empty boundary is allowed in that statement; under its hypotheses its finite integral limit and lying-over in the assembly show why it cannot occur here. The item allows non-domains initially, but zero contraction forces a domain before any domain-only result is applied. No source requiring universal catenarity is used without that hypothesis. None of the six proof steps exceeds 2000 characters.

The corrections made during this review were restoration and reporting of the quotient hypothesis, removal of the ambiguous contraction orientation, separate citations for integrality and minimal-prime existence, and replacement of a potentially catenary height comparison by the principal-quotient argument. Every cited node has an exact verbatim quote in citations.json. Generic off-unit algebra tools are declared in split_report.tool_uses. No SGA source, Lean edit, compiler, repository write, launcher edit, local preflight, or agent was used.

## Remaining work

Nothing in the stage-1 split is intentionally left open. The two new nodes are unsplit by design and queued for their own proofs. The absent full Nishimura–Nishimura paper is explicitly requested above; its source-level lemmas, rather than purported reconstructed proofs, are the new frontier. The independent maintainer review should especially check the contextual hypothesis repair and the precise boundary clause of the normalization-limit lemma against the full paper.
