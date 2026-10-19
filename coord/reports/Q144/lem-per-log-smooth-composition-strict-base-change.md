# Stage-1 report: Q144

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-log-smooth-composition-strict-base-change.json: item, statement split into seven proof steps; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-fs-log-infinitesimal-criterion.json: one new statement-only lemma, unsplit; no Mathlib match.
- citations.json: verbatim cited-statement excerpts, including the existing square-zero base-change lemma.

The retained split, citations, and searches.jsonl were recovered from the earlier attempt. They were compared with the current shared item, whose statement remains unchanged and whose status was unsplit. There was no report.md, hence no initial retained report to dry-run. No Lean was written or compiled; only the sandbox was written.

## Attachments

None. A fresh search of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the item tag and LogSmooth, LogEtale, logSmooth, logEtale and logarithmic found only unrelated logarithmic derivatives. There is no project declaration stating the item or the new criterion.

## WANTED

WANTED: Kato, Logarithmic structures of Fontaine--Illusie, Definitions 3.1--3.3 and Theorem 3.5, printed pp.200--202, for lem-per-fs-log-infinitesimal-criterion. The previous attempt recorded an online check at https://math.uchicago.edu/~drinfeld/p-adic_periods/Kato_log-structures.pdf; this document is not in local literature. The local ILO references to that theorem were re-read. The item's proof is explicitly agent-origin rather than claimed to be a verbatim proof from an unavailable local source.

## Findings and corrections

The imported statement has been preserved. The source's short assertions of composition and log-etale blowups were not complete DAG proof steps. The recovery retains the earlier seven-step argument, and explicitly cites the existing first-order-thickening base-change theorem in the two-stage lifting step. Locality is marked non-elementary because it uses several etale permanence statements. No new node merely restates one of the item's closure clauses. The sole new node is the chart/infinitesimal equivalence, a different characterization used as input to the actual lifting arguments.

The locally Noetherian qualification is retained throughout: strict base change is asserted within that category. Fine test log schemes in the new criterion are explicitly allowed to have arbitrary underlying schemes, so it does not quietly restrict the infinitesimal test class to Noetherian schemes or to saturated test monoids. Strictness and the square-zero condition are specified. No statement dispute was found. No SGA source is used.

## Unfinished work

Nothing remains for this one-level split. The new criterion is deliberately statement-only and remains for a later stage-1 worker. The Kato document remains wanted locally, as explicitly recorded.

## Searches and blueprint route

Retained searches.jsonl was read in full. The five searches for the new criterion include grep, LeanSearch, Loogle and two distinct LeanFinder phrasings. Their hits concern ordinary smooth/etale scheme morphisms and ordinary formally smooth/etale algebras; none includes logarithmic structures or strict logarithmic lifting. The item itself has the inherited searches and the four additional recorded searches from this sandbox. No unavailable service has been recorded as a no-match result, and no unexecuted search has been added. The queries in the node records are unchanged from the logs.

The ancestor command gives lem-per-artin-gabber-affine-curve. Whole-blueprint searches for log smooth, infinitesimal and Kato find no matching blueprint node; logarithmic finds only the unrelated trace and zeta nodes. DAG searches by Kato, 3.5, lifting, strict square zero and log smooth were read. The new node's from.place and via name the inherited ancestor's Step 3, through the ILO XVI 3.7 geometric modification chain. This only supplies logarithmic chart calculus below that route. The chapter and unit records were read and were not changed. Generic scheme and log-chart tools from other units are declared in split_report.tool_uses for maintainer review.

## Not duplicates

lem-per-fs-log-infinitesimal-criterion vs lem-per-log-smooth-composition-strict-base-change: the new criterion equates chart smoothness/etaleness with infinitesimal lifting; the item proves composition, strict base change, locality and blowup assertions using that equivalence.
lem-per-fs-log-infinitesimal-criterion vs def-per-fs-log-smooth-etale: the existing definition specifies charts and finite group conditions, and contains no lifting equivalence.
lem-per-fs-log-infinitesimal-criterion vs lem-per-kato-lattice-chart-realization: the existing lemma realizes a prescribed lattice and logarithmic differential basis in an etale chart, assuming log smoothness; it does not characterize log smoothness by tests against square-zero immersions.
lem-per-fs-log-infinitesimal-criterion vs lem-per-trait-log-smooth-uniformizer-chart: the existing lemma gives a special uniformizer chart over a trait, assuming log smoothness, not the infinitesimal equivalence for general bases.
lem-per-fs-log-infinitesimal-criterion vs lem-per-equivariant-log-smooth-chart: the existing lemma produces equivariant charts under a finite tame group action, not a characterization of general log smooth or log etale maps by lifting.
lem-per-fs-log-infinitesimal-criterion vs lem-trf-log-smooth-log-regular: that statement concerns preservation and recognition of log regularity, not infinitesimal tests.
lem-per-fs-log-infinitesimal-criterion vs lem-trf-log-regular-saturation-normality: that statement is about saturated complete local models and normality, and cites Kato 1994 rather than the 1988 infinitesimal criterion.
lem-per-fs-log-infinitesimal-criterion vs lem-trf-complete-toric-monomial-factors: that statement is a complete-ring divisorial-recognition input, not a lifting criterion.
lem-per-fs-log-infinitesimal-criterion vs lem-trf-log-regular-monomial-tor: that statement is monomial Tor independence, unrelated to infinitesimal log smoothness.

## Review by Q144

I re-read ILO VIII 3.3.3--3.3.11, printed pp.107--108, and X Proposition 1.2 and its proof, printed pp.136--139. VIII gives the log ideal/blowup construction, strict restriction, saturation and the log-etaleness assertion; X recalls Kato 3.5 and explicitly gives the fs chart refinement. I also read XVI Proposition 3.6.3 and its proof, printed p.252, which explicitly identifies its fs chart result as a refinement of Kato 3.5. These are the local sources of the item and new node. Kato's full infinitesimal equivalence is isolated in the new node, with its exact reference and local availability recorded above; it is not silently treated as elementary.

For Step 1 I opened lem-per-fs-log-infinitesimal-criterion, def-per-fs-log-smooth-etale and lem-trf-associated-log-universal-stalks. Unique lifting implies existence with the identity cover; identities and strict etale maps use identical monoid charts. The associated-log lemma explicitly gives the chart universal property and etale restriction, rather than just a definition of log structures.

For Step 2 I opened lem-sbc-locally-finite-presentation-composition and lem-weil-pbc-etale-covering-composition as well as the new criterion. Their statements give respectively the underlying composite's finite presentation and composition of the actual covering families produced by lifting. I added lem-weil-pbc-first-order-thickening-base-change, whose statement explicitly preserves both the closed immersion and square-zero ideal under arbitrary scheme base change. The two successive liftings have the correct intermediate map T_j to Y. In the log-etale case uniqueness is checked first after composing to Y, and then for the lift to X; it is not inferred from the smooth existence case.

For Step 3 I read def-trf-fs-log-blowup, def-pc-fibre-product and the full associated-log lemma. The product construction uses the fs chart of X pulled back to the ordinary scheme product; strictness of Y' to Y is essential. The argument writes the universal map on chart elements and units and checks uniqueness, so it does not cite the associated-log lemma as a nonexistent arbitrary fibre-product theorem. The resulting chart remains the same fs monoid. This is an elementary construction from those definitions, not a hidden theorem about non-strict fs fibre products.

For Step 4 I opened lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-finite-presentation-base-change-composition and def-sbc-locally-finite-presentation. The first gives exactly the affine tensor ring, the second allows arbitrary scalar extension, and the third is the local finite-presentation condition used by the criterion. The lift to X is paired with the fixed map to Y' via Step 3; this proves the needed lifting square rather than asserting an unidentified base-change compatibility. Because the original f is log smooth it is locally finitely presented, so the base-changed schemes remain locally Noetherian over the locally Noetherian Y'.

For Step 5 I opened all four etale covering/permanence lemmas in its uses. Composition and cancellation apply to the actual scheme morphisms in the factor U_i to X times_Y V_i, whose projection to X is etale by the base-change lemma. The strictness comes from both source structures being pulled back from X. For the reverse direction the definition's chart neighborhoods simply compose; the covering-composition statement gives joint surjectivity. Target covers pull back by the covering-base-change statement. This is marked non-elementary in the repaired split.

For Step 6 I opened lem-trf-coherent-log-ideal-chart-construction in full. It actually states the saturated charts, their group completions, descent and the universal property, not merely the definition of blowup. Thus P to Q_e^sat has identity group completion, kernel and cokernel zero, and the comparison scheme map is the identity on the stated tensor ring. The affine-fibre-product statement justifies this precise comparison. The chart definition then gives log etaleness, and uniqueness of the universal object identifies every representative. No new blowup-etale clause-node is needed.

Step 7 is finite induction, including the empty tower. Its only external notion is the finite tower in def-trf-fs-log-blowup; the induction uses the log-etale composition already proved in Step 2. I checked trivial log structures (ordinary smooth/etale lifting), identity maps, empty underlying schemes, principal log ideals (identity blowup), and a two-generator toric blowup (group completion unchanged). The square-zero test requires no flatness assumption on the immersion. No argument assumes the blowup is strict or smooth as an ordinary scheme map.

Against delivery-errors B--E: the new node is self-contained and has no proof or proof dependencies; every new notion is defined inline or names its defining node, and TeX has one escaping layer. Source places and the wanted Kato reference are explicit. Existing nodes were reused for scheme permanence and saturated blowup construction. Every proof citation has a verbatim statement quote in citations.json; each cited statement was read for the actual clause used. All seven steps are under 2000 characters, and none hides an independent comparison lemma: strict product construction, chart-family locality and tensor-ring comparison are written explicitly. Dependencies are forward inputs and the new criterion does not depend on the item. No off-route theorem replaces a unit step; generic tools are declared. Mechanical cycle, route and delivery validation is performed by the required server dry run.

## Dry-run repairs

The first server preflight rejected Step 3 for the phrase "the item's scope" (B2). I replaced it with the explicit locally Noetherian category and scheme names; the mathematical construction and all hypotheses are preserved.
