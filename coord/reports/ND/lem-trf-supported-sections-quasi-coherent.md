# Stage-1 delivery: lem-trf-supported-sections-quasi-coherent

## Files written

- dag/nodes/sec-trace-formula/lem-trf-supported-sections-quasi-coherent.json: item, statement, now split; no exact Mathlib match.
- citations.json: nine verbatim cited-statement excerpts, one per step/node pair.
- searches.jsonl: actual msearch.py results; the item retains its earlier search records and adds this run's queries.
- report.md: this report.

Zero new nodes; zero Mathlib leaves. prepare.py is sandbox-only preparation code, not a delivery node.

## Attachments

None. Searched lean/WeilConjectures by the blueprint tag, supported-sections vocabulary, and combinations of supported/quasi-coherent. No declaration states all the item's clauses. The module restriction and supported derived-object results concern different assertions; they are not attachments. In particular the source declarations underlying the generic principal-open tools do not themselves prove this item.

## WANTED

None.

## Corrections and source comparison

The statement is faithful to Stacks 07ZP, properties.tex, lemma-sections-supported-on-closed-subset (1)--(3), read at lines 3827--3890. Its vanishing-off-Z definition is the support condition in that lemma: a section is zero on an open precisely when its germs there are zero. No statement change or dispute was needed. The source gives the ideal-power formula using element support and radicals. The delivery writes the finite-generator argument instead, using the existing general compact-section power-torsion statement; this avoids creating a duplicate support lemma.

For quasi-coherence the source identifies the sheaf as the kernel of restriction to the direct image from the open complement. I read the cited pushforward proof in schemes.tex, Tag 01LC, lemma-push-forward-quasi-coherent. Rather than insert a new open-immersion or kernel lemma, the split verifies the existing principal-open criterion directly, using the already stated extension and torsion lemmas from that same affine localization argument. This is a node-level expansion of the source's kernel proof, and changes no unit-level route. The essential extra power is written explicitly: after extending s to t, multiply t by a further power to kill its restriction to W minus Z.

The current blueprint ancestor is literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md and its .proof.md, both read, along with the latest chapter/unit texts. It proves contracting local terms, not this algebraic support lemma; this node is an auxiliary through the inherited strict-transform/flattening route. The existing from.place already describes the exact intervening Stacks 080G/07ZP obligation and is retained. Searches across the whole DAG and blueprint for supported sections, sections supported, 07ZP, principal-open criterion, spectrum topology, and basic opens found no other blueprint node stating this lemma. The pro-etale support definitions do not concern quasi-coherent structure-sheaf modules. No blueprint text is silently substituted for the current one.

## Not duplicates

No new nodes. The five generic facts needed are cited as existing nodes. A finite basic-open cover and the resulting finite generated defining ideal are an elementary compactness step from the existing basic-open basis, not a new leaf; the ideal-power monomial calculation is also retained in the item's proof. Searches returned PrimeSpectrum.isCompact_isOpen_iff_ideal and finite basic-open descriptions, but those only prove this elementary part, not the full item. The stronger global ideal-existence node lemma-nagata-qc-open-complement-ideal-exists was not used: it would require passing from a finite type sheaf ideal to a finitely generated affine ideal, an unnecessary extra comparison.

## Review by ND

I read Stacks 07ZP for the item and Stacks 00F6 (algebra.tex, lemma-qc-open) for the finite ideal construction. I also read Stacks 01IA (schemes.tex, lemma-quasi-coherent-affine), the 01LC pushforward proof, and the project source statements of the principal-open criterion in Modules/QuasicoherentKernel.lean and compact-section/extension lemmas in Modules/QcqsSections.lean. No new nodes require source verification.

Step 1 is the direct sheaf gluing argument: restrictions, sums and scalar multiples stay zero off Z, and gluing stays zero by the sheaf uniqueness axiom on the complement. It uses no omitted theorem or categorical kernel identification.

Step 2 cites lem-weil-pbc-spec-localization-away-basic-open. I opened its statement: clause (i) actually states the basic-open basis and refinement property needed here. Retrocompactness as defined in the item supplies compactness of U minus Z. Selecting a finite subcover and testing prime containment gives J explicitly. No theorem giving quasi-coherent ideals is being mistaken for a theorem giving finitely generated ring ideals.

Step 3 cites lem-weil-pbc-affine-scheme-qcqs and pqf-lem-qcoh-compact-section-power-torsion. I read both statements: the former supplies compactness of the affine U, and the latter applies to arbitrary quasi-coherent modules on a compact open, not just the structure sheaf. It yields each individual generator power; the written monomial expansion yields an ideal power. The reverse implication uses invertibility of each generator on its basic open and sheaf uniqueness. The argument is for every finite generated defining ideal, as required, and is not limited to the ideal chosen in Step 2.

Step 4 cites pqf-lem-qcoh-qcqs-section-power-extension, lem-weil-pbc-affine-scheme-qcqs, and pqf-lem-qcoh-compact-section-power-torsion. The first statement gives extension after a power on W because W is affine, hence compact and quasi-separated by the second. The third needs only compactness on V=W minus Z, supplied by the item's hypothesis, and applies to t restricted to V. I checked the vanishing locus is precisely V intersect D_W(a), so its conclusion gives a supported extension a^k t and the exponent n+k. No extension theorem for the not-yet-proved quasi-coherent sheaf K is used.

Step 5 cites the same affine compactness and torsion statements and pqf-lem-qcoh-principal-open-criterion. I opened the criterion and copied its two actual hypotheses into citations.json. Step 4 verifies its extension condition for K; Step 5 verifies its vanishing condition using F and the sectionwise injective inclusion K into F. This supplies exactly quasi-coherence of K, with no unproved comparison or hidden pushforward hypothesis. Each of the nine quotes in citations.json is checked as an exact substring of its cited node's statement.

I tested the boundary cases: empty scheme/empty affine chart (zero ring); Z empty (K=0, defining ideals have full radical and the power calculation still kills the section); Z=X (K=F, J=0 allowed, with exponent 1); empty generator family; generators with exponent zero (increased to positive in the pigeonhole argument); and ideal-power exponent zero (forces m=0). No Noetherian, finite-type module, separatedness of X, or finiteness of F is used. For the extension step all separation assumptions are on the affine W, not on arbitrary X. Every non-elementary input has a node; elementary compactness, monomial expansion, unit multiplication and sheaf gluing arguments are written. All proof steps are shorter than 2000 characters. Generic off-unit citations are explicitly declared in split_report.tool_uses for maintainer review.

The Mathlib queries were run only through the prescribed msearch.py and their actual hits read. They returned quasi-coherence definitions, structure-sheaf restriction theorems, and ideal-sheaf constructions; none states the full supported-section theorem. Both natural-language phrasings were checked. No unavailable service is represented as an absence result.

## Unfinished work

None at stage 1. The existing dependency nodes retain their own proof obligations. No Lean was written or compiled, no agents were started, and all authored files are confined to the item sandbox.
