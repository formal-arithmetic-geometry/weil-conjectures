## Worker report

Files written:
- dag/nodes/sec-deligne-laumon-a1/lem-per-tame-normalization-log-regular.json: item split into six steps, existing normalization/excellence tools and three new logarithmic facts.
- dag/nodes/sec-deligne-laumon-a1/lem-per-regular-boundary-divisorial-chart.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-prime-to-order-snc-kummer-charts.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-invertible-kummer-chart-log-regular.json: statement, unsplit; no Mathlib match.
- citations.json: one verbatim statement quotation for each step/dependency pair.

The sandbox contained only dispatcher brief markers when resumed. No previous report, nodes, search log, or active delivery process existed. The current repository item and its inherited searches were retained. No Lean was written or compiled, and no shared project or launcher files were changed.

## Attachments

None. Searched the read-only WeilConjectures source by the exact blueprint tag, item id, tame normalization, log regularity and Kummer. The project KummerTorsor file constructs torsors of units and their automorphisms; it does not prove logarithmic regularity of a normalized ramified cover. EtaleTorsorSpreading explicitly says that tame ramification and purity are not formalised there. The item has no existing Lean declaration or audit frontier to attach.

## WANTED

None: the proof uses the locally available ILO volume and Stacks sources. Its new chart-preservation statement is supported by ILO VI 1.8 together with VI 2.2--2.3, rather than depending on an unavailable standalone chart-criterion reference.

## Corrections and limitations

The item originally cited def-sc-normalization, which defines normalization only in the original function field. The item already explicitly defined normalization in the finite extension field correctly. I replaced that definition reference by the existing def-fin-normalization-extension and changed the corresponding statement dependency. No hypothesis or conclusion was changed, and no statement dispute is needed.

The imported source reference to VI 2.3 is evidence for preservation of log regularity under Kummer covers, not a proof that the underlying finite morphism is etale. The existing lem-trf-log-smooth-log-regular assumes a torsion-free cokernel; ramified Kummer charts have a finite torsion cokernel, so I did not use that theorem. The new preservation lemma records invertibility of the torsion exponent instead. The conclusion is log regularity, not ordinary regularity.

All three new nodes are unsplit statements without proof sketches, proof steps, or proof dependencies. They join the queue. The item supplies the argument combining them and does not delegate its whole conclusion to any one of them. Finiteness and excellence remain proved separately by existing nodes. There are no unfinished tasks inside this one-level split.

## Searches and route

I read the chapter sec-deligne-laumon-a1 and unit sk-p-dl-a1-perverse, and the current main-20261015 ancestor lem-per-artin-gabber-affine-curve proof. This item is a supporting node of the already-developed ILO IX uniformization branch of that ancestor, through lem-per-gabber-prime-to-ell-regular-cover. I did not change chapter or unit records. Each new blueprint.from names that ancestor, keeps the complete inherited via chain with this item prepended, and identifies its place in IX 2.1--2.2. Whole-blueprint searches for log regular, log smooth, normal crossings, divisorial, Kummer etale, Kummer charts and Abhyankar returned no statement matching the proposed children. The broader Kummer and logarithmic hits concerned torsion cohomology and weights, not these assertions.

I searched all dag/nodes statements and titles for the concepts, normalization, finite separable integral closure, excellence, tame ramification, and the ILO VI/IX places. This found and led to reuse of the finite separable integral-closure theorem, generic normalization theorem, excellence permanence, normal components, generic pullback and divisorial recovery. Every cited statement was opened. The Mathlib results for each proposed id are saved in its -searches.json file; the msearch.py log is searches.jsonl. Each has two semantic phrasings, Loogle, grep, and LeanSearch, with exact query texts and outputs copied into mathlib_searches. All services succeeded on these calls. No unavailable service is reported as absence. Relevant hits were ordinary scheme normalization, standard smooth presentations, ordinary etale base change, the regular-sequence dimension formula and arithmetic Kummer extension theory. None has fs logarithmic structures or the assertions of the children. No Mathlib leaf is claimed.

Generic tool uses outside the unit are declared in split_report.tool_uses: normal decomposition, finite separable generic fibres and pullbacks, finite integral closure, generic normalization, excellence permanence and divisorial recovery. These implement the fixed ILO branch and do not replace a unit-level proof step with another route.

## Not duplicates

lem-per-regular-boundary-divisorial-chart vs lem-trf-snc-divisorial-log-chart: the existing statement assumes a smooth finite-type scheme over an algebraically closed field. The new statement works on arbitrary regular Noetherian schemes, including mixed characteristic and arithmetic bases, and cannot specialize that existing theorem.

lem-per-regular-boundary-divisorial-chart vs def-trf-strict-normal-crossings-boundary: the latter defines the boundary by regular intersections; it does not establish the divisorial chart, finiteness/saturation or regular-stratum dimension theorem.

lem-per-regular-boundary-divisorial-chart vs lem-trf-regular-local-ufd-boundary-factorization: the existing local ring factorization result assumes parameters already chosen; it neither produces charts from the global regular-intersection boundary nor proves logarithmic regularity.

lem-per-regular-boundary-divisorial-chart vs lem-per-tame-normalization-log-regular: the child is a theorem about the original regular boundary with no covering; the item concerns the possibly singular normalization in a ramified extension.

lem-per-prime-to-order-snc-kummer-charts vs lem-per-tame-normalization-log-regular: the chart theorem assumes finite normalization and concludes existence of compatible fs monoid charts with an etale comparison, not finiteness/excellence or log regularity. Step 2 proves the assumed finiteness, and Steps 3, 5 and 6 are still needed to get the item's log regular pair.

lem-per-prime-to-order-snc-kummer-charts vs lem-sbc-trait-generic-normalization-charts: the latter concerns smooth schemes over a DVR with one special-fibre divisor. The new theorem concerns an arbitrary-dimensional strict normal crossings boundary and simultaneous monoid charts at intersections.

lem-per-invertible-kummer-chart-log-regular vs lem-trf-log-smooth-log-regular: the existing theorem assumes torsion-free group cokernel, whereas the new theorem treats finite cokernel annihilated by an invertible integer; neither is an applicable specialization of the other for nontrivial ramification.

lem-per-invertible-kummer-chart-log-regular vs lem-trf-log-regular-toric-refinement: that result assumes Q lies inside P's original group completion, so the group map is an isomorphism. Kummer root charts enlarge that group completion by finite index.

lem-per-invertible-kummer-chart-log-regular vs lem-trf-log-regular-divisorial-structure: the latter starts with log regularity and recovers divisorial structure. The new theorem proves the source's log regularity from explicit chart hypotheses.

## Review by Q73

I read ILO Expose IX Proposition 2.1 and paragraph 2.2, printed pp. 133--134, together with VI 1.2--1.8 and 2.1--2.3, printed pp. 69--73. IX 2.1 identifies tame covers of the regular normal-crossings complement with Kummer covers on the normalization. IX 2.2 makes precisely the log-regular-pair inference used here. VI 2.2 supplies compatible charts with invertible finite group cokernel and VI 2.3 explicitly says the source is log regular when the target is. In the invertible-order torsor case there is no wild inertia: locally at each boundary valuation the wild inertia is a residue-characteristic group inside the torsor group, whose order is invertible. The new chart node packages this ramification/extension theorem; the item's steps do not use it silently. I read the boundary regular-intersection criterion in VIII Remark 4.2.2(i) and the free-chart/rank discussion of VI 1.5(i) for the regular-boundary child.

For the normalization part I read Stacks algebra.tex Tag 032L, label lemma-Noetherian-normal-domain-finite-separable-extension: the input is a Noetherian normal domain and a finite separable field extension, exactly the data established before applying it. I read morphisms.tex Tag 035L, label lemma-normal-normalization, for normal integral generic normalization, and more-algebra.tex Tag 07QU, label lemma-finite-type-over-excellent, for excellent finite-type algebras and their localizations. The stronger reduced-scheme normalization preparation node only normalizes the original generic fields; it was deliberately not used for normalization in L.

Step 1 uses rem-pc-regular-normal for normality of V, lem-weil-pbc-finite-type-over-noetherian for Noetherianity of the finite cover, and lem-fin-etale-normal-components for its disjoint normal integral components. Each statement supplies exactly that assertion. Nonemptiness follows from the torsor over the nonempty complement, and connectedness then leaves one component; I did not infer irreducibility of an arbitrary connected scheme. The generic pullback is finite etale by the actual pullback statement lem-galois-descent-data-existence. The definition def-weil-etale-morphism supplies unramifiedness, so lem-trf-unramified-field-fibre-decomposition supplies finite separability. The finite-dimensional domain is a field by the injective/surjective multiplication argument written in the step.

Step 2 uses def-fin-normalization-extension for gluing in L, rem-pc-regular-normal for normal affine rings, Tag 032L's existing node for module finiteness, and def-weil-finite-integral-morphism for the affine criterion of finiteness. The generic normalization node gives normal integrality with L as function field. Noetherianity guarantees quasi-separatedness for its hypothesis; its canonical generic point is the one of Y. Excellence uses the original excellent affine rings and the finite-type/localization theorem, and Noetherianity uses the finite-type-over-Noetherian theorem. A finite module generating set generates the algebra, so no unsupported finite-implies-finite-type step was hidden.

Step 3's new boundary node gives exactly the fs divisorial structure, free charts, regular strata and dimension formula used. Its regularity and Noetherian hypotheses hold globally and T is precisely the boundary in the statement. Step 4's new chart node assumes finite b, already proved, and invertibility everywhere on Y, present in the item; it gives all monoid data and the etale comparison used next. Step 5's new preservation node then has both locally Noetherian fs schemes, a log-regular target, injective Kummer charts, and invertible finite cokernel. This check corrected the tempting but invalid use of the existing torsion-free-cokernel lemma. I did not assert ordinary regularity or ordinary etaleness of b.

Step 6 uses the chart theorem's characteristic-identification clauses to identify the exact triviality locus. The equivalence P=0 iff Q=0 is written out using injectivity, the Kummer multiple property and sharpness, rather than assuming that the source has no extra boundary. The existing divisorial-recovery statement supplies density and equality of the log sheaf with the divisorial one on that exact locus. The definition of log regular pair then applies. The final step cites no proof-internal construction of any existing node. The citations.json quotations are verbatim from every cited statement and include the parts used.

For small cases I checked empty boundary (P=Q=0 and a finite etale regular cover), the identity torsor (identity chart), a one-parameter tame root t=s^n with n invertible (injective group map with cokernel Z/n, showing why torsion-free is wrong), and a two-branch cover z^n=xy (its normalization can be singular, while log regularity still holds). The arithmetic regular trait with n invertible is allowed; the smooth-over-an-algebraically-closed-field chart result would not cover it. Dropping invertibility permits wild ramification and is not claimed. The rank-zero monoid and zero-branch chart are explicitly allowed; none of the new statements excludes them.

I checked B1--B10 against the written files: children have standalone hypotheses and statements only, notions cite their definitions, the extension-field normalization reuses its existing definition, searches ran and are recorded verbatim, and blueprint ancestry is filled. C1--C8 were checked by opening each cited statement and ensuring the preceding steps supply its hypotheses; off-unit generic tools are declared. D1--D5 were checked by retaining the actual combination argument in the item: no child states all its clauses, and neither a lemma nor an induction is justified circularly. E1--E7 were checked on the source hypotheses and the small cases above; the main repaired inference is torsion-free versus invertible torsion in the Kummer chart. Every proof step is shorter than 2000 characters. No second worker is claimed: this is the authorized direct-delivery self-review, followed by the maintainer's independent review.
