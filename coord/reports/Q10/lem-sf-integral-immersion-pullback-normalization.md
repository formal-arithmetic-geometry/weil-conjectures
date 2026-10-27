## Worker report

Item: lem-sf-integral-immersion-pullback-normalization. Group: Q10. Stage 1, direct delivery, 2026-10-22.

### Files written

- dag/nodes/sec-smooth-purity/lem-sf-integral-immersion-pullback-normalization.json: completed the proof in six steps; status split; existing statement and statement dependencies unchanged; preserved all original fields and earlier searches.
- citations.json: 22 entries, one for every cited node in every step. Each quote is the entire verbatim statement, so the precise claim and its hypotheses remain available to the checker and reader.
- report.md: this report and signed review.

### New nodes

None. No new Mathlib leaves. The relevant general statements already have DAG nodes.

### Attachments

None. I searched lean/WeilConjectures for the blueprint tag, completedPullback/derivedComplete and integral immersion/pullback terminology. No declaration in that project root proves the entire item with these actual completed coefficient categories, both specified comparisons and their shifts. The existing comparison theorem in lean/Sheaf/Paper/IntegralPullbackCompletedComparison.lean ends in sorry at line 314. It is evidence for the interface, not a finished attachment.

### WANTED

None for this assembly: all substantive claims are existing cited nodes. Their unresolved prerequisites retain their own source responsibilities. I used the Stacks source files present in literature/ and the blueprint proof; no unavailable Bhatt--Scholze PDF is claimed to have been read.

### Findings and corrections

The item was unsplit and the sandbox initially had only dispatcher marker files. There was no earlier proof or report to discard. I preserved the statement, including its global field, completed coefficient category, named comparisons and uniform interval requirement. No statement dispute arose.

The apparent need for a new normalization lemma disappeared after opening lem-a1-integral-pullback-completed-comparison and lem-sf-immersion-completed-pullback-comparison. The former compares the two specified integral constructions for arbitrary scheme maps, with projection equations and integer shifts. The latter supplies the actual completion comparison for locally closed immersions and the same reduction interval. Neither alone is an exact restatement of this item: the item assembles their two maps and verifies geometry, coefficients, transitions, exactness and linearity.

I did not infer a map into a homotopy limit merely from its individual projections. Step 4 cites the whole strict-tower comparison; step 5 uses augmentation-normalized Roos realization. This is essential because a bare triangulated derived-limit object does not select a unique completion map. In particular the existential triangle definition of derived completeness is not used as if it selected that map: the existing comparison lemma supplies the intrinsic-completeness implication and its specified comparison.

### Searches and blueprint route

I read the chapter sec-smooth-purity and unit sk-prop-sf-open-closed-triangle. I read the current main-20261015 proof of prop-sf-open-closed-triangle-all-stages. The assembly serves its integral-stage first paragraph (finite reductions of immersion pullbacks) and rational-stage first paragraph (exact R-linear integral pullbacks). It does not change the chapter or unit route.

Whole-DAG searches covered ordinary/completed pullback, immersion comparison, derived completeness, finite perfect quotients and the existing comparison module name. Blueprint searches were: `completed pullback`, `immersion completed`, `quotients perfect`, and `pullback comparison`. The completed-pullback search returned 25 blueprint nodes, the last 19; none states this entire paired normalization package. The two middle searches returned zero. The ancestor tool identifies prop-sf-open-closed-triangle-all-stages; the existing exact from.place and via chain are retained. No imported duplicate of the item was found, so same_as remains [].

The search-command log contains six actual searches in this run: two different LeanFinder phrasings, one LeanSearch query, one Loogle query, and two grep expressions. Their exact text and results are appended to the item's earlier records. I read every returned hit. The first LeanFinder result was scheme normalization; the second concerned ordinary algebraic adic completion and structure-sheaf restriction. In particular Mathlib AlgebraicGeometry/Sites/ElladicCohomology.lean lines 61–66 defines a coefficient sheaf and does not compare derived pullbacks; AlgebraicGeometry/Modules/Sheaf.lean lines 348 and 453 concerns modules over a scheme's structure sheaf; RingTheory/AdicCompletion/Exactness.lean line 184 concerns ordinary module completion. None supplies the item's pro-etale completed-coefficient functors or their normalized maps. Loogle's two hits are categorical pullback exactness. No service was unavailable.

### Unfinished work

None in this one-level split. Cited unsplit or sorried prerequisites remain independent existing work items. No Lean file was written, compiler run, repository file changed, or agent started.

## Not duplicates

No new nodes were created; there are no new/existing same-tag pairs to justify.

## Review by Q10

I read the item, its chapter and unit, and the current blueprint source with both integral and rational paragraphs open. I also read Stacks proetale.tex Tag 099N, label lemma-pushforward-Noetherian-case, especially (2) and (5), and Tag 09AA, label lemma-closed-immersion, (1). The former describes completed pullback as completion of ordinary pullback and as the limit of finite pullbacks; the latter gives preservation of limits for the closed inverse image. These are supporting sources, not claimed verbatim proofs of our entire normalized ring-sheaf package. The exact signed and strict-tower refinements come from the existing cited node statements. For auxiliary geometry I read morphisms.tex lemma-finite-type-noetherian and lemma-closed-immersion-proper, properties.tex lemma-locally-Noetherian-quasi-separated, and schemes.tex lemma-quasi-compact-permanence. For realization I read sites-cohomology.tex Tag 0941, lemma-derived-limit-is-ok, including its K-injective tower model. I read derived.tex Tag 015F, lemma-right-derived-exact-functor, which says every complex computes the exact derived functor.

Step 1 uses five existing geometry statements. Finite type over a Noetherian base gives X, and, after the closed-immersion-proper statement supplies finite type of i, also Z. The open-subscheme statement gives U. The locally Noetherian quasi-separated statement applies to each; the qcqs permanence statement then applies to j because U is quasi-compact and X quasi-separated. No claim that intersections of affine opens are affine is made. The field being Noetherian follows directly from its two ideals.

Step 2 uses the actual DVR statement for R and the standard-quotients-perfect statement, whose second case explicitly covers O_E, not only Z_l. The profinite inverse-image statement applies because each A_n is finite. Its statement explicitly contains the projection and transition equations and identifies the canonical maps, so it supplies more than an abstract ring isomorphism. Preservation of constant R-sections is checked at all finite projections.

Step 3 uses exactly the statement of lem-sf-immersion-completed-pullback-comparison: the actual specified comparison is invertible, ordinary pullback is exact and preserves completeness, finite reductions commute, and integral constructibility has the same uniform interval. Both i and j satisfy its locally closed condition by using an identity open or closed factor. This is an existing stronger lemma, not a new node restating the item.

Step 4 checks ell-invertibility from ell distinct from p on every k-scheme. The general integral/strict-tower node applies to every derived-complete K and asserts natural R-linearity, projection equations and the shift equation. The integral operations definition identifies the requested g_R^* with that node's source functor. The finite-pullback strict-tower node explicitly gives its comparison with actual quotient transitions and all derived morphisms; this justifies transition compatibility without reading a fact out of its proof. I checked the source and target of gamma: integral to strict completed, as required.

Step 5 checks all hypotheses of the exact-product strict-limit statement: exact immersion module inverse image along an isomorphism of coefficient sheaves, preservation of countable products, and exact products of modules on each pro-etale site. Each is the explicit statement of its cited node. The strict-limit statement explicitly respects augmentation and connecting maps. The normalized Roos shift statement gives (y,x) mapped to ((-1)^r y,x). On the quotient augmentation the y-coordinate is zero, so this sign fixes it, proving compatibility of the actual completion map with shifts. The general comparison node supplies gamma's specified shift compatibility. Thus c inverse gamma has the canonical shift structure, not merely isomorphic underlying functors.

Step 6 applies the exact-functor-derived-triangulated statement to the exact ordinary functor from step 3. The R-linearity calculation uses the constant-section-preserving coefficient identification of step 2. Naturality of the module-linear comparison maps conjugates scalar multiplication, so the other two functors are R-linear. Shift-compatible natural isomorphisms transport distinguished image triangles with their final arrows. Completeness and reduction bounds transfer through the finite projection identifications already proved, with no Tor-amplitude assertion. All modules are over B_T throughout, never over the constant R-sheaf.

I tested the identity immersion, empty open complement, empty closed subscheme, zero K, n=1 and n=2, and a nonzero shift. Empty sources yield the zero derived category; no dimension or nonemptiness hypothesis is introduced. n=2 uses perfectness over R and never assumes its residue module is perfect over R/t^2. Negative shifts use the integer Roos sign, with the shifted coordinate still zero. Uniform intervals are inclusions and remain unchanged even for zero reductions. None of the arguments uses separatedness beyond the item's existing hypotheses.

For B1–B9 there are no new nodes; all notions and existing source metadata of the item remain intact, all new proof text is single-escaped TeX in JSON, and all appended searches were run by the authorized command. For C1 and C4 I opened every cited node and included its verbatim statement in citations.json; every non-elementary ingredient is named. The only inline deductions are the field/DVR Noetherian observation, constant-section check, scalar conjugation and sign check written above. For C6 I traversed statement and proof dependencies of each proposed citation and found no path back to this item. Off-unit generic tools are explained in split_report.tool_uses; no top-level maintainer tool_uses field was added. For D1–D5 the proof assembles existing facts and creates no restatement nodes. For E1–E7 the hypothesis and edge checks above found no false imported assertion to repair. All six proof steps are shorter than 2000 characters. This is my own direct-delivery review under the dispatched brief, not a claim of an independent second reading.
