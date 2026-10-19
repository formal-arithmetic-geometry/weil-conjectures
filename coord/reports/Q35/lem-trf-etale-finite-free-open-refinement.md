# Q35 stage-1 delivery: lem-trf-etale-finite-free-open-refinement

## Files written

- dag/nodes/sec-trace-formula/lem-trf-etale-finite-free-open-refinement.json: statement item, six proof steps, status split; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-standard-etale-finite-free-prime-lifts.json: one new statement-only node, status unsplit; no Mathlib match after the logged searches.
- citations.json: one verbatim statement quotation for each of the 18 step/node citations.

The original item statement, created record, unit/chapter binding and blueprint ancestry are retained. No unit realization record is needed: this is a supporting node, not the key statement of sk-i-curve-zero. All written files are in the assigned sandbox.

## Attachments

None. Searches in WeilConjectures by the item tag and by finite/free/flat refinement concepts found no project declaration with the full conclusion. AlgebraicGeometry.Scheme.exists_finite_surjective_refinement_of_etale (WeilConjectures/AlgebraicGeometry/EtaleFiniteRefinement.lean:70) requires a qcqs base and supplies a finite, finitely presented, surjective morphism, with no flatness conclusion. Its affine-source version likewise gives no flatness. These do not attach to this item. The upstream master remains reference material only. Existing Mathlib standard-etale presentation and root-map declarations cover ingredients, not the new algebraic lift theorem.

## WANTED

None: all mathematical sources used are in the repository literature.

## Findings and corrections

The imported item is true as stated, including empty schemes and empty families. Its proof was empty, so this delivery supplies the argument. No STATEMENT-DISPUTED change is needed. The finite locally free definition in the DAG is finite + flat + locally finite presentation; I read Stacks 02KB to verify its equivalence with the finite locally free algebra notion used in 02LI. A merely finite flat cover without finite presentation would be insufficient over arbitrary bases. The construction here uses an actual finite free algebra and its localization.

Stacks 02LI is a remark rather than a detailed proof. I wrote the omitted shrinking argument: the union of the lifts contains the whole fibre, and the closed image of its closed complement can be removed from the base. The proof is accordingly marked proof_origin.by = agent. The chart reduction and algebra lifting follow 02LG and 00UF. No SGA source is used. This is a generic etale-topology refinement tool in the already seeded descent chain below the unit's contracting-correspondence route; no chapter/unit route is replaced.

The new node records the finite free strengthening explicitly supplied by the proof of 00UF, rather than only finite projectivity in its statement. The construction there is a finite free faithfully flat splitting extension obtained by adjoining the roots. It has positive finite rank (for constant monic f, choose R itself); its local maps lift each prescribed prime. This is a substantive algebraic ingredient, not a clause about covering an arbitrary scheme. In particular, I did not introduce the whole 02LG or 02LH conclusion as a new node and then assert 02LI by application.

The standard-etale source's omitted root/prime comparison remains the mathematical content of the new unsplit node. When this node is split later, one can use the existing monic finite free splitting extension, followed by the irreducible-factor argument in residue fields and evaluation at a suitable root. No proof is embedded in the delivered new statement or its proof field.

## Mathlib and duplicate searches

All new searches were run with msearch.py Q35 lem-trf-etale-finite-free-open-refinement and are present in searches.jsonl. Both item and new lemma have LeanFinder, Loogle, grep and LeanSearch records, with a second semantic phrasing. The answers were read. Semantic hits for the item describe the covering topologies or openness; the Loogle hit exists_etale_isCompl_of_quasiFiniteAt was checked at Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:49-54 and has a different conclusion. The new lemma's hits describe StandardEtalePresentation, StandardEtalePair.homEquiv, stability of standard etaleness under localization, or an etale extension splitting a finite algebra. None supplies the claimed finite free algebra and prescribed prime lifts. I read StandardEtalePair and its root-map API in Mathlib/RingTheory/Etale/StandardEtale.lean:49-85. Polynomial.Monic.exists_splits_map, already attached to an existing leaf, only gives a splitting extension; obtaining all the prime lifts is a separate argument, so it is no one-line match. The new records accurately say no match; there were no unavailable services in these new searches. The item's older Q60 searches are preserved.

I searched the entire DAG for the tags 00UF, 00UG, 02LG, 02LH and for standard-etale/finite-flat/free-domination concepts, and ran blueprint_refs.py search for these tags and the phrases standard etale, finite flat and finite locally free. No existing node states 00UF's prescribed-prime lift conclusion. The nearest blueprint ancestor command gave lem-trf-local-term-locality, and the new node's via list is the item's id followed by the retained ancestor chain. Both same_as fields are empty.

## Not duplicates

lem-trf-standard-etale-finite-free-prime-lifts vs lem-weil-pbc-etale-locally-standard: the existing Mathlib leaf produces a standard-etale chart around a prime, while the new node starts with such a chart and produces a finite free algebra with local maps hitting any specified prime.
lem-trf-standard-etale-finite-free-prime-lifts vs lem-weil-pbc-monic-finite-free-splitting-extension: the existing leaf gives a finite free algebra splitting a monic polynomial; it gives no localized maps from the standard-etale algebra and no control of contracted prime ideals.
lem-trf-standard-etale-finite-free-prime-lifts vs lem-trf-etale-finite-free-open-refinement: the item concerns small covering families on arbitrary schemes; the new node is the affine polynomial input, with individual specified-prime lifts and no open-cover or neighbourhood-shrinking conclusion.

No existing node shares the new node's source tag 00UF. These comparisons also explain why obvious-looking candidates do not remove its substantive algebraic content.

## Review by Q35

I read Stacks more-morphisms.tex, labels lemma-dominate-etale-neighbourhood-finite-flat (02LG), lemma-dominate-etale-affine-finite-flat (02LH), and remark-topologies (02LI), and algebra.tex, label lemma-standard-etale-finite-flat-Zariski (00UF), including the preceding locally-standard proof and the following 00UG. I read schemes.tex lemma-basis-affine-opens (01IT), and morphisms.tex lemma-finite-proper (01WN), lemma-finite-quasi-finite (02NU), and lemma-finite-flat (02KB). The three blueprint levels are respected: the chapter and unit are untouched, and this node supplies the generic refinement input in its existing descent ancestry. The unit record already realizes its own key statement through lem-trf-local-term-locality.

For Step 1, I checked the surjectivity definition against the empty family: no point is covered, so only an empty base is allowed. The empty J family then satisfies every conclusion vacuously. The pointwise reduction is written in the step.

For Step 2, I opened all four cited statements. The affine-basis node supplies an affine neighbourhood inside an arbitrary given open, so I choose E inside the preimage of V rather than assuming any intersection of affine opens is affine. The etale definition explicitly has the affine-local characterization, which is preserved on open charts. The locally-standard Mathlib leaf states the localization and the monic polynomial/derivative condition at the selected prime; it applies because E -> V is etale, with no finiteness assumption on S. The basic-open affine-section node supplies both affineness and the localization ring, so D(b) has the exact standard presentation, including its map to V.

For Step 3, the new 00UF node supplies every prime-lift datum actually used, not just a splitting polynomial. Its hypotheses are exactly the monicity and derivative unit produced in Step 2. The same contraction to R holds since t and x both map to s. The finite-free spectrum node states finite, flat and locally finite presentation for arbitrary rings, not just Noetherian ones. The basic-open affine-section theorem and spectrum definition turn the algebra map into a morphism from an actual principal open over V and hence over S; the inverse-image equation on primes gives h_t(t)=x. A ring map merely existing without that contraction control would not suffice, which is why I retained the full prime-lift statement.

For Step 4, I checked the finite-closed-map node's first clause, which says the image of every closed subset is closed, exactly the assertion applied to Z. Its hypotheses hold because Step 3 made pi finite. The complement O contains all fibre points, so s cannot belong to pi(Z). The principal-open basis node allows a principal neighbourhood inside V minus pi(Z); it requires only an affine spectrum and an open subset. I restrict to the actual opens W_s and W_s intersect D(c_t). There is no inference that an arbitrary morphism factors through a subscheme merely because of its set-theoretic image.

For Step 5, I opened each of its four cited statements. The basic-open affine-section theorem gives the localized coordinate rings; the localization-tensor node is a module isomorphism, and I use it only as a module isomorphism. The free-base-change node gives precisely the same finite-index basis after tensoring, which verifies the hypothesis of the finite-free spectrum lemma over R_l. Thus the restricted map has all three properties in the project's definition of finite locally free. Surjectivity of the restriction follows directly by choosing a preimage under pi. The morphism equations are restrictions of the already established equation over S and are written explicitly. The only off-unit non-leaf tool required is the generic finite-free spectrum criterion, declared in split_report.tool_uses.

For Step 6, I checked the finite-fibre clause of the finite-closed-map node, which makes each K_s finite. The size convention ensures the underlying point-index family is small in the specified universe. Every chosen U_s contains s; the open covers and equations were established before assembly. Empty intersection opens can be left in the family because the statement allows empty schemes. No finite subcover of S, separatedness, or affine-intersection theorem is invoked.

I tested the new statement on R=0, f=1 (so B=0), g=0, identity charts f=t with g=1, and a nontrivial finite separable field extension chart. In the first three cases a missing prime makes the lift condition vacuous, and C=R with a one-element basis supplies the conclusion when B=0. In the identity chart the local map is the identity. For a field extension, the splitting algebra supplies roots over each prime; neither the original cover nor the chosen point must have trivial residue extension. This is precisely the role of 00UF. Positive rank avoids accidentally using a zero cover of a nonempty spectrum. The global proof also covers an infinite/non-quasi-compact base because choices are pointwise and only finite fibres are used.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the actual files and open sources: the new node is statement-only and self-contained; notions are defined or cited; source labels/tags and TeX are explicit; no search is invented; no clause is relabelled as a lemma; citations use statements, not proofs; quotations are literal; the only additional argument is written; no source dispute or missing hypothesis was found. Every proof step is shorter than 2000 characters. The single substantive standard-etale prime-lifting argument is already exposed as the new node, and the remainder is construction from the cited statements. The required server dry run completed with OK (not pushed), commit 7d1dd9d758: preflight passed, including the DAG-overlay and split checks. I corrected the report-only source line for the existing Lean refinement theorem to line 70 after reading the numbered file; no mathematics changed.

## Unfinished work

None for this one-level split. The new algebra node deliberately remains unsplit for later stage-1 work. No Lean was written or compiled and no live project, source checkout, literature or launcher file was changed.
