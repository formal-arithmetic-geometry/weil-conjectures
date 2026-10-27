## Worker report

Q101, stage 1, 2026-10-22. Item: lem-sp-integral-local-model-finite-matrix-reduction.

Files written: dag/nodes/sec-smooth-purity/lem-sp-integral-local-model-finite-matrix-reduction.json (statement unchanged; split into eight steps using existing nodes), citations.json, and this report. searches.jsonl retains the actual msearch results. No Lean was written or compiled, and no repository or launcher file was edited.

## New nodes

None. No new Mathlib leaves. The scalar finite-free-resolution and valued-DVR finite-quotient facts already have Mathlib-leaf nodes, and the sheaf tools already have DAG nodes. Introducing fresh copies would duplicate them.

Attachments: none. Searches of lean/WeilConjectures for the blueprint item tag, integral local models, finite matrix reductions and completion/constant exactness found no declaration giving every clause of this item. Existing strict-henselization completion flatness declarations concern other rings and give none of this simultaneous derived matrix statement.

WANTED: none for this split. The existing local-field nodes record their own historical missing-reference notices; no new external arithmetic claim is introduced here.

The imported item has no proof. Its statement is correct as written. The main-20261015 blueprint file det-sp-reduction-tower-normalized gives only the parent statement, not a proof; the eight-step expansion is therefore marked agent-written, with the Stacks source places identified. The item source's tags 093J, 093M, 0AUW and 06YQ are the intended route. No hypothesis on Noetherianity of the scheme, or invertibility of ell on the scheme, was added.

## Blueprint and searches

Read the smooth-purity chapter and sk-def-sp-normalized-towers unit. This split realizes the parent's constructibility paragraph/former step 6, without altering the chapter or unit route. blueprint_refs.py ancestor returned det-sp-reduction-tower-normalized. Whole-blueprint searches for 'finite matrix', 'constant exact' and 'finite constant' produced no alternate blueprint statement of the complete item. In particular sk-def-sfb-constructible defines the local models; it does not prove their derived reductions. DAG searches for 093J, 093M, 0AUW, 06YQ, scalar resolutions and exact constants located the reused tools. The parent's independent review specifically suggested the finite constant resolution and ringed finite-free tensor tools, both read here. I chose the more general scalar resolution plus completion-flatness statements so the ring in the proof is literally the limit B specified in the item, without an extra condensed coefficient identification.

All newly recorded Mathlib queries were run through msearch.py, and their log was read. Loogle and grep gave zero hits. The two LeanFinder phrasings returned ordinary constant/condensed module constructions, Nobeling freeness, and sheaf finite-presentation predicates. LeanSearch returned ordinary constant functors, their adjunctions, a coefficient-reduction tactic and AdicCompletion.transitionMap_comp_reduceModIdeal. I read Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:265-284 (these define local finite presentation, with no derived reduction assertion) and Mathlib/RingTheory/AdicCompletion/Functoriality.lean:65-69 (ordinary scalar reduction naturality). None states the coefficient-valued derived matrix model or all the item's clauses. No unavailable service was recorded as a negative result. The item's inherited Q92 searches were retained unchanged.

## Not duplicates

No new nodes, hence no new/existing pairs. Existing lem-sfb-scalar-finite-free-resolutions and lem-weil-valued-dvr-finite-quotients are cited rather than reproduced. Existing lem-sfb-finite-constant-model-two-term-free-resolution concerns the pulled-back condensed coefficient ring and does not by itself identify the concrete B of this item's statement; its scalar and flatness ingredients are used through existing, more directly applicable nodes.

## Review by Q101

I read Stacks sites-modules.tex at lemma-constant-exact (093J), lemma-completion-flat (093M), and lemma-kernel-finite-locally-constant (093U), sites-cohomology.tex at lemma-bounded-flat-K-flat (06YQ) and lemma-restriction-K-flat (0E8K), and more-algebra.tex at lemma-dedekind-torsion-free-flat (0AUW). The scalar DVR, exact constant realization, flat completion and bounded-free K-flat tools agree with these sources. The blueprint parent statement was read in main-20261015, and the existing parent's reviewed split identifies exactly where this local constructibility calculation is needed. There are no new node statements to check against sources.

Step 1: lem-pc-kflat-resolution states existence of a flat-term K-flat resolution of any complex. lem-sfb-ringed-site-restriction-kflat states both exactness of slice restriction and preservation of K-flatness. lem-sfb-localized-site-tensor-restriction states a natural tensor comparison normalized on pure tensors, sufficient termwise because the coefficient sheaf is in degree zero. lem-pur-derived-change-of-rings computes the result in the coefficient-valued derived category. These statements really supply the locality comparison; I do not infer tensor locality from a definition of restriction. All sites and slices are small in the coefficient universe fixed in the item. No identification of scheme pullback and a newly formed completion is needed.

Step 2: lem-weil-l-adic-extension-integers-dvr states that A is a DVR; lem-weil-pbc-pid-noetherian-normal supplies Noetherianity for its PID. lem-sfb-scalar-finite-free-resolutions supplies an injective finite-free kernel presentation for every finitely presented N, including torsion. lem-weil-pbc-finite-type-constant-exact states exactness of the constant functor; lem-weil-pbc-completed-constant-sheaf-reduction states exactly that extension to the concrete inverse limit is flat/exact for every ideal of a Noetherian A. Apply it with I=(ell), not with a quotient ring assumed flat. Exact restriction and natural tensor restriction are supplied by the two slice tools. Restriction of a constant sheaf to an object is its localized constant sheaf: local constant representatives and covering families are the same on both slices. Restriction of the limit is sectionwise. The basis formulas identify the scalar differential explicitly. This avoids applying a lemma about the condensed coefficient ring without proving agreement with B.

Step 3: lem-sfb-ringed-finite-free-resolution-tensor explicitly states the quasi-isomorphism of the specified augmented two-term resolution, K-flatness, free-basis identifications and the transported matrix differential. lem-pur-derived-change-of-rings gives the comparison in D((B_n)_U), rather than only in D(B_U) after forgetting scalars. Combining with step 1 proves exactly the original restricted derived assertion. No flatness of B_n over B is used.

Step 4: sk-def-sp-coefficient-towers gives the actual quotient maps. lem-pur-sheaf-ring-derived-coefficient-adjunction gives the unit x -> x tensor 1 and the adjunct formula x tensor a -> a g(x). Applying those formulas to the fixed augmentation produces precisely x tensor a -> x tensor q(a). The displayed coefficient equation proves the chain-map condition; quotient-map composition proves compatibility for all pairs and triples of levels. This corrects a possible gap in saying only that comparison 'is natural': the actual transition is calculated.

Step 5: the extending absolute value in def-weil-l-adic-coefficient-extension makes ell nonzero of norm less than one. The factorization and units clauses of lem-weil-l-adic-extension-integers-dvr give ell = w pi^e, e positive. The Mathlib-leaf node lem-weil-valued-dvr-finite-quotients applies at exponent en with its finite residue-field hypothesis supplied by the same DVR node. Thus ramification is allowed and ell is not mistakenly treated as a uniformizer.

Step 6: lem-weil-pbc-finite-type-constant-exact states preservation of both kernels and cokernels for any scalar linear map on any small site. def-weil-abstract-derived-category explicitly gives H^r = ker(d^r)/im(d^(r-1)) and factorization of cohomology through localization. These suffice to compute cohomology of this two-term complex; no general claim that completion commutes with cohomology was taken from them.

Step 7 is elementary and written out: a kernel is a subset and a cokernel is a quotient of finite sets, and every finite module M over the finite ring A_n admits a surjection A_n^M -> M whose kernel is finite. Taking all elements of that kernel gives a finite presentation. No hidden use of a coherence or Noetherian theorem remains.

Step 8 is elementary from the explicit local constant identifications, the generators in step 7, and def-weil-proetale-locally-constant-sheaf, whose statement is exactly the cover-wise constant-module definition. It retains the given cover for all n. I tested N=0 (take both ranks zero), a free N (take u=0), and N=A/(pi) in a ramified extension: the matrix [pi] modulo ell^n gives both a nonzero kernel and cokernel and shows why degree -1 must not be discarded. I also checked identity transitions, all m<=n, L=0 and empty S. No argument uses points of the site or Noetherianity of S.

All eight steps have fewer than 2000 characters. The non-elementary steps cite the statements they use, rather than their proofs. The tool_uses requested in split_report are generic scalar or ringed-site tools absent from this unit, and preserve its local-matrix route. The top-level maintainer tool_uses field was not written. proof_deps equals the union of uses; all 21 citation entries are verbatim statements of their cited nodes. I checked each cited node has no dependency path back to this item. There is no statement correction, circular step, new clause-node, hollow definition or SGA citation.

Nothing remains mathematically unfinished in the split; server dry-run and delivery results are recorded below when available.

## Validation

Initial required deliver.py --no-push completed with exit 0 and preflight passed at 0aed023e128. I then refined each step source to name the precise source actually used (slice restriction, K-flat computation, normalized adjunction, and elementary assembly separately); no mathematical statement or proof argument changed. A final dry run is required on these final files before pushing.
