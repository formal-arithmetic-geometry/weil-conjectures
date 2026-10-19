## Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-site-hypercover-derived-descent.json`: item, statement unchanged, five proof steps, status split; Mathlib searches found no match.
- `dag/nodes/sec-trace-formula/lem-trf-site-hypercover-injective-sections.json`: new statement-only lemma, arbitrary-site injective section exactness (01GW); no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-site-augmentation-acyclic-cech.json`: new statement-only lemma, Cech computation for componentwise acyclic total-site sheaves (0D79/0D7A); no Mathlib match.
- `citations.json`: one verbatim statement quotation for each step/node citation. `searches.jsonl` contains the actual msearch.py results. `prepare.py` is sandbox-only preparation code, not part of the delivery.

Attachments: none. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact id, blueprint tag, hypercover/cohomological-descent terminology, and the concepts of each new node. Only finite 0/1-hypercover sheaf gluing and related site-generation code appeared, not a declaration of this assertion or either new lemma. The item has no Lean audit declaration to read. No master sorry declaration is used as evidence of completion.

WANTED: none. All proof sources are available in the repository.

What was wrong or incomplete: the imported item had no proof, and the easiest nearby DAG section-exactness inputs require a subcanonical site, whereas the item does not. I did not add subcanonicality. Instead I used the arbitrary-site assertion of Stacks 01GW, whose proof uses sheafified free representables. Likewise the existing total-image spectral-sequence node is specifically for simplicial scheme etale topoi, so it cannot be applied to arbitrary slice sites. The new general acyclic-computation lemma removes that gap. The unused direct dependency on `def-weil-pbc-topos` was removed; the statement already introduces topoi through its geometric-morphism definition dependency. No target, unit route, or statement was changed.

Nothing remains unfinished in the one-level split. The new lemmas intentionally remain unsplit, with statements only. This delivery creates two new nodes and zero Mathlib leaves. There are no proof steps longer than 2000 characters (all five are below 1000).

## Proof route and searches

I read `spaces-simplicial.tex`, section-hypercovering and 0D8N, then its references 0D8L (the over-object reduction), and 0D8G (`lemma-hypercovering-descent-bounded-abelian`), particularly its first paragraph and bounded case. The proof uses injective localization and the alternating-face computation, followed by Leray. The split retains this route: it evaluates the injective Cech complex on each test object to get sheaf exactness from 01GW instead of introducing a separate internal-Hom construction. This is the same injective/free-resolution argument in 01GW and 0D8G, and avoids any point or subcanonical-site assumption.

For the first new node I read `hypercovering.tex` 01GW (`lemma-injective-trivial-cech`) and 01GE (`lemma-acyclic-hypercover-sheaves`), including their proofs. A representable simplicial object is a singleton semi-representable object in each degree; the matching covering-sieve hypotheses give the required local surjections on representable presheaves after sheafification. These are precisely the hypotheses in 01GE. The section complex and augmentation in 01GW are exactly the statement of the new node. For the second new node I read `spaces-simplicial.tex` 0D79 and 0D7A with the injective double-complex proof, and `sites.tex` 09W9 (`lemma-relocalize-given-fibre-products`), especially (3), for the explicit evaluation formula. Resolving the total sheaf gives rows exact in positive degree and columns computing the component derived images. If these component groups vanish above zero, the comparison of the degree-zero column cycles with the total complex is a quasi-isomorphism. The row comparison also identifies H^0 with the same kernel b_*F, so the comparison cannot introduce a different degree-zero map.

Before creating the nodes I searched all `dag/nodes` by hypercover/injective/augmentation/Cech concepts and by 01GE, 01GW, 0D79, 0D7A, 0D88, 03F3 and 09W9; I opened the close statements (the differences are recorded below). I ran `tools/blueprint_refs.py ancestor` for the item and searched the whole blueprint for hypercover, hypercover derived descent, injective localization, Leray, augmentation, Cech, injective hypercover, hypercover injective sections, and simplicial augmentation acyclic. There was no equivalent blueprint node. Both new nodes carry the retained nearest blueprint ancestor `lem-trf-local-term-locality` and the full via chain with this item prepended; their `same_as` fields and the item's field are empty after the searches.

For each new node, five searches were actually run through msearch.py: leanfinder twice with different phrasings, loogle, grep, and leansearch. The item has another five actual searches in this run; the Q55 searches already in its base record were retained. Every result was read, and the exact query/result log was transcribed into mathlib_searches. Loogle found no results. Grep found only comments about exact multiforks for 0/1-hypercovers for the injective-section query and no hits for the other two queries. Semantic hits were Mayer-Vietoris short complexes, ordinary injective resolutions, local-surjection properties, Cech-nerve constructions, generic right-derived functors, generic derived-unit formulas, and OneHypercover gluing. None states either full node or specializes to it in one line. No service failure was represented as a no-match result.

## Review by Q118

I checked the item against 0D8N: C is a small site, finite limits are stronger than the source's fibre products, all matching maps locally cover, and only D+ is claimed. The source's unbounded statement was not used. In particular no torsion, scheme, etale, splitness, or subcanonicality assumption enters. The unit, not merely an arbitrary isomorphism of the two objects, is the conclusion. The chapter/unit binding and inherited normal-cone/Orgogozo ancestry are unchanged, and no unit realization record belongs to this auxiliary item.

Step 1 cites the site definition for induced topology and pullback stability. The slice identification and the matching base-change identification are written by their objects and universal properties, rather than asserted as a theorem. The n=0 matching object becomes T. This step is elementary: compatible families on a test object are the same on both sides, and the covering sieve is the pullback of the assumed one. No non-small index category or infinite matching limit occurs.

Step 2 cites `lem-weil-pbc-site-restriction-injectives` for exactly its stated exact left adjoint to restriction. That node does not literally state injective preservation; the proof writes the short extension-and-adjunction argument using the definition in `def-sp-injective-resolutions`. The general site enough-injectives node states abelian sheaves have enough injectives, so it applies to all slices and the total site, unlike the scheme-etale existence node. Clause 1 of `lemma-weil-pbc-leray-acyclicity` states injective objects are acyclic for a left exact additive functor; localization direct image is such a functor because it is the abelian right adjoint to exact inverse image. The new Cech-computation node explicitly gives the acyclic comparison and the evaluation formula needed here. Its statement is quoted in full in citations.json; the proof does not mine its unsupplied proof.

Step 3 cites the new section-exactness lemma on the site D itself, with W=T and the pulled-back diagram from step 1. The coefficient I is injective on D, exactly as required: I am not assuming I(U_p) is an injective group or that arbitrary inverse image preserves injectives. Every evaluation of the augmented Cech sheaf complex is therefore exact. The passage from sectionwise exactness to sheaf exactness is immediate from kernels and sheafified images and is spelled out. The Cech-computation statement supplies both the degree-zero kernel and the actual derived comparison. Its degree-zero normalization makes the underived restriction augmentation the underived unit. This proves the required acyclicity for b^{-1}I without turning that entire derived descent assertion into a new lemma.

Step 4 applies `lem-weil-pbc-ring-sheaves-grothendieck` only to the integer sheaf on the base and total small sites. Abelian sheaves and integer modules have the same objects and maps, since the integer action is forced by addition. The site enough-injectives and bounded-below representative theorems then have their exact hypotheses: the latter states a lower cohomological bound gives an injective complex with the same lower degree bound. The total site's size is verified explicitly; no unbounded resolution is needed. Exactness of inverse image is the defining finite-limit preservation of the geometric morphism together with preservation of colimits by its left adjoint, giving exactness on abelian sheaves.

Step 5 cites clause 3 of `lemma-weil-pbc-leray-acyclicity`, now with the Grothendieck hypothesis verified, for the natural cohomology comparison on the bounded-below termwise-acyclic complex. `lem-weil-pbc-right-derived-plus-injective` supplies the canonical resolution comparison and its isomorphism on injectives, rather than an unspecified choice of derived functor. The ordinary derived unit is the chain-level adjoint of the injective-replacement map, displayed explicitly. Naturality of the underived unit makes its first arrow a chain map, and step 3 makes that arrow an isomorphism degree by degree. Thus every cohomology map of the specified composite is invertible. The derived-category definition is cited only for complexes, quasi-isomorphisms, and localization.

I checked each new node against B1--B9: all objects and hypotheses are stated, notions have definition dependencies, no proof is included, the sources use tags and labels, and search and blueprint records are present. Each is a smaller independent ingredient: the first concerns only ordinary sections with injective coefficients, and the second assumes no hypercover at all and concludes a Cech computation for componentwise acyclic coefficients. Neither restates the item's derived-unit clause. I checked C1/C4 by opening every cited statement and writing a verbatim quote for each use, and corrected the second new node to include the localization evaluation formula explicitly, supported by 09W9. No argument is supplied just by a source reference. No SGA reference is used.

Small cases: for the identity constant hypercover, the alternating complex has maps 0,id,0,id,..., and both lemmas give exactly the expected H^0 and zero positive cohomology. A zero injective sheaf gives a zero augmented sequence. An empty representable cover, possible when the topology covers the initial object by the empty family, forces the relevant sheaf sections to be zero, so exactness still holds. No nonempty choice of a cover or point is made. For the second lemma, even a sheaf with noninvertible transition maps is allowed: its total direct image is the kernel of the first two face maps, rather than an assumed cartesian value. On a trivial site this is the usual cosimplicial abelian-group complex. Negative lower bounds in D+ are permitted; the injective representation and Leray are applied with that same lower bound and no finite upper bound. These checks exposed no statement dispute.

## Not duplicates

lem-trf-site-hypercover-injective-sections vs lem-weil-pbc-ringed-hypercover-finite-local-cones: the existing conclusion constructs finite local cone functions on original simplex labels; it does not assert exactness of an injective section complex.

lem-trf-site-hypercover-injective-sections vs lem-weil-pbc-ringed-hypercover-injective-augmentation: the existing module statement requires a subcanonical site. The new lemma works on arbitrary sites, as the item requires; specializing coefficients to integers cannot remove subcanonicality.

lem-trf-site-hypercover-injective-sections vs lem-weil-pbc-proetale-hypercover-injective-row: the existing statement is specifically on the scheme pro-etale site with the data and augmentation of its definition nodes; it is not an arbitrary-site theorem.

lem-trf-site-hypercover-injective-sections vs lem-weil-pbc-proetale-hypercover-local-lifting: the existing assertion constructs local matching lifts on a pro-etale site, and has no injective-coefficient exactness conclusion.

lem-trf-site-hypercover-injective-sections vs lem-weil-pbc-hypercover-injective-module-positive: the existing clause uses def-weil-pbc-finite-split-hypercover (a finite split etale hypercover of a qcqs scheme); it is not exactness on an arbitrary site or on an arbitrary nonsplit hypercover.

lem-trf-site-hypercover-injective-sections vs lem-weil-pbc-hypercover-free-module-positive: the existing clause concerns a sheafified free resolution on a finite split etale hypercover of a qcqs scheme. The new lemma concerns injective section complexes on arbitrary sites, with no splitness or scheme assumption.

lem-trf-site-hypercover-injective-sections vs lem-weil-pbc-hypercover-injective-module-zero: the existing clause uses def-weil-pbc-finite-split-hypercover (a finite split etale hypercover of a qcqs scheme); it is not exactness on an arbitrary site or on an arbitrary nonsplit hypercover.

lem-trf-site-hypercover-injective-sections vs lem-weil-pbc-hypercover-free-abelian-positive: the existing clause concerns a sheafified free resolution on a finite split etale hypercover of a qcqs scheme. The new lemma concerns injective section complexes on arbitrary sites, with no splitness or scheme assumption.

lem-trf-site-hypercover-injective-sections vs lem-weil-pbc-grothendieck-injective-hypercover-row: the existing assertion assumes a qcqs scheme and a finite split etale hypercover. The new lemma permits arbitrary sites and nonsplit representable hypercovers.

lem-trf-site-hypercover-injective-sections vs lem-weil-pbc-hypercover-injective-abelian-zero: the existing clause uses def-weil-pbc-finite-split-hypercover (a finite split etale hypercover of a qcqs scheme); it is not exactness on an arbitrary site or on an arbitrary nonsplit hypercover.

lem-trf-site-hypercover-injective-sections vs lem-weil-pbc-hypercover-injective-abelian-positive: the existing clause uses def-weil-pbc-finite-split-hypercover (a finite split etale hypercover of a qcqs scheme); it is not exactness on an arbitrary site or on an arbitrary nonsplit hypercover.

lem-trf-site-hypercover-injective-sections vs lem-sc-ringed-hypercover-injective-augmentation-ring: the existing noncommutative-module statement also assumes a subcanonical precoverage-generated topology. The new abelian statement has no such assumption.

lem-trf-site-hypercover-injective-sections vs lem-weil-pbc-hypercover-free-abelian-zero: the existing clause concerns a sheafified free resolution on a finite split etale hypercover of a qcqs scheme. The new lemma concerns injective section complexes on arbitrary sites, with no splitness or scheme assumption.

lem-trf-site-hypercover-injective-sections vs lem-weil-pbc-hypercover-free-module-zero: the existing clause concerns a sheafified free resolution on a finite split etale hypercover of a qcqs scheme. The new lemma concerns injective section complexes on arbitrary sites, with no splitness or scheme assumption.

lem-trf-site-augmentation-acyclic-cech vs lem-trf-simplicial-derived-image-spectral-sequence: the existing statement is for simplicial scheme etale topoi with constant module coefficients. It does not give the general arbitrary-site Cech comparison for a componentwise acyclic sheaf.

lem-trf-site-augmentation-acyclic-cech vs lem-trf-total-site-derived-components: the existing theorem computes components of a morphism between two simplicial total sites, not the derived augmentation into a single base site.

lem-trf-site-augmentation-acyclic-cech vs lem-trf-simplicial-proper-exchange: the existing theorem is proper base-change exchange for torsion scheme-etale complexes; it does not state this arbitrary-site, non-hypercover acyclic computation.

## Validation

The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q118 lem-trf-site-hypercover-derived-descent --no-push` exited 0 and printed `OK (not pushed)` at commit `1b126b6525`: server preflight passed, including the required DAG and split checks. No compiler or build tool was run, and no live project file was changed.
