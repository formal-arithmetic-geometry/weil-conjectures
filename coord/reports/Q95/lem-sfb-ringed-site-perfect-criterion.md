# Stage-1 delivery: lem-sfb-ringed-site-perfect-criterion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-perfect-criterion.json: statement, split; statement unchanged; five proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-approximation-opcycle.json: new statement-only node, unsplit; no Mathlib match. This is flatness of a specific cokernel of a bounded flat approximation, with no perfectness conclusion or finite-presentation assumption.
- citations.json: thirteen exact statement quotations, covering every step/node pair.
- report.md and searches.jsonl: this report and the actual search log; search-result-*.txt retain the new searches' full outputs.

## Attachments

None. Searched WeilConjectures for the item tag, ringed-site perfectness, pseudo-coherence, and approximation/opcycle statements. The scheme and ring pseudo-coherent finite-Tor criteria and finite-constant-coefficient pro-etale results do not state this arbitrary-ringed-site criterion. In particular RingPseudoCoherentFiniteTorPerfect.lean is about modules over a single ring. No Lean or compiler was run.

## Wanted literature

None. Read sites-cohomology.tex, Tags 08FT (definition-pseudo-coherent and the following representative-independence discussion), 08FZ (definition-tor-amplitude), 08G1 (lemma-tor-amplitude), 08G5 (definition-perfect), 08G7 (lemma-perfect-precise), 08G8 (lemma-perfect), and 08FG (lemma-flat-tor-zero). Read sites-modules.tex, Tag 08FD (lemma-flat-locally-finite-presentation), statement and proof. Tag/label correspondence was checked in tags/tags.

## Findings and corrections

The item statement is correct and unchanged. It does not require quasi-compactness, a Noetherian or coherent structure sheaf, enough points, or a global cohomological bound. The inherited unit/chapter records and the newest blueprint/latest unit and direct-images proof were read; this supporting criterion serves the inherited direct-image prerequisites, rather than replacing a unit-level argument. Its inherited blueprint ancestor is null, as confirmed by blueprint_refs.py ancestor; its full via chain is retained. No unit record is edited: this is not the unit's key statement.

The converse cannot use lem-sf-site-perfect-tor-window, lem-sf-site-perfect-lower-model, or lem-sf-site-perfect-opcycles-retract: these already assume a strictly perfect representative of K, which is what the converse must construct. The new cutoff lemma instead starts with a finite approximation, not a quasi-isomorphic perfect representative. Its flat terms need not be finite or projective and its conclusion concerns one module sheaf, not perfectness.

I expanded the finite-presentation step into an explicit matrix. I kept the original finite upper bound of the approximating complex: the last display in 08G7 is written ending at b, but brutal truncation at b would not automatically be legitimate. The criterion only needs a finite upper bound, so no extra upper-end-shortening result is needed. Good lower truncation is identified with K by its adjunction, not by pretending that the original approximation is a quasi-isomorphism.

## Unfinished

The one new supporting lemma is deliberately unsplit, as required for a one-level stage-1 split. Its complete argument is retained below for its next worker. No part of the assigned split is left unwritten.

## Argument retained for lem-sfb-flat-approximation-opcycle

This argument is not placed inside the new statement-only node. It is the low-degree argument of 08G7 without its finiteness assumptions. Set R=ker(P^(a-1) -> P^a). Testing K's Tor bound on the structure sheaf gives H^j(K)=0 below a. In a cone triangle P -> K -> C -> P[1], the cohomology long exact sequence, the lower bound on P, and the comparison isomorphisms give H^(a-2)(C)=R and zero cohomology in every other degree. Therefore C is isomorphic in the derived category to R[2-a], with boundary to P[1] induced by the kernel inclusion. Tensor this triangle with any module sheaf N. A bounded flat P is K-flat and computes P tensor^L N by the ordinary tensor complex. For the single sheaf R, derived tensor is supported in nonpositive degrees and H^0(R tensor^L N)=R tensor N. The tensor triangle's cohomology sequence and H^(a-1)(K tensor^L N)=0 now give exactness at the middle of

    R tensor N -> P^(a-1) tensor N -> P^a tensor N.

The first arrow is the tensor of the actual kernel inclusion, not an arbitrary map having the same source. This is the compatibility needed in the argument. Put S=im(d^(a-1)). Right exactness of tensor identifies S tensor N with the cokernel of R tensor N -> P^(a-1) tensor N. The displayed exactness therefore makes S tensor N -> P^a tensor N injective. Since P^a is flat, the Tor sequence of 0 -> S -> P^a -> Q -> 0 gives Tor_1(Q,N)=0 for every N. By 08FG, Q is flat. In a later split, the tensor-triangle compatibility, leading-degree derived-tensor computation, and Tor sequence must be cited as supporting statements rather than silently treated as definitions. They are not facts used separately by the assigned item's proof, which cites the new lemma's conclusion only.

## Mathlib and duplicate searches

Ran the required msearch.py commands for this item and the new lemma; the log records each exact query, service status, hit names and digest. Read all new outputs. Item hits are cohomological bounds and finite presentations, with no perfect/pseudo-coherent criterion. The new lemma's first semantic query returned DerivedCategory fraction factorizations and support bounds, not flatness. Its second returned ordinary module equational criteria and exact tensor characterizations, which do not specialize in one line to sheaves on an arbitrary ringed site. LeanSearch returned short-complex homology and cokernel constructions. Loogle's flat/cokernel query and the new grep were empty. Thus the new lemma is not a Mathlib leaf. The item itself also has a second semantic phrasing (LeanSearch) and a grep; inherited search records were retained.

Searched the entire DAG for the source tags, flat cokernels, approximation and opcycles; searched blueprint_refs.py for perfect, strictly perfect, 08G7, flat cokernel, approximation and opcycle. The blueprint's scheme perfect-complex definition does not state the new generic flatness lemma. The arbitrary-site flat-opcycle criterion already present is about universal tensor exactness of a flat complex itself. Here P need not even be exact in degree a-1: P=O placed in degree a-1, K=0 is allowed, so that criterion cannot be applied directly to P. Its tensor kernel must instead be compared to the cone as above.

## Not duplicates
- lem-sfb-flat-approximation-opcycle vs lem-sf-site-perfect-opcycles-retract-transport: the existing statement transports a given finite-free retraction between iterated slices; the new lemma establishes flatness from a derived approximation and supplies no retraction.
- lem-sfb-flat-approximation-opcycle vs lem-sf-site-perfect-tor-window: the existing statement assumes K is already locally perfect and constructs representatives in a prescribed interval; the new lemma assumes only a bounded flat approximation and proves flatness of one cokernel.
- lem-sfb-flat-approximation-opcycle vs lem-sf-site-finite-projective-lift: the existing statement locally lifts maps from finite free sheaves across epimorphisms; the new lemma is an opcycle-flatness theorem for derived approximations.
- lem-sfb-flat-approximation-opcycle vs lem-sf-site-perfect-upper-model: the existing statement starts from a perfect object/representative and shortens its degree bounds; the new lemma starts from a non-isomorphic approximation and does not construct a perfect model.
- lem-sfb-flat-approximation-opcycle vs lem-sf-site-finite-projective-section: the existing statement locally splits an epimorphism onto a finite-free retract; the new lemma does not assume a finite-free retract and proves flatness instead.
- lem-sfb-flat-approximation-opcycle vs lem-sf-site-perfect-restriction-exact: the existing statement is an exactness/additivity assertion for slice restriction functors; the new lemma is a flat-cokernel assertion requiring a derived approximation and a Tor bound.
- lem-sfb-flat-approximation-opcycle vs lem-sf-site-perfect-restriction-additive: the existing statement is an exactness/additivity assertion for slice restriction functors; the new lemma is a flat-cokernel assertion requiring a derived approximation and a Tor bound.
- lem-sfb-flat-approximation-opcycle vs lem-sf-site-perfect-overmap-additive: the existing statement is an exactness/additivity assertion for slice restriction functors; the new lemma is a flat-cokernel assertion requiring a derived approximation and a Tor bound.
- lem-sfb-flat-approximation-opcycle vs lem-sf-site-perfect-overmap-comp: the existing statement concerns composition of slice restriction functors; the new lemma concerns a derived approximation on a fixed ringed site.
- lem-sfb-flat-approximation-opcycle vs lem-sf-site-perfect-opcycles-retract: the existing statement assumes P is a strict-perfect representative of K and concludes a local finite-free retraction; the new lemma allows a comparison failing in degree a-1 and concludes only flatness, with no finiteness assumptions.
- lem-sfb-flat-approximation-opcycle vs lem-sf-site-perfect-overmap-exact: the existing statement is an exactness/additivity assertion for slice restriction functors; the new lemma is a flat-cokernel assertion requiring a derived approximation and a Tor bound.
- lem-sfb-flat-approximation-opcycle vs lem-sf-site-perfect-lower-model: the existing statement starts from a perfect object/representative and shortens its degree bounds; the new lemma starts from a non-isomorphic approximation and does not construct a perfect model.
- lem-sfb-flat-approximation-opcycle vs lem-sf-site-perfect-derived-restriction-iso: the existing statement identifies two derived restriction constructions; the new lemma is about flatness of a cokernel on a fixed site.
- lem-sfb-flat-approximation-opcycle vs lem-sf-site-perfect-package-map: the existing statement transports already given finite-free retraction packages through additive functors; the new lemma assumes no package and concludes flatness only.
- lem-sfb-flat-approximation-opcycle vs lem-trf-two-term-perfect-tor-window: the existing statement is a two-term perfect-model criterion for schemes; the new lemma allows arbitrary ringed sites and flat approximation terms without any perfectness conclusion.

## Review by Q95

I read the actual Stacks proof of 08G8 in both directions and the 08G7 argument it invokes, rather than using the existence of those tags as a proof. I checked the inherited statement's local quantifiers against 08FT, 08FZ and 08G5; they intentionally allow bounds to vary with the covering member. I also read 08FD and 08FG for the new lemma and the final splitting. No SGA source is used.

In Step 1, I opened lem-pc-sheaf-modules-tensor-closed: its statement supplies additivity and the structure sheaf as tensor unit. The finite-summand flatness argument is then a retract of a finite sum of exact sequences. I opened lem-sp-ringed-site-tor-flat-model: implication (2) to (1) accepts these bounded flat sheaves on any ringed site, without points or constructibility. The same local derived isomorphism gives every pseudo-coherent cutoff, not just one chosen cutoff.

In Step 2, I opened def-pur-localized-ringed-site, whose statement supplies both covering families and relocalization, and lem-pur-site-restriction-module-adjunction-exact, whose conclusion includes exact restriction. Thus every cohomology comparison can be restricted legitimately. I opened lem-sf-site-tor-interval-restriction: it tests against every module sheaf on the slice, so I am not merely restricting global test sheaves. The brutal lower truncation preserves cohomology from degree a upward, which is exactly what the new lemma needs; it need not preserve degree a-1. Tensor additivity is cited again for flatness of its finite-free-summand terms.

In Step 3 I checked every hypothesis of lem-sfb-flat-approximation-opcycle: boundedness, flat terms, vanishing below a-1, universal Tor interval, and comparison isomorphisms for j>=a. The conclusion is precisely flatness of Q, and no part of the item's perfectness claim is being imported from it. Its source was read through the cone and Tor_1 arguments. I checked the matrix presenting Q: p_1 is onto P^(a-1), and 1-e kills exactly the complement of P^a in the finite free sheaf. This establishes finite presentation without assuming the structure sheaf coherent.

In Step 4 I opened def-sbc-standard-tstructure-derived-category and clause (1) of lem-weil-heart-short-exact-triangles. They give the standard t-structure and the left-adjoint property used to factor the comparison through the good lower truncation. I opened lem-weil-pbc-derived-plus-iso-on-cohomology; it has a bounded-below hypothesis, which both K and T satisfy locally with the explicit lower bound a. This is a local use of D-plus inside the unbounded category, not a global boundedness assumption. The cohomology computation of the good truncation shows the induced map is an isomorphism in all degrees.

In Step 5 I opened lem-sf-site-flat-fp-finite-retract. Its hypotheses are flatness and the local finite-presentation sequence, both established in Step 3, and its conclusion is the exact finite-free splitting required for the new lowest term. Exact restriction and relocalization cited here preserve the good truncation and identify the composite covers. I explicitly avoided a brute upper truncation at b, which would require an additional splitting argument. All steps are under 2000 characters; none conceals an additional long comparison argument. The new cutoff lemma is statement-only and its argument is retained above for the next stage-1 worker.

Edge cases checked: the zero object uses interval [0,0]; all ranks can be zero, and the matrix still presents the zero cokernel correctly. When a=b, the construction remains valid and does not assume the higher terms vanish brutally at b. The formula for C=R[2-a] has R in cohomological degree a-2; this checks the shift sign. Over Z, the complex [Z --2--> Z] in degrees [-1,0] cannot satisfy the lemma's a=0 Tor-bound hypothesis for K=Z/2, as its tensor with Z/2 has degree -1 homology; removing that hypothesis would give the false flatness conclusion for Z/2. If comparison isomorphisms are omitted, the same P with K=0 gives a false conclusion. On a disjoint union with unbounded local degree intervals, the argument stays on individual covering members and introduces no uniform bound. Flatness is tested by sheaves and Tor, never by existence of stalks. Source/duplicate checks and thirteen verbatim citation entries were verified, including the new statement's quotation.
