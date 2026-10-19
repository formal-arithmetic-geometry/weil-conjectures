# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-coefficient-dual-constructible.json`: existing item split; unchanged statement; no new nodes or Mathlib leaves.
- `dag/units/sk-p-dl-a1-perverse.json`: only `realized` and `realized_by`, repairing the landing's missing-realization failure. The actual perverse-heart theorem realizes the first step; the Fourier t-exact equivalence realizes the second. Both statements together cover the unit statement.
- `citations.json`: 29 verbatim current-node statement quotations, one for every step/use pair.
- `searches.jsonl`: retained previous LeanFinder, LeanSearch, Loogle and Mathlib grep searches; the first five actual logged searches are now recorded on the item. No searches were invented or repeated.

## Attachments

None. I searched the current `lean/WeilConjectures/` for the item tag and dual/constructibility notions. BoundaryDuality's finite-stage theorem assumes an algebraically closed base and finite Tor amplitude, so it does not state this item for arbitrary bounded constructible complexes and fields. No Lean was changed or compiled.

## WANTED

None. BBD and the Stacks sources used here are present.

## Corrections and checks

This repairs the returned landing failure: `unit sk-p-dl-a1-perverse has no realization recorded yet`. I retained the sandbox's proof, report, citations and search history, compared its item and unit with the current read clone, and used the delivery tool to rebase rather than issuing git commands in the shared repository. The initial resumed dry run exited successfully (`a0fa5c6aeb`, not pushed); I made the substantive repairs below before the final validation and push.

The current item has the human's 2026-10-19 affine-space route; I preserve that route and its exact statement. The earlier sandbox's Step 3 use-list had been repaired without updating its bracketed citations. More seriously, `lem-sf-ext-sheaf-constructible` now explicitly assumes a residue ring of a finite extension of Q_l; it cannot supply the arbitrary finite-ring calculation here. I replaced it with the existing general ringed-site finite-free Hom model, finite-free resolution and finite hyper-Ext theorem, with their argument written in Step 4. I also replaced a Tate-twist definition used as a local-constancy theorem by `lem-asd-etale-finite-twist-pullback`. No new lemma was needed. The proof's origin is honestly marked agent: BBD provides context, while this exact arbitrary-ring proof follows the human-mandated route and the cited existing nodes.

The missing unit realization is repaired by its actual key theorems, not by pretending the coefficient lemma proves the perverse-heart statement. I read `thm-a1-curve-perverse-heart` and `thm-a1-fourier-t-exact`: the former states the ordinary cohomology descriptions, bounded t-structure and heart; the latter states t-exactness and the exact Fourier equivalence. The unit statement and both unit proof steps are thereby represented without changing their text or route.

## Review by Q49

I reread the current statement of every item statement dependency and every proof citation, and compared the retained quotations against those statements. For the source context I read BBD's finite-ring discussion in 2.2.12–2.2.13 and its duality/perversity discussion in 4.0; the previous reference to 4.1.1 as if it proved this constructibility calculation was inaccurate (it is affine perverse exactness). I also read Stacks `algebra.tex`, Tag 00LP (`lemma-resolution-by-finite-free`), and `sites-cohomology.tex`, Tags 08JB, 08JC and 08JI (restriction, triangles and the finite-free Hom model). There are no new-node sources to audit. I read the current item/unit/chapter records and followed the human's affine-embedding/purity/direct-image route throughout.

Step 1 uses the actual open-restriction isomorphism for the exceptional adjoint, the exact restriction theorem for internal Hom, and finite constructible stratifications. The affine-chart factorization theorem supplies the finite cover and closed affine-space embeddings, with all schemes separated finite type over k. Finite-cover gluing and the empty case are written out.

Step 2 uses compact-support composition to identify right adjoints, the closed-adjoint existence statement, affine-space adjunction, the finite Tate-twist local-freeness theorem, the closed-support triangle, finite-type direct-image finiteness, Serre closure and the closed inverse-image left inverse. The coefficient exponent is positive and invertible on every scheme involved; k is Noetherian, all spaces are finite type over k, and the complement is an open subscheme of a Noetherian scheme. The twist theorem now explicitly says locally constant of rank one. The closed triangle is stated for the ambient categories and the indicated Ri^!, not just a constructible subcategory. The abelian closed-support equivalence transfers to module sheaves since its canonical maps commute with scalars.

Step 3 uses the hyper-Ext theorem's actual lower bound c-r, truncation/long exact sequences, internal Hom's triangle property and Serre closure. The general finite-coefficient devissage states a finite filtration with locally closed lisse factors; the prime-field-only monodromy lemma is not used. The ambient stratum-Hom statement gives precisely the displayed sheafified adjunction. Compact-support composition identifies its right-adjoint value on omega_T with omega_S, to which the already-proved first assertion applies. This avoids claiming boundedness of the full dual over a ring of infinite global dimension.

Step 4 uses 00LP only after checking Lambda is Noetherian (it is a finite ring) and L_0 finite. The general 08JI node permits a bounded-above resolution and a bounded-below target with arbitrary commutative coefficients. With target F[0] its terms are finite sums of F, so kernels and cokernels give the Ext assertion using Serre closure. The hyper-Ext node explicitly supplies the finite abutment filtrations and half-plane bounds needed to pass to a bounded-below target; no infinite closure of constructibility is assumed. The restriction theorem identifies local calculations, and the surjective-pullback criterion descends constructibility along a finite disjoint union of affine etale charts; these source and target schemes are qcqs.

Step 5 uses the stated truncation triangle and a bounded-below injective resolution to justify the single-degree comparison with tau^{<=q}N. This truncated object is bounded constructible, so the finite-type direct-image theorem applies exactly with the hypotheses already in force. The finite filtration/truncation inductions then use Serre closure. No blanket finiteness theorem for an arbitrary unbounded direct image is asserted.

I checked zero complexes, empty schemes, zero modules, affine dimension zero, identity open and closed immersions, and finite disconnected affine covers. At T=Spec k the conclusion allows an unbounded-above derived dual, as required for nonregular finite rings. Every cited statement is quoted verbatim in citations.json; proof_deps is exactly the union of the uses. Every step is under 2000 characters. No new node duplicates an old node, and no SGA source is used.

## Not duplicates

No new nodes.

## Unfinished work

None in this one-level split. Existing cited nodes remain the downstream items of the project.
