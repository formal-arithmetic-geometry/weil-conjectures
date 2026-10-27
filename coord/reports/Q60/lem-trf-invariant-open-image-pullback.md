## Files written

- dag/nodes/sec-trace-formula/lem-trf-invariant-open-image-pullback.json: item split in six steps; statement unchanged. The complete statement is not a Mathlib leaf, although all non-elementary geometric inputs already have DAG nodes that are Mathlib leaves.
- citations.json: statement quotations for every step/node pair.
- searches.jsonl: actual msearch.py outputs retained; the item retains its imported searches and adds the five Q60 searches.

No new nodes; no new Mathlib leaves. No Lean written or compiled. Only the sandbox was written.

## Attachments

None. Searches under lean/WeilConjectures for the blueprint tag and invariant-open notions found EffectiveDescent/Gluing.lean, especially mem_of_apply_eq_apply and isEffective_restrict_of_le, but these concern restrictions of an existing effective descent datum, not every clause of this item under precisely its hypotheses. InvariantOpenEffectiveDescent.lean concerns gluing an invariant cover. Neither gives an attachment for the full item.

## WANTED

None.

## Problems found and repaired

The item was statement-only, without a proof. Its mathematical statement is correct, including arbitrary opens without quasi-compactness and arbitrary schemes without finite-presentation or quasi-affineness hypotheses. No statement correction or route change was needed. The potential pitfall is treating scheme fibre-product points as pairs: Step 1 instead uses the existing general image formula. Another potential gap is claiming that an isomorphism of underlying schemes preserves the given descent datum: Step 6 writes the actual equality and cancels a monomorphism.

## Searches and reuse

Read GOAL.md, SETUP.md's three levels, the worker brief, stages/1-dag.md, delivery-errors B through E, and the unit and chapter records. Blueprint ancestor is lem-trf-local-term-locality, through the existing geometric quotient-presentation branch; the item serves the final paragraph of Stacks 0247 within that branch. The chapter and unit were not changed.

Searched the whole DAG statements and Mathlib-match fields for flat quasi-compact quotient maps, kernel-pair invariance, fibre-product points, open factorization and open-immersion monicity. Opened each of the reused nodes. Blueprint-wide searches for quotient topology, open immersion, invariant open, fibre product points and fpqc open produced no blueprint node stating this full item. The general DAG search found the existing open-subscheme-fpqc-descent node and the stronger subset image formula, so neither was recreated. The proof exposes saturation and openness directly rather than hiding the whole conclusion behind that compatible-open descent theorem.

Ran msearch.py with leanfinder (two distinct mathematical formulations), leansearch, loogle and grep; read the hits and the relevant Mathlib source. Flat.isQuotientMap_of_surjective is already carried by lem-weil-pbc-flat-qc-surjective-quotient-map. Scheme.image_preimage_eq_of_isPullback is already carried by lem-weil-pbc-base-change-image. IsOpenImmersion.lift, lift_fac and lift_uniq are already carried by lem-weil-pbc-morphism-factors-through-open-subscheme. IsOpenImmersion.mono is already carried by lem-weil-pbc-open-immersion-monomorphism. The search hit descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact' descends a property of a given morphism; it does not construct the descended open and its datum from this item's input. Thus it does not state the complete item.

## Not duplicates

No new nodes. Existing compatible-open descent, quotient-map, fibre-product image, open-factorization and monomorphism statements were reused, not duplicated.

## Review by Q60

I read descent.tex, Tag 0247 (lemma-quasi-affine), especially the final paragraph constructing the descended open inside the affine descended ambient scheme. That paragraph uses only flatness, quasi-compactness and surjectivity of the projection to descend the stable open. The extra quasi-affineness and quasi-compactness appearing earlier construct the ambient model; our item assumes that model and therefore correctly does not assume them for V. I also read descent.tex Tag 03N0 (lemma-open-fpqc-covering) as a consistency check, morphisms.tex Tag 02JY (lemma-fpqc-quotient-topology), schemes.tex Tag 01HI (lemma-restrict-map-to-opens), and schemes.tex Tag 01L7 (lemma-immersions-monomorphisms). The Tag 01S1 subset image formula and its Mathlib realization were checked against the existing base-change-image node. The relevant Mathlib source includes PullbackCarrier.lean:306 and :420, Morphisms/Flat.lean:124, and OpenImmersion.lean:546, :701, :705, :708, :767. These are reading locations, not newly claimed attachments.

Step 1 uses exactly lem-weil-pbc-base-change-image's formula for arbitrary subsets C. Taking f=g=q and C=O supplies r1(r0^{-1}(O))=q^{-1}(q(O)); invariance then proves containment in O. The converse is a set identity. This proves saturation and membership equivalence without needing an uncited assertion that a tensor product of residue fields is nonzero.

Step 2 uses def-weil-open-immersion for openness of the range O and lem-weil-pbc-flat-qc-surjective-quotient-map for the open-preimage equivalence. Its three morphism hypotheses are exactly the item's assumptions. Uniqueness among arbitrary subsets uses actual surjectivity; the pointwise definition is recorded in the item's statement dependencies. No assertion that q is an open map is used.

Step 3 takes the unique open factorization from lem-weil-pbc-morphism-factors-through-open-subscheme, whose statement explicitly applies to an arbitrary scheme morphism with image in an open subscheme. The range condition is qj(V)=q(O)=U. It imposes no finite-type or separation assumption.

Step 4 is the short universal-property argument, using that same factorization, def-weil-open-immersion's identification with the open image, monicity from lem-weil-pbc-open-immersion-monomorphism, and def-pc-fibre-product's full existence/uniqueness property. Equality after i is enough to prove the second projection equality. This checks the actual square and canonical morphism, not just equality of underlying point sets.

Step 5 uses the fibre-product universal property twice to construct inverse morphisms explicitly. The hypotheses on theta ensure compatibility over B and identify the A-projection. Both composites are identities by the indicated projections and cancellation through j. The schemes A and B can be arbitrary and the morphism A to B need not itself be fpqc; only the given projection q is required to be fpqc.

Step 6 uses def-pd-descent-datum for the overlap isomorphism and the canonical datum of a base-change object, def-pc-fibre-product for the two overlap identifications, and the monomorphism statement for i. It proves directly that k is monic from its U and A2 projections, rather than silently citing base-change stability of open immersions. Intertwining with the ambient canonical datum gives k phi=k, so the transported phi is exactly the identity under those identifications. No compatibility theorem is hidden behind the word transport: the two maps and the cancellation equation are specified.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the files: no new nodes, no circular dependencies through the item, no proof clauses moved to statement-only copies, and no new definition chosen by existence. The cited nodes' statements are quoted verbatim in citations.json. Elementary steps 4-6 consist of universal-property constructions and cancellation with all needed facts cited; each is under 2000 characters. No source assumes normality, separatedness, noetherianity, a finite index set or finite presentation in the portions used. Small cases checked: V empty gives U empty and the empty pullback; V=W gives U=W' by surjectivity; q an identity recovers the same open; disconnected schemes and non-injective fpqc maps are covered by saturation rather than injectivity; empty W' forces empty W. The datum argument applies also to empty overlap schemes, where monicity and the universal property still hold. No counterexample or statement dispute was found.

## Unfinished

None in this one-level split. The required dry run and push are performed after this report is written.
