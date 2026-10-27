## Worker report

Stage 1, Q90, 2026-10-22. Item: lem-zl-lisse-short-complex-common-stage-exactness. Direct delivery, with the worker's own review below and the maintainer's independent review still to follow.

### Files written

- dag/nodes/sec-deligne-laumon-general/lem-zl-lisse-short-complex-common-stage-exactness.json: split into seven steps. The existing fibre-detection theorem proves exactness in the common-stage heart; finite distinguished-triangle witnesses, their isomorphisms and inverse equations descend alongside the prescribed arrows. No new nodes or Mathlib leaves.
- citations.json: 23 per-step citation records, every excerpt checked verbatim against the current cited statement.
- report.md: this report. searches.jsonl is the genuine msearch log; prepare.py is a sandbox-only preparation script and is not a delivery node.

### Attachments

None. The upstream project search for the exact blueprint tag returned no declaration. Searches for lisse exactness and common-stage coefficient exactness found lisse Weil abelian-subcategory and curve representation results, notably WeilSheaf/LisseAbelian.lean and EtaleCohomology/Purity/RealSheaves/LisseRepAbelian.lean. These do not state simultaneous exact descent of prescribed finite models and relations, so none is claimed as an attachment.

### Literature wanted

None. No WANTED document is needed for this split.

### What was wrong and what changed

The imported item had no proof. Its final Weil sentence omitted an explicit requirement that the arrows satisfy intertwining equations. I corrected only that sentence, as detailed under Source error. The proof does not infer t-exactness from triangulated exactness alone: it separately checks the sf/PBC comparison against both definitions of the standard halves. It also does not claim that arbitrary pro-etale points detect arbitrary sheaves or that a particular integral lattice sequence is exact.

### Unfinished work

None for this stage-1 split. The dependencies retain their current live states; this delivery makes no claim that they have finished Lean proofs.

## Source error

STATEMENT-DISPUTED: the unqualified final Weil clause is false when 'carries Weil maps' means only vertex isomorphisms. Take Y_0 = Spec(F_q), let A be the rank-one constant rational lisse sheaf, and use the short exact sequence 0 -> A --id--> A -> 0 -> 0. Give its source Weil operator 1 and its middle Weil operator 2, and give the zero object its unique invertible operator. All vertex Weil maps have inverses and the underlying sequence is exact on every normalized fibre. But the identity arrow is not Weil-equivariant: id composed with 1 is 1, whereas 2 composed with id is 2. This remains false over every coefficient extension (including ell = 2, since the coefficients are rational). Include just the vertex inverse identities among the prescribed equations to see that every other original hypothesis is satisfied.

Original clause: 'If the diagram carries Weil maps and their inverses, the resulting sequences consist of Weil-equivariant maps with those same realized Weil structures.'

Corrected clause: 'If the diagram carries Weil maps and their inverses, with the Weil-equivariance equations for its arrows included among the prescribed equations, the resulting sequences consist of Weil-equivariant maps with those same realized Weil structures.'

This makes explicit the intended input in the parent lem-zl-classical-weil-filtration-heart-transport and the current blueprint thm-zl-real-mixed-by-curves.proof.md paragraph 1: its filtration is already a filtration of Weil sheaves, hence its inclusions and quotients intertwine the vertex Weil structures. The definition def-weil-weil-sheaf-complex states precisely that equation. No hypothesis or conclusion about the underlying short complexes, prescribed models, equations, comparison, or finite coefficient fields was changed. The same-source lemma remains applicable to the parent's Weil-equivariant input.

## Sources and searches

I read the chapter and unit records, the current main-20261015 proof of thm-zl-real-mixed-by-curves (paragraph 1, the actual finite Weil filtration), and the parent heart-transport and finite-diagram realization statements. The item supplies the exactness and common-coefficient-stage portion of that route; it does not change the chapter or unit argument.

For the coefficient mathematics I read Bhatt--Scholze, The pro-etale topology for schemes, Corollary 6.8.5 and its proof (kernels and cokernels of lisse rational maps), Definition 6.8.6 and Lemma 6.8.7 (constructible kernels and cokernels), and Proposition 6.8.14(1),(2) (finite coefficient categories and raw rational realization). I also read BBD, Faisceaux pervers, Theorem 1.3.6 and the admissible-heart argument, together with the blueprint statement and proof of lem-weil-heart-short-exact-triangles(4). Stacks Tag 0145 is derived.tex, definition-triangulated-category: TR1 is exactly closure under triangle isomorphism. The finite witness descent is an explicit agent assembly from the project's Hom-colimit and common-stage triangle definitions, rather than a verbatim claim attributed to Bhatt--Scholze. Accordingly proof_origin.by is agent.

The actual Q90 msearch runs cover leanfinder, leansearch, loogle and grep, with a second natural-language phrasing. The first Loogle pattern contained an unknown identifier; that response is recorded honestly and a second valid query was run. Its hit CategoryTheory.ShortComplex.shortExact_iff_of_iso was read at Mathlib/Algebra/Homology/ShortComplex/ShortExact.lean:60 (and the defining ShortExact and shortExact_of_iso at lines 35 and 45). It transports short exactness across an isomorphism; it does not give this item's lisse realization, normalized geometric fibre criterion or finite coefficient descent. The other semantic hits concern abstract homological functors, filtered colimits in a single category, condensed-module exactness and module adic completion. They do not supply this statement. The grep hits for 'lisse' were metric 'isSeparated' substrings; the second grep exposed the genuine abstract ShortExact declarations. No service failure was recorded as absence. Existing upstream search records were retained; the new records are exactly the Q90 queries in searches.jsonl, including the subdirectory in the recorded result where appropriate.

Whole-DAG title/concept searches for exact fibres, common stages, finite diagrams and coefficient exactness, plus tools/blueprint_refs.py searches 'lisse exact', 'finite diagram' and 'short exact', found the needed existing statements. In particular lem-dl-a1-constructible-fibres-exact states the normalized common-stage exactness test outright, while def-weil-algebraically-closed-coefficients supplies the raw sf Hom colimits and finite-stage triangles. Thus no new general 'common-stage short exact descent' node was created merely to restate the assembly. I did not use the PBC scheme-limit lemma lem-weil-pbc-finite-diagram-lift-of-models, whose objects are schemes rather than coefficient complexes, nor assume det-sp-qbar-finite-descent's additional six-functor assertions.

## Not duplicates

No new nodes. There are consequently no new/existing same-tag pairs. Blueprint same_as stays empty: the stronger simultaneous prescribed-model assertion is not a restatement of the fibre-detection theorem alone or the abstract finite-diagram colimit assertion alone.

## Review by Q90

I checked the split against delivery-errors B--E with the actual node statements open. This is a direct worker self-review, not a claim of an additional independent reader.

Step 1 uses only lem-dl-a1-constructible-fibres-exact, whose statement explicitly identifies its fibres with derived point pullback and the normalized point-fibre functor and asserts the short-exact iff criterion. The finite-field, prime, separated finite-type scheme, geometric base change and constructible-heart hypotheses match verbatim here. Although the item is lisse, no assertion about all pro-etale sheaves or ordinary discrete stalk conservativity is being used. This existing general result is enough for the first conclusion, and no duplicate lisse-only detection node is warranted.

Step 2 uses lem-weil-heart-short-exact-triangles(4) in its forward direction to obtain the connecting maps, then def-weil-algebraically-closed-coefficients to obtain a finite triangle and its triangle isomorphism. I checked that this definition really specifies distinguished triangles via isomorphisms from finite-stage triangles, rather than merely describing their objects. Each triangle contributes three component isomorphisms and inverses and exactly the three commuting-square equations written in the step. This is finite auxiliary data, not an extra assumption on exactness.

Step 3 uses the equality-of-representatives rule actually present in def-weil-algebraically-closed-coefficients. It first picks fields for the maps and then, separately, fields witnessing their finitely many equations; taking a common upper field is legitimate in its directed finite-extension index set. In particular no transition Hom map is asserted injective. All vertex objects remain the scalar extensions of the prescribed models. The definitions in def-weil-weil-sheaf-complex specify the actual stagewise Frobenius pullback action, and lem-tw-lisse-rational-realization states naturality and finite scalar compatibility of that pullback identification. They therefore permit the Weil equations to be treated as equations between finitely many actual stagewise arrows. This step is elementary finite-colimit bookkeeping after those cited interfaces, not a new descent theorem hidden behind the word 'descends'.

Step 4 uses lem-weil-scalar-extension-exact-triangulated to retain each finite distinguished triangle, and the TR1 clause of def-weil-triangulated-category to replace its vertices by the prescribed objects using the now-realized inverse identities and three squares. The last square uses the shifted first component and the specified shift comparisons, so this is an isomorphism of triangles, not merely an isomorphism of three unrelated objects. The truncation/scalar commutation of prop-constructible-truncations retains the heart condition; the scalar-compatible lisse equivalence of lem-tw-lisse-rational-realization retains lissity. With these hypotheses in force, the reverse direction of lem-weil-heart-short-exact-triangles(4) gives finite-stage heart exactness.

Step 5 uses the identity-on-integral-objects and pure-tensor map formulas of lem-fd-rational-coefficient-category-comparison, not only the word 'exact'. I compared def-weil-constructible-standard-tstructure with prop-weil-pbc-integral-tstructure: both integral halves test the same ambient cohomology vanishing. Its rational halves and those of prop-weil-localized-tstructure are the isomorphism closures of those halves. Hence J and its inverse preserve the halves directly, and its triangle preservation plus lem-weil-heart-short-exact-triangles(4) really yields exactness in the PBC heart. The geometric situation is precisely the separated finite-type geometric base change singled out in the comparison's final paragraph; ell is invertible. There is no unproved identification of unrelated coefficient categories.

Step 6 again uses the exact triangulated transition theorem and scalar-compatible truncations, followed by the same heart-triangle criterion, for arbitrary finite L/E. Lissity and compatibility of towers use the explicit lem-tw-lisse-rational-realization clause; the PBC assertion uses the specified scalar compatibility of lem-fd-rational-coefficient-category-comparison. Original relations and inverse identities remain equations because extension is a functor. No integral map or lattice exactness is introduced here.

Step 7 uses exactly the Weil-pair morphism equation of def-weil-weil-sheaf-complex and the normalized pullback realization of lem-tw-lisse-rational-realization. The counterexample above is what forced me to write the missing equivariance assumption explicitly. The stagewise theta and inverse maps represent the original common-stage maps, rather than arbitrarily chosen new Weil structures.

I tested the zero short complex, the empty family, the empty diagram, disconnected schemes and the empty scheme. All steps are component-free finite bookkeeping. With no short complexes no triangle witnesses are added; with no data at all Q_l is an admissible field. A point is never selected in the proof, so the empty scheme does not introduce a missing base-point hypothesis. The rank-one point example also checks rational denominators and shows why imposing lattice exactness or integral invariance would be extraneous.

For B, no new statement-only or Mathlib node is needed, every preserved definition is cited, and the item's TeX remains singly escaped. For C, all non-elementary facts are cited statements, all 23 excerpts are verbatim, proof_deps is the union of uses, and no source proof is treated as an unstated strengthened theorem. For D, the proof contains the finite list of triangle squares and equality witnesses rather than delegating the whole item to a new node. For E, the sf/PBC heart check is explicit, Frobenius pullbacks use the given normalization, and the missing equivariance hypothesis is corrected and documented. Every proof step is below 2000 characters; the longest is the finite map/equality bookkeeping step, which hides no separate comparison lemma.

The off-unit tools are declared in split_report.tool_uses: normalized fibre exactness, the generic heart-triangle criterion, exact scalar transitions, compatible standard truncations, normalized lisse realization, the sf/PBC comparison, and the two PBC standard-half descriptions. They supply general coefficient/category facts; none replaces the actual Weil-filtration argument of sk-i-dl-general-real.
