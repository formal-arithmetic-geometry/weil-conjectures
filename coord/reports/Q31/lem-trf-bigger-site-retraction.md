# Worker report — Q31 — lem-trf-bigger-site-retraction

## Files written

- dag/nodes/sec-trace-formula/lem-trf-bigger-site-retraction.json — statement, split; original statement and all hypotheses retained. The full theorem is not a Mathlib leaf.
- dag/nodes/sec-trace-formula/lem-trf-adjoint-triple-unit-counit.json — statement, Mathlib leaf: CategoryTheory.Adjunction.Triple.isIso_unit_iff_isIso_counit, Mathlib/CategoryTheory/Adjunction/Triple.lean:66–75. One new node, one Mathlib leaf, no new unsplit nodes.
- citations.json — verbatim statement passages for each citation in each of the seven proof steps.
- searches.jsonl — actual msearch.py results. Initial search commands for potential Kan-extension nodes were exploratory and those draft nodes were removed. The final adjoint-triple searches initially had the candidate id in the command's item position, so they were repeated with the correct delivery item to put the authentic records in this sandbox's log. No search is invented, and no discarded candidate's records occur in the final node.

## Attachments

None. Searching the project WeilConjectures/ trees for the blueprint tag and for bigger-site, retraction, and continuous/cocontinuous full faithfulness found no declaration proving the complete general-site item. The sorry-free open-immersion instances in SixFunctors/Etale/LowerShriek/OpenImmersion/FullyFaithful.lean prove only a special scheme-theoretic situation, not this item. The new generic lemma is Mathlib's theorem, so it is a Mathlib leaf rather than a project attachment.

## WANTED

None. The Stacks sites.tex source and the exact Mathlib source are available and were read.

## Corrections and route

There is no statement dispute or correction: the item agrees with Sites 00XU, with the canonical isomorphisms also specified in 00XT. Replacing literal equality of terminal objects by their specified isomorphism does not change the terminal-object hypothesis.

The imported empty proof is replaced by seven steps. The finite-limit implication of final objects and pullbacks is written out. The generic 00X6 tool gives L ⊣ R and left exactness, so f is genuinely a morphism of sites. The existing 00XR node gives R ⊣ g_* with a compatible-family formula and the counit. Full faithfulness explicitly makes that counit invertible. Rather than claiming that presheaf evaluation survives sheafification without proof, the exact general adjoint-triple theorem gives the canonical unit for the actual sheafified L. The final two steps identify the composite geometric morphism and invert the actual map on Hom sets. This is a change below the unit's node level allowed by SETUP.md: sk-i-curve-zero's contraction/normal-cone route is preserved. No SGA source is cited.

The two off-unit tools are declared in split_report.tool_uses: lem-weil-pbc-left-exact-site-inverse-image-tensor is the generic finite-limit site theorem of 00X6, of which only its set-sheaf clauses are used; lem-weil-pbc-continuous-cocontinuous-topos-adjunction supplies the generic 00XR adjunction and canonical compatible-family formulas. Neither replaces any contraction or normal-cone step of the unit. The Mathlib adjoint-triple leaf is a generic tool in the item's own unit.

## Not duplicates

lem-trf-adjoint-triple-unit-counit vs lem-trf-bigger-site-retraction: the new node concerns arbitrary categories and two supplied adjunctions; it proves neither existence of a site morphism nor the fully faithful site's invertible counit. It is only the formal implication used after the item's explicit computation.

lem-trf-adjoint-triple-unit-counit vs lem-trf-big-small-etale-exact-retraction: the existing node is a scheme-specific exactness and unit theorem on abelian big/small etale sheaves. It does not state the general unit/counit equivalence for arbitrary adjoint triples.

lem-trf-adjoint-triple-unit-counit vs lem-trf-adjoint-mate: the existing node compares adjunctions of exact functors on triangulated categories using a supplied isomorphism of left adjoints. The new node instead concerns two consecutive adjunctions on arbitrary categories and the invertibility of their unit and counit.

lem-trf-adjoint-triple-unit-counit vs lem-sfb-finite-extension-by-zero-fully-faithful: the existing node states full faithfulness for a particular open-immersion functor; it does not give a theorem for arbitrary adjoint triples.

The full DAG and blueprint were searched for 00XU, 00XT, 00XR, 00X6, bigger site, adjoint triple, unit counit, isIso_unit_iff_isIso_counit and fully faithful Kan extension. blueprint_refs.py found no equal blueprint statement for the new generic lemma or the item. The two potential Kan-evaluation draft nodes were removed: they are unnecessary because the right-adjoint family calculation is elementary and the generic triple theorem directly addresses the sheafified adjunction.

## What remains unfinished

Nothing in the stage-1 split. No Lean was written or compiled. The item is not the key node of sk-i-curve-zero, so its realized fields require no edit. The maintainer's independent review is the delivery's next stage.

## Review by Q31

I read sites.tex Tag 00XU (lemma-bigger-site), its entire proof, Tag 00XT (lemma-back-and-forth) and its proof, Tag 00XR (lemma-when-shriek) and its proof, and Tag 00X6 (proposition-get-morphism) with the following remark. I matched the tags to sites labels in tags/tags. Hypotheses (a)–(e) of the item are exactly the source hypotheses; an isomorphism u(e_C) ≅ e_D suffices because terminality is invariant under isomorphism. There is no dropped final-object, pullback, continuity or cocontinuity condition, and full faithfulness is the actual bijectivity of Hom maps. I also read the recorded source and proof route of the ancestor lem-trf-local-term-locality, the chapter record, and both steps of sk-i-curve-zero. This generic site lemma serves the existing small/big etale comparison in the ancestor's normal-cone route; it changes none of the chapter or unit steps.

For the new node I read Mathlib/CategoryTheory/Adjunction/Triple.lean:54–75. Lines 54–60 define a triple as exactly two adjunctions F ⊣ G and G ⊣ H, and lines 66–75 prove the iff for their actual unit and counit. Thus the node's arbitrary categories, directions of F,G,H, and transformation domains all agree literally with the theorem. It is an exact leaf, not a multi-step construction requiring a bridge between site conventions. Its statement introduces every functor and both transformations and carries no proof sketch. I inspected the actual msearch.py hits; all four final searches succeeded, so none is mislabeled unavailable. The broader site searches found separate Kan-extension/adjunction results, and the dense-subsite equivalence requires cover-density absent here. I read CoverLifting.lean:275–367, Pullback.lean:36–100 and DenseSubsite/SheafEquiv.lean:97–108 to check that they do not already state the full item.

Step 1 uses exactly clause (3) of def-weil-pbc-sites-and-cohomology to read off preservation of coverings. Its finite-limit argument is elementary: products are pullbacks over the final object and equalizers are pullbacks along diagonals. Hypotheses (d),(e) preserve these constructions; no existence of all finite limits in D is assumed separately.

Step 2 uses the statement, not the proof, of lem-weil-pbc-left-exact-site-inverse-image-tensor: it explicitly supplies the sheafified left Kan extension, adjunction to restriction, and finite-limit and colimit preservation. I checked the finite-limit and cover hypotheses against step 1. def-weil-pbc-sites-and-cohomology(3) defines the site morphism from precisely this exactness, and def-trf-geometric-morphism defines the geometric adjoint pair. def-weil-size-convention permits the common small presentations and containing sheaf universe; no non-small indexing category is introduced.

Step 3 uses exactly the statement of lem-weil-pbc-continuous-cocontinuous-topos-adjunction, which I opened in full. Its L is our R and its R is our g_*, so there is no reversal of the adjunction direction. Its statement explicitly asserts the geometric morphism, supplies the compatible families with their equations and restriction maps, and identifies the canonical counit by evaluation at (X,id). The only hypotheses are continuity and cocontinuity, already (a),(b), with no extra density or local-fullness assumption.

Step 4 cites that same statement solely for these explicit family and counit formulas. The inverse is proved, not imported: write ψ=u(a) uniquely, send t to F(a)t, verify compatibility by functoriality, and recover every family using its equation for a:A→X. I corrected the naturality sentence while reviewing so that it explicitly checks h:X'→X: the coordinate at a:A→X' after restriction is F(h∘a)t=F(a)F(h)t. The inverse is natural in F by a natural transformation's defining square. This is the elementary evaluation argument in the first paragraph of 00XT and does not use the source's harder plus-construction argument or leave a sheafification identification implicit.

Step 5 cites the exact Mathlib leaf only after the actual adjoint triple has been established. Its counit is the one computed in steps 3–4, so it yields the canonical unit of the actual sheafified L ⊣ R, not merely an invertible map between the same objects. This matters for the big/small etale citer. Step 6 uses the composition and 2-morphism clauses in the statement of def-trf-geometric-morphism; the direct image of f∘g is Rg_*, and the proved counit supplies the required invertible 2-morphism. Step 7 derives full faithfulness by giving the inverse to a↦L(a) and checking it using unit naturality and the adjunction bijection already established. It invokes no additional lemma. Every external non-elementary fact is therefore in a cited statement, and citations.json quotes those exact statements verbatim.

I checked delivery-errors B–E against the actual files: the only new node is statement-only, self-contained, correctly typed TeX and an exact located Mathlib leaf; its blueprint ancestor/via adds this item in front of the existing via list. It is neither a clause of the site theorem nor a renamed input and has no dependencies that can cycle back to the item. The statement-dependency list of the item is unchanged and still defines every site notion used there. proof_deps is the union of uses. None of the seven steps exceeds 2000 characters, and none hides an additional geometric lemma. No definition node is being used as if it proved a non-elementary comparison.

For edge cases I tested u=id (all maps become identity), a one-object terminal site (the family is uniquely determined by its sole coordinate), empty covering families (no point or nonempty-cover argument occurs), and sheaves with empty section sets (the inverse functions are defined without choosing a section). The finite-limit hypotheses preclude an actually empty source category; I did not manufacture objects in one. For the new abstract triple theorem I checked the identity triple and the triple from the one-object category A to the poset B={0<1}, with F selecting 0, G:B→A the unique functor, and H selecting 1: F ⊣ G ⊣ H and both transformations on A are identities. Full faithfulness is used only at the coordinate computation and cannot be weakened to faithfulness alone. These checks use no stalk conservativity and make no identification of set sheaves with abelian or condensed coefficients.

Dry-run repair: the first server preflight reported that the new leaf cited no definition node. I opened def-nagata-category and added it as the definition of the categories in the new statement, with that exact statement dependency; I also spelled out both natural Hom-set bijections to define the adjunctions inline. The unit/counit equivalence itself is unchanged, so its exact Mathlib match and the recorded searches still apply. I updated the step-5 verbatim quote accordingly. The earlier standalone server check_dag passed with no introduced finding.
