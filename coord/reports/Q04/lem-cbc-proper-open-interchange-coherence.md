# Stage-1 report: lem-cbc-proper-open-interchange-coherence

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-proper-open-interchange-coherence.json`: statement node, split into ten steps; no Mathlib match.
- `citations.json`: 43 exact statement excerpts for every step/node citation.
- `searches.jsonl`: seven searches executed through the required msearch command.
- `report.md`: this report.

No new DAG nodes and no Mathlib leaves. The existing module-termwise exchange theorem supplies the separate comparison calculation hidden inside the former final step.

## Attachments

None. Searched the whole read-only slopmaster2 `WeilConjectures/` for the item id and proper/open interchange terminology. No project declaration there states all the normalization, refinement, vertical/horizontal composition, identity and arbitrary-base-change clauses. The inherited `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence` record is not a closed declaration in the designated slopmaster2 source and is not an attachment.

## Literature

No WANTED sources. Read the local Stacks `more-etale.tex`, especially Tags 0F7B (lemma-shriek-proper-and-open), 0F7C (lemma-shriek-proper-and-open-compose), 0F7D (lemma-shriek-proper-and-open-compose-horizontal), and 0F7F (lemma-shriek-proper-and-open-base-change), including its entire resolution diagram. Checked the support-calculus statements against Tags 0F50, 0F51, 0F55, 0F77 and read `sites-cohomology.tex` Tags 0736 (lemma-base-change-map-flat-case) and 07A7 (remark-base-change) for the module exchange computation. Read the current main-20261015 `thm-cbc-finite-torsion.proof.md`, the unit sk-prop-sf-cbc and its chapter. The split serves the refinement paragraph and final coherence sentence; it changes neither the unit route nor coefficient categories. No SGA source is used.

## What was wrong and what changed

The repository item was marked unsplit despite retaining an earlier proof and review. The former step 8 contained 4214 characters, including an independent proof of the module resolution formula for exchange. I searched the DAG and blueprint before considering extraction and found `lem-weil-pbc-derived-exchange-module-termwise`; its statement gives precisely the computation for constant-ring module sheaves and permits the bounded-below representatives used here. Citing it avoids making a duplicate node. The resolution setup, exchange computation and actual final diagram comparison are now separate steps 8–10. Step 10 displays the map-factor equalities and the transported chain homotopy. Step 9 specifies that its p-side representative incorporates the target identification through beta_k; this ensures the map proved equal is the exact displayed base-change map.

Removed direct-image preservation of injectives from stmt_deps because it is used only in the proof. Preserved the statement, blueprint ancestry, historical review and Lean records. All ten non-elementary steps have fewer than 2000 characters. Their subdivision separates distinct operations; the independent comparison lemma itself is cited as an existing node rather than merely spread across steps.

## Mathlib and duplicate searches

Ran LeanFinder twice with distinct formulations, Loogle for `"shriek"` and `"extensionByZero"`, source grep for `shriek|extensionByZero|properOpenInterchange` and `lowerShriek|extension_by_zero|proper.*interchange`, and LeanSearch for proper/open interchange of derived etale modules. All services answered. Read the returned signatures: they concern ordinary structure-sheaf pushforward composition, restriction along open immersions, and open-immersion section/stalk isomorphisms. None gives extension by zero on the small etale site, its derived proper interchange, or the required coherence equations. Retained the historical search records and appended only the seven queries actually executed in this sandbox.

Searched the entire DAG for module/termwise/resolution exchange and the Stacks tags 0736/07A7, and ran blueprint_refs searches for exchange, proper/open, interchange and module-termwise. The blueprint search returns no equivalent proper/open theorem. The module-termwise statement already exists and is used as a generic tool. Its dependency closure does not reach this item. There are no new-node/existing-node duplicate pairs to list.

## Review by Q04

I read delivery-errors B–E in full and applied them to the actual statements and maps. There are no new statements to test or source places to invent. The original item remains unchanged: finite commutative coefficients, D+ on small etale sites, both proper vertical maps, arbitrary open immersions, no Cartesian assumption on the interchange square, both pasting directions and arbitrary scheme base change. Every quoted citation in citations.json is copied verbatim from its current repository statement.

Step 1 uses the proper-support composition node for equality as subsheaves, its proper/open specializations, and naturality. Its hypotheses are separated locally finite-type morphisms; properness gives these for vertical maps, and local identification with an open subscheme gives them for open immersions. The proper, finite-type and open-immersion definition statements say exactly these things. No quasi-compactness of opens is assumed.

Step 2 uses Grothendieck module-sheaf existence, enough injectives and the D+ injective-representative lemma to choose bounded-below injectives. The extension-by-zero exactness statement guarantees that the complex remains a representative; the open-extended injective proper-acyclicity statement has exactly this non-Cartesian proper/open square and finite ring hypotheses. Leray clause (3) supplies the bounded-below termwise-acyclic calculation; the direct-image definition expressly includes module sheaves and its resolution comparison. Applying the same clause to the source with its identity resolution and to its injective replacement proves p_*t is a quasi-isomorphism. Finite rings are torsion without any residue-characteristic hypothesis.

Step 3 uses the actual Hom-bijection statement for K-injective targets, which permits arbitrary complexes in the ambient derived category. This verifies normalization even for a K-injective representative that is not termwise bounded below: it is homotopy equivalent to the bounded-below injective choice. Additive functors preserve that homotopy, so the same map is obtained. Exactness supplies descent of extension by zero.

Step 4 uses the comparison definition's specified theta and alpha, not an arbitrary isomorphism. The open-restriction and clopen-component statements give the displayed restriction isomorphisms under exactly the hypotheses recorded in the definition; extension-zero base change supplies the specified open comparison. The section identification is identity on the selected component and zero elsewhere. The extension-zero adjunction and exactness of both functors give the derived adjunction already specified in the comparison definition, so equality of the restricted map implies equality with alpha.

Step 5 uses direct-image preservation of injective module sheaves, the same finite-coefficient acyclicity statement and Leray clause (3). Thus r1_*J and p1_*I are valid bounded-below injective representatives and the comparison's image under Rp2_* is computed by the displayed ordinary chain map. The ringed-topoi pushforward composition statement includes its normalization on these representatives; it supplies the exact canonical compositor, not an unnormalized composition isomorphism.

Step 6 uses exactness to compose the horizontal resolutions. Naturality of the already constructed delta and equality on common sections prove the equation. The support-composition statement includes composition of open extensions, giving the stated compositor. Identity cases follow by taking the identity resolution or by localizing the resolution map itself; both types of identity square are covered.

Step 7 uses the support node's pullback restriction and its composition compatibility, the inverse-image exactness statement, the specified extension-zero comparisons and both mate-pasting clauses. It identifies the two sheaf paths inside the same ordinary direct image. Pulling back the support inclusion remains injective because inverse image is exact. The support node explicitly says the comparison is the ordinary one restricted to that subsheaf; no construction is being borrowed from an uncited proof.

Step 8 uses exactness of inverse image and extension by zero, the D+ injective-representative statement and the K-injective Hom bijection. These yield a representative z and the stated homotopy into I1. Its derived class is invertible, so z is a quasi-isomorphism. I did not assume inverse image or extension by zero preserves injectives.

Step 9 uses the existing module-termwise theorem, not the abelian-only theorem. Its source I (respectively J) and target I1 (respectively J1) are K-injective, its replacement z (respectively s) is a quasi-isomorphism, and the projection squares are Cartesian. Its formula is exactly f'_*j after ordinary module exchange. The coefficient-exchange statement specifies the same module mate; the direct-image definition gives the same normalization on bounded-below injectives. The full-subcategory definition permits this bounded-below specialization. The p-side target identification is explicitly beta_k followed by the chosen resolution, so e_p represents the proper exchange followed by Rp1_*beta_k. Nothing is inferred from faithfulness of derived forgetting.

Step 10 substitutes the sheaf equation, moves t and s through the natural transformations and applies p1_* to the chosen homotopy. The displayed expressions have common target p1_*I1. The exact extension-zero comparison supplies the required beta maps, the full-subcategory statement lets equality be read in D+, and the two scheme base-change lemmas ensure the base-changed square again has proper vertical maps and open horizontal maps. The equality is the original item's equation, including its direction and canonical comparisons.

For small cases I checked the zero complex and zero ring, both identity types, the empty open (all relevant extensions vanish), and the refinement r=id case. I also checked a non-Cartesian example: let B=C=D be a disjoint union of two copies of Spec(k), let A be one component, let i and p be identities, and let k and r be that component inclusion. Both vertical maps are proper and both horizontal maps are open, but B times_D C is B rather than A. The comparison identifies r_* with k_!, which agree for this clopen component. In general refinement examples, p can have extra components over the lower open, and the normalization still selects exactly the j1 component. Arbitrary base change requires only the projection squares to be Cartesian, which is how the module-termwise lemma is applied. None of these checks forces a missing Cartesian, quasi-compact-open or invertibility assumption.

The report declares off-unit module/adjunction/resolution facts as generic tools. The new citation is the already existing module-termwise comparison and does not replace a step of the unit route. B: no duplicate, elementary, clause-restating or unstated new node. C: every non-elementary external result is a cited statement; all quotes were checked. D: the comparison, pasting and final homotopy arguments remain in the item. E: coefficients, boundedness, object types and the actual maps have been checked as described above.

## Unfinished work

None in this one-level split. Existing unsplit descendants remain their own items; this delivery neither claims their proofs nor changes them. No Lean was written, no compiler was invoked, and no shared project or launcher file was changed.
