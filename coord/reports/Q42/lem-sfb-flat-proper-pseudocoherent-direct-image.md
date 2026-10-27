# Stage-1 report: lem-sfb-flat-proper-pseudocoherent-direct-image

1. Files written: dag/nodes/sec-six-functors-basics/lem-sfb-flat-proper-pseudocoherent-direct-image.json (statement, split, no Mathlib match); citations.json (26 verbatim citations); report.md. No new nodes or Mathlib leaves. searches.jsonl contains the actual search-command results.
2. Attachments: none. The exact blueprint tag has no project Lean hit. Searches by pseudo-coherence and proper direct image found the ordinary-module finite-free complex and Noetherian bounded-coherent perfect-direct-image results; neither states the arbitrary-base, possibly unbounded-below assertion here. No Lean was written or compiled.
3. WANTED: none.
4. No statement dispute or change. The item is exactly the pseudo-coherence conclusion of Stacks 0CSD. Its source proves it by specializing 0CSC. Instead of adding 0CSC as a larger black box and immediately specializing it, this split writes its perfect-approximation argument for the structure-sheaf specialization. The pre-existing perfect approximation, uniform direct-image bound and proper-support perfect-direct-image statements cover the entire argument.
5. Nothing unfinished in this stage-1 split. Its cited existing nodes remain independent tasks according to their own states.

## Source and route

Read perfect.tex, lemma-flat-proper-pseudo-coherent-direct-image-general (0CSD), lemma-base-change-tensor-pseudo-coherent (0CSC), the preceding lemma-base-change-tensor-perfect (0A1H), lemma-quasi-coherence-direct-image (08D5), theorem-approximation (08ES), and its approximation definitions 08EM/08EN. Read cohomology.tex, lemma-restrict-direct-image-open (08FE), definition-pseudo-coherent and lemma-pseudo-coherent-independent-representative (08CB/08CC). Read the project right-derived-functor triangulated implementation at WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/Triangulated.lean: its instances cover unbounded complexes, unlike the bounded-below theorem with a similar name.

Read the chapter and unit records and the latest blueprint's sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The current direct-images proof (3) assembles proper/open direct images on constructible categories. The inherited from.place describes the supporting coherent cohomology branch below that route; this split is a generic structure-sheaf tool there and changes no chapter or unit route. The ancestor tool returns None, which is retained rather than inventing a blueprint ancestor. Searches of the whole DAG by 0CSD, 0CSC, source labels and conceptual keywords, and blueprint_refs searches for pseudo-coherent, tensor-pseudo-coherent and the tags found no duplicate for the item. No candidate new node was created.

Mathlib search results were read, including the two tensor/pseudo-coherence phrasings and the item-specific phrasing. LeanFinder returned ordinary pushforwards, flatness, Tor or light-condensed monoidal facts; LeanSearch returned short-complex tensor exactness, sheaf finite presentation and derived fractions. None states pseudo-coherent derived pushforward. Loogle for PseudoCoherent and the Mathlib grep had no hits. The inherited searches remain in the item, and the actual current queries are appended with their results.

## Not duplicates

No new nodes; therefore no new/existing same-tag pairs.

## Review by Q42

I checked the item against 0CSD with the source open: flatness, properness and finite presentation are all present, and neither Noetherianity nor boundedness below occurs. I also read every cited node's statement, and copied its actual statement into citations.json, rather than borrowing facts from its proof.

Step 1 uses the full derived open-restriction statement lem-pc-restrict-derived-direct-image-open, not the ordinary higher-direct-image version (which only concerns modules and nonnegative degrees). The proper base-change node applies to the affine-open inclusion; qcqs-morphism-permanence supplies finite presentation of the base change; qcqs-over-affine supplies exactly the source hypotheses needed for perfect approximation. Flatness restricts because the stalk rings and their maps are unchanged. Pseudo-coherence restricts by its local definition. Thus the original base is not accidentally assumed quasi-compact.

Step 2 uses pseudo-coherent-qcoh to enter D_QCoh, the uniform truncation-bound node with a quasi-compact affine target, and the perfect approximation node with the now qcqs source. The chosen integer is a=m-N-1, and approximation supplies isomorphisms above a and a surjection at a, exactly as its cited statement says. No lower cohomological bound was inserted.

Step 3 uses TR1 to take the cone and supported-qcoh-triangulated with support all of Y, so its extra support condition is empty. The long exact sequence proves vanishing at degree a as well as above it; surjectivity at a and injectivity at a+1 are both used. I checked the cochain shift sign against the abstract-derived-category definition: C[a-1] has no positive cohomology.

Step 4 applies the proper-support perfect-direct-image theorem with a genuinely perfect P and the bounded complex O_Y[0]. The structure sheaf is finitely presented by its rank-one presentation; stalk flatness over S is exactly flatness of f, with the relative module definition giving the same condition. The closed-support properties node allows using Y itself as a proper closed subset and its empty subset for zero terms. The monoidal-structure definition supplies the derived right unitor, so the result really is perfection of Rf_*P. This avoids using the finite-presentation-module direct-image theorem to claim a result about an arbitrary perfect complex.

Step 5 uses the unbounded triangulated right-derived-functor node for both shifts and the image triangle. Applying the bound to C[a-1] gives vanishing at j>=N+a-1=m-2, stronger than the needed j>=m-1. The two adjacent zero groups in the long exact sequence give the asserted isomorphism at every i>=m. The arithmetic and both endpoint degrees were checked explicitly.

Step 6 uses the local strictly-perfect definition of a perfect object and the derived formulation of m-pseudo-coherence. The composite approximation is an isomorphism even at m and hence supplies its required surjection. The all-m equivalence in the pseudo-coherent definition then gives the conclusion, with affine-local descent already justified in step 1. No extra lemma about coherence over noncoherent rings is used.

Small cases checked: E=0 and empty source/base give zero images and vacuous local conditions; f=id over any ring gives the same complex back. In particular over A=k[x_1,x_2,...], the zero-differential complex with A in each nonpositive degree is pseudo-coherent and unbounded below, and the argument never truncates it below globally. For a finite flat map the relative-flat structure-sheaf specialization has exactly the required hypotheses. A non-quasi-compact base is handled one affine open at a time, so no single uniform N or approximation is required over that entire base.

I checked B--E of delivery-errors: no new-node schema issue, no relabelling into a larger black box, every non-elementary ingredient has a cited node, every citation says the fact used, and no cycle runs through any proposed proof dependency back to the item. Each proof step is under 1000 characters, with no hidden long argument. Off-unit citations are declared generic tools in split_report.tool_uses; none substitutes another chapter's geometric route. No SGA source is used.

The preliminary server review_split passed with zero new nodes. The required delivery dry run and final push follow this signed mathematical review.
