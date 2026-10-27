## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-dg-homotopically-projective-hom-derived.json`: item, split, statement and statement dependencies unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-dg-homotopy-acyclic-localization.json`: statement, unsplit; no direct Mathlib match for modules over an arbitrary DG algebra.
- `dag/nodes/sec-six-functors-basics/lem-sfb-left-orthogonal-localization-hom.json`: statement, Mathlib leaf; exact `CategoryTheory.ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated`, `Mathlib/CategoryTheory/Triangulated/Orthogonal.lean:124–137`.
- `citations.json`: verbatim statement excerpts for every citation in the item's steps.

Attachments: none. Read-only searches of `lean/WeilConjectures/` for the item tag and homotopically-projective/DG-Hom notions found no project declaration stating the item. The ordinary-complex K-projective theorem is not an attachment for arbitrary DG algebras.

WANTED: none.

The live item had an empty proof and searches partly recorded as unavailable without having been run. I replaced that search record with actual logged msearch calls and read their hits. The services were available. The item follows Stacks 09KY's argument under a hypothesis that directly implies the vanishing used there. No statement correction or route departure was needed. No Lean was written, no compiler was run, and no repository or launcher file was changed.

Nothing mathematical remains unfinished in the item's split. The new DG foundation is deliberately a statement-only node, for the next splitting level. Its proof is Stacks 09KJ (the DG homotopy category is triangulated) and 09KW (acyclic modules are a saturated triangulated subcategory and their associated multiplicative system is the quasi-isomorphisms). It is independent of homotopical projectivity and the conclusion about localized Hom, so it does not relocate a clause of this item.

## Blueprint and searches

Read the latest blueprint, `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially paragraph (3). Also read the chapter and unit records. This is a foundational input below the existing coherent-family/Quot/telescope prerequisite chain, specifically the comparison used in step 2 of `lem-sfb-dg-sequential-colimit-triangle`; no unit step is replaced. `tools/blueprint_refs.py ancestor` returns None for this created-node chain, so new nodes preserve the null ancestor and prepend the item to its existing via list. Their places describe the exact supporting subargument.

Searched the whole DAG for 09KY, 09KM, 09KJ, 09KW, 09KX, homotopical projectivity, cone/localization, left orthogonality, fractions, and the exact general Mathlib declaration. Blueprint searches included `homotopically projective`, `homotopy category`, `mapping cone`, `orthogonal`, `representable`, and `localization`. No imported blueprint node states either new lemma. The generic localization hit occurs in search/review/proof material of several nodes, but none of their statements gives its general conclusion; the existing `lem-coef-kprojective-derived-hom-bijection` concerns ordinary cochain complexes, not an arbitrary triangulated category. Existing DG module projective-resolution/model-category results use enhanced mapping objects or projective replacements; this split needs neither that stronger package nor a resolution of P.

Each new node has actual LeanFinder, LeanSearch, Loogle and grep searches copied from `searches.jsonl`. The DG-foundation searches used two semantic phrasings. Read the ordinary-complex candidates in `Mathlib/Algebra/Homology/HomotopyCategory/Acyclic.lean:31–76`, `DerivedCategory/KProjective.lean:43–48`, and the general orthogonality theorem in `CategoryTheory/Triangulated/Orthogonal.lean:74–137`, plus the definition of leftOrthogonal in `ObjectProperty/Orthogonal.lean:41–47`. Ordinary cochain complexes in an abelian category do not give the arbitrary-DG-module triangulation in one specialization. The general orthogonality theorem is an exact leaf: membership in E is its object property, the cone class is trW, and vanishing of all maps into E is its leftOrthogonal hypothesis.

## Not duplicates

lem-sfb-dg-homotopy-acyclic-localization vs lem-sfb-dg-derived-admissible-triangles: the existing statement gives triangulation and graded-split triangles in D(A,d); it does not state that K(A,d) is triangulated or identify its acyclic triangulated subcategory and cone class. Those are the new node's conclusions, needed before applying the Mathlib localization theorem.

lem-sfb-dg-homotopy-acyclic-localization vs lem-sfb-dg-finite-cell-compact: the existing statement concerns compactness of a finite cell module in D(A,d), not K(A,d), its acyclic subcategory, or the cone class of quasi-isomorphisms.

lem-sfb-dg-homotopy-acyclic-localization vs lem-sfb-dg-property-p-resolution: the existing statement constructs a property-(P) resolution with size control; it does not assert any homotopy-category triangulation or identify the acyclic cone class. Its 09KJ citation is incidental and even labels a different auxiliary assertion.

lem-sfb-dg-homotopy-acyclic-localization vs lem-sfb-space-dg-tensor-quasicoherent: the existing statement concerns the quasi-coherence of derived DG tensor on an algebraic space; it does not give the intrinsic DG homotopy category and acyclic cone class.

lem-sfb-left-orthogonal-localization-hom vs lem-coef-kprojective-derived-hom-bijection: the existing statement is for K-projective ordinary cochain complexes in an abelian category; the new exact Mathlib leaf is the general theorem about any triangulated category and its triangulated subcategory.

## Review by Q26

I read Stacks dga.tex Tag 09KY, `lemma-hom-derived`, statement and proof of (1). Its stated input is a property-(P) resolution P -> M, but the comparison for maps out of P uses only vanishing of Hom_K(P,Q[k]) for acyclic Q. The item's homotopical-projectivity hypothesis gives exactly this vanishing. Taking arbitrary P as in the item adds no hidden resolution, boundedness, freeness or countability assumption. I also read 09KM to distinguish the sufficient property-(P) construction in that source from the hypothesis actually used. The original item statement is correct and unchanged.

For the DG foundation I read 09KJ, `proposition-homotopy-category-triangulated`, including the proof reducing TR4 to admissible monomorphisms, and 09KW, `lemma-acyclic`, including its cohomological-kernel argument. Its statement introduces A and the right modules, homotopies, shifts, cones, acyclicity and W_E itself. Right-module shifts keep the action unchanged, which is the Stacks convention; the signed differential and cone formula agree with the original item. This is a substantive structural input, not an elementary identity. The existing derived-category triangle node does not supply the homotopy-category assertion (C4), so I did not cite it for that assertion. The new node has no proof or proof dependencies, as required for the next level.

For the Mathlib leaf I read the full declaration and its proof at Orthogonal.lean:124–137. Its ambient triangulated category and target category have independent universes; it assumes only a triangulated object property, a source left orthogonal to it, and a localization at its cone class. I checked leftOrthogonal's definition directly. Its result is bijectivity of L.map, so it supplies the specified comparison rather than some unrelated bijection. The Mathlib proof includes injectivity by postcomposition with a denominator and surjectivity by lifting a left-fraction numerator; no fractions theorem is being silently assumed by the assembly proof.

Step 1 cites the DG foundation's actual statement: K is triangulated, E is triangulated, and W_E is exactly the quasi-isomorphisms. Since D(A,d) is already defined as localization at those same maps, its functor has the hypothesis of the generic theorem. This is a change of the name of the morphism class, not an unproved comparison between distinct derived categories. All three claims appear in the verbatim citation excerpt.

Step 2 uses only the item's own definitions. For an acyclic E, the Hom complex is acyclic by hypothesis; hence H^0 vanishes, and its stated identification with Hom_K means every map is zero up to homotopy. I explicitly wrote that argument rather than creating a new node for it. Every shift of an acyclic module remains in E, so the source's all-shifts vanishing is covered. This step is elementary.

Step 3 cites the generic leaf's actual conclusion after the hypotheses have been checked in steps 1–2. Its L.map is the original localization map. It uses no hidden property of the proof of either cited node. Both citations are in citations.json with literal substrings of the respective statements; proof_deps is precisely their union. Neither new node depends on this item, so the added edges cannot introduce a return edge through their own dependencies.

I tested the hypotheses and conclusions on P=0, N=0, the zero DG algebra, A concentrated in degree zero, and unbounded modules over a DG algebra with nontrivial graded terms. The zero maps/Hom groups and acyclic cone class behave as asserted; no use of termwise projectivity occurs. For the generic leaf, E={0} reduces to localization at isomorphisms, whereas E=T forces P to be zero (id_P=0), so both extreme subcategories satisfy the claim. The foundation allows acyclic objects which are not contractible; it does not identify acyclicity with being a zero object in K. These checks rule out the main plausible strengthening errors. No source or statement dispute was found. All proof steps are under 2000 characters; none hides an additional comparison lemma or a standard argument. No prohibited SGA source is used.
