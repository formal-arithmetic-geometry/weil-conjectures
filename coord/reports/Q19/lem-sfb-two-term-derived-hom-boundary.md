# Stage-1 report: lem-sfb-two-term-derived-hom-boundary

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-two-term-derived-hom-boundary.json: statement, split using existing nodes only; full item is not a Mathlib leaf.
- citations.json: every cited statement, verbatim, for every proof step.
- report.md: this report. searches.jsonl retains the interrupted attempt's searches and the additional executed searches. write_split.py is a sandbox-only reproduction aid.

There are zero new nodes and zero new Mathlib leaves. The statement, statement dependencies, inherited provenance, import fields, and blueprint prerequisite chain are retained.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for two-term, derived Hom, boundary, cokernel and Hom combinations. MappingConeCoimage and truncation modules are related constructions, not declarations of every clause of this item. No exact project theorem was found. Mathlib declarations are reused through their existing DAG nodes.

## WANTED

None. The sources used are present in literature/stacks-project/derived.tex.

## Issues found and repaired

The item had no proof. Its source correctly names 0149 and 06XS, but citing those tags alone would leave the cone signs, Hom identification, and naturality unproved. I supplied those arguments. No STATEMENT-DISPUTED issue was found, and no hypothesis was added. The null blueprint ancestor is inherited: blueprint_refs.py ancestor reports None for this prerequisite chain; I preserve it rather than invent an ancestor. The exact inherited place already names det-thm-sf-ctf-stability-direct-images (3) and its deformation prerequisites. I read the current latest blueprint's sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md; the auxiliary homological calculation changes neither route nor unit statement. The archived DAG unit and current blueprint differ, so the current blueprint was used as instructed. The item is not the unit key node and no unit record is changed.

An important sign is explicit in step 1: the stored cone convention has boundary -q, so its rotation initially has second arrow -q and third arrow -d[1]. Negating the third vertex yields the triangle with exactly q and d[1]. This avoids relying on an unstated convention for the boundary. The Ext-zero clause is proved using the actual chain map to the cokernel, not merely an abstract isomorphism of groups.

## Not duplicates

No new nodes were created. Searches of the whole DAG by tags 0149, 06XS, 0154 and 011J, by Hom exactness, single fully faithful, standard t-structure, truncation triangles, and termwise-split connecting morphisms found the existing leaves used here. blueprint_refs.py searches for homological, negative-exts and two-term found no equivalent blueprint node. No clause was moved into a restatement node. In particular a new general negative-Ext lemma is unnecessary: the standard t-structure node and its defining orthogonality already supply the vanishing in two lines.

## Unfinished work

None in this split. No Lean was written and no compiler, Lake, global build, or local DAG/preflight checker was run. The server dry run is the required mechanical validation, followed by direct delivery.

## Review by Q19

I read derived.tex at lemma-representable-homological (Tag 0149), definition-cone (014E), the distinguished cone conventions (014Q), the rotation axiom (0145), lemma-derived-canonical-delta-functor (0152) and lemma-negative-exts (06XS). I also read the item and every statement it cites, along with the Mathlib declarations recorded for the reused leaves. There is no new-node source to review.

Step 1 uses def-weil-abstract-derived-category for the explicit matrix cone and its boundary -p, and def-weil-triangulated-category for TR2 and invariance under isomorphism. These statements actually contain those clauses. The two-term cone identification is immediate degree by degree and the three signs are written, so this step is elementary application of those definitions rather than a hidden cone-comparison lemma.

Step 2 uses clause (ii), not merely the title, of lem-weil-pbc-hom-out-of-triangle-exact: a map from the third vertex killed by the second factors through the third arrow. Here its third vertex is M[1], its target G[1], and its last arrow d[1]. The shift is an additive autoequivalence by def-weil-triangulated-category, so k unshifts to a map F[0] to G[0]. The fully faithful embedding node identifies precisely those maps with morphisms F to G, with no injectivity assumption. For the reverse implication I did not silently assume that qd is zero as a chain map: d[1]q is generally nonzero as a chain map, and the component h^0=1_F is its explicit contracting homotopy. The derived-category node explicitly allows passage through the homotopy category, so this homotopy gives zero after localization.

Step 3 uses abelianness for the ordinary image/kernel/cokernel sequence. Its complex kernel L has degree zero im(d), not ker(d), and its degree -1 differential is the epic coimage-to-image factorization. Both displayed rows are exact in every abelian category. The statement of lem-weil-pbc-complex-ses-triangle applies to degreewise short exact sequences of arbitrary cochain complexes, not only split ones or complexes with injective terms, and supplies exactly L to K to C[0].

Step 4 uses the cohomology formula in def-weil-abstract-derived-category, the actual standard aisles in def-sbc-standard-tstructure-derived-category, and axiom (2) in def-weil-t-structure. I wrote the shift of both arguments explicitly: U[-1] has cohomology in degrees at most zero, hence Hom(U[-1],G[-1])=0 and Hom(U,G)=0. This uses no boundedness of the ambient derived category. In particular the imported t-structure definition's extraneous bounded-truncation discussion is not being used. The computation is only of L and L[1]; no unsupported assertion that arbitrary derived maps are chain maps is made.

Step 5 invokes clause (i) of Hom exactness for existence and clause (ii) for uniqueness, using the two different vanishings from step 4. The full-faithfulness statement says precisely Hom(C,G) equals Hom_D(C[0],G[0]), so it gives the named canonical additive map. Additivity follows from composition and addition in the additive category; the inverse is additive by bijectivity, not by a new structure theorem.

Step 6 uses only functoriality of shifts, chain maps, and the universal property of the cokernel. I wrote q' u=a[1]q, p' u=c[0]p and both postcomposition equations. Thus the square has the correct contravariant direction and the isomorphism is induced by p, rather than an unspecified map with a potentially different sign. Every citation's full verbatim statement is in citations.json. All steps are under 1000 characters; no long-step extraction is hidden.

I tested the statement on d=0, d=1_M, M=0 and F=0, as well as the zero abelian category. For d=0, K=F[0] plus M[1], and the boundary includes Hom(M,G) into its shifted summand, so its kernel is zero as required. For d=1, K is contractible, the first map is surjective and the cokernel and both Hom groups in degree zero vanish. For F=0 the boundary is the fully faithful single-embedding identification shifted by one. For M=0 it is the zero map out of the zero middle group, and the degree-zero isomorphism is the usual embedding for F. No projectivity, injectivity, enough resolutions, splitting of the image sequence, or finiteness is used anywhere. This also checks the concerns in delivery-errors B through E: self-contained unchanged statement, existing notions, exact citation hypotheses, no cycles via new nodes, no restatement nodes, and explicit compatibility equations.
