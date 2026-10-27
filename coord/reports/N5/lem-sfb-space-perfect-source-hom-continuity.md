# N5 stage-1 delivery: lem-sfb-space-perfect-source-hom-continuity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-perfect-source-hom-continuity.json: the unchanged statement, now split in nine steps; not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-derived-hom-mayer-vietoris.json: one new statement-only lemma, unsplit; searches found no Mathlib match.
- citations.json: one verbatim quotation of the cited statement for every step/node pair. Full statements are quoted so the hypotheses as well as the conclusions remain visible.

One new node, zero Mathlib leaves. No unit file, Lean file, shared repository file or launcher file was written. Sandbox scripts are working notes, not delivery files.

## Attachments

None. Searched the live project source by the item's blueprint tag and by perfect/Hom/limit concepts, and inspected the scope of the affine-perfect declarations and the ring-complex comparisons. Scheme results for two perfect complexes, and algebraic results about bounded finite-projective targets, do not state the algebraic-space assertion with its arbitrary unbounded quasi-coherent target. No project declaration states the full new Mayer–Vietoris assertion either; the existing derived-open-Hom result concerns open covers of ringed spaces, rather than elementary distinguished squares of algebraic spaces.

## WANTED

None. All mathematical source files used are present under literature/stacks-project/.

## What needed repair

The imported item had a statement and searches but no proof. Its statement is correct: it is precisely clause (1) of spaces-perfect.tex Tag 09RI, in Situation 09RH, with the chosen index renamed. I have not changed its hypotheses, statement dependencies, statement, source or inherited blueprint chain. In particular I have not assumed that K is perfect, bounded, coherent, finite Tor dimensional, or that the transition maps are flat. There is no STATEMENT-DISPUTED issue.

Several existing Picard-framework Hom-continuity results require that both objects be perfect, or both module complexes have finitely presented terms. They cannot provide this item's affine case for arbitrary K. I initially considered a separate fixed-ring finite-projective filtered-Hom lemma, searched it, then removed it before delivery: the finite-coordinate proof is elementary from the existing elementwise module-colimit theorem and is now written in steps 5–6. Its exploratory queries remain honestly logged in searches.jsonl; no discarded node is delivered. On self-review I also added the existing bounded-flat K-flatness theorem in step 3, rather than treating that theorem as part of the definition of projectivity.

The nearest blueprint ancestor returned by tools/blueprint_refs.py ancestor is null, already so in the item. I retained that value and its full explicit from.place and via chain. Whole-blueprint searches for perfect/limit, Hom continuity, induction principle, 08H9, derived Hom Mayer, and bounded projective filtered found no equivalent blueprint assertion to substitute. I read the latest blueprint unit sk-thm-sf-ctf-stability, and the existing chapter and unit records and their route. This remains the Tag 09RI full-faithfulness input below the existing perfect-limit-category and direct-image-stability route.

## Review by N5

I read spaces-perfect.tex Situation 09RH, the complete statement and proof of Tag 09RI, and the scheme proof in perfect.tex Tag 09RE, particularly case (1). The latter explicitly chooses a bounded finite-projective source and an arbitrary K-flat target: only the source is finite. This is why no boundedness restriction has appeared in the split. I also read spaces-perfect.tex Tag 08GP (the exact distinguished-square induction hypotheses), Tag 08H9 (derived Hom excision), its extension-by-zero input Tag 08GV, the small-etale equivalence Tag 071Q, and the perfectness comparison Tag 08HG. I checked the tag/label table rather than relying on numerical section references; an initially mistyped perfectness-comparison tag in a proof source was corrected to 08HG.

For the new node I read Tag 08H9 and its proof from the canonical extension-by-zero triangle, and the actual statement of lem-sfb-space-elementary-shriek-exact. The latter gives the exact functors, the signed sequence, and its version after arbitrary base change. The new node states the Hom long exact sequence for arbitrary derived objects, including negative degrees, and explicitly requires the naturality of its specified boundary under derived base change. This last compatibility is essential for a directed system of exact sequences; it is not inferred merely from the existence of some long exact sequence. It is the canonical-triangle naturality implicit in the 09RI argument, recorded as a separate reusable theorem to be split later. The new node has no proof, no proof dependencies and no proof sketch inside its statement.

For every proof step I opened and read the statement of every cited node. The following are the actual uses and hypothesis checks.

1. The affine-limit node gives affine projections and the formula for base change of the inverse limit; affine-locality gives affine base change and qcqs preservation. The chart-calculus node states preservation of quasi-coherent cohomology, exact etale restriction, pullback base change and associative comparisons. These statements apply to the chosen small directed tail and qcqs etale test T. The property is formulated for all integer shifts, not only degree zero. Perfectness of the restriction follows directly by restricting its local summand models.

2. Affine-locality and affine projections show that each pulled-back space is an affine scheme. The limit-sections node gives the coordinate-ring colimit with its actual maps. The quasi-coherent clause of lem-sfb-space-perfect-uniform-tor applies because the initial test T is affine, hence quasi-compact; I do not use its Tor bounds. The existing Zariski–etale equivalence explicitly covers unbounded D_QCoh and composition-compatible pullbacks; etale-detects-perfect gives the needed direction of perfectness. The affine perfect theorem supplies a bounded finite-projective model, the affine derived equivalence supplies a complex for K, and the module K-flat-resolution theorem explicitly allows an unbounded input. Each is applied to the same commutative coordinate ring A_0. There is no Noetherian or finite-type hypothesis in these inputs.

3. The affine derived-pullback theorem identifies derived scalar extension; the etale comparison makes this the structure-module pullback in the item. Finite-projective terms are flat by their explicit finite-free splittings, and the newly added bounded-flat K-flatness citation proves that this bounded source computes its own derived tensor. The target uses its K-flat replacement from step 2. Bounded-above-projective K-projectivity and lem-coef-kprojective-derived-hom-bijection give chain maps modulo homotopy for any target complex. I checked that the latter node says this for every target, unlike the separate bounded-below Hom-complex lemma which I did not cite. The two displayed scalar-adjunction formulas work on maps and on degree-minus-one homotopies; they explain exactly why the comparison is the prescribed pullback cocone rather than an unspecified bijection.

4. The algebra-colimit-underlying-module theorem explicitly applies to a small filtered diagram of commutative A_0-algebras. Tensor-colimit preservation applies degree by degree to its module cocone and the fixed module C^r; tensor symmetry interchanges the factors if necessary. The maps commute with the differential by naturality. No derived filtered-colimit interchange or unbounded spectral sequence is used.

5. The module elementwise-colimit theorem gives both finite-stage representatives and eventual equality. With a splitting B^r -> A_0^m -> B^r, lifting the finitely many values of f on the second map's standard basis and precomposing by the first map lifts f. Equality is checked on that same finite generating list. This is the complete elementary argument, including simultaneous choices by directedness; it needs no finite presentation or boundedness of target modules.

6. The same elementwise theorem kills the finitely many chain-map defects and then the finitely many homotopy defects. Boundedness of B is what makes the lists finite, even though C may be unbounded in both directions. The shifted differential is used in the homotopy equation. This proves both surjectivity and eventual equality of homotopy classes, not just descent of graded maps. The maps are those identified in step 3.

7. The new Mayer–Vietoris statement supplies precisely the two unbounded Hom sequences, their exactness and their canonical base-change squares, including the boundary square. The existing abelian-group filtered-exactness node explicitly states that a filtered system of long exact sequences stays exact. Its indexing category is the small directed tail already fixed. Finite direct-sum interchange here follows from the biproduct universal property. I wrote the five terms and require the induction hypotheses in adjacent degrees, so no boundary compatibility or negative Ext group is suppressed.

8. I wrote both directions of the elementary five-term diagram chase. In the injectivity argument one subtracts a lifted preceding local-pair element before invoking the overlap comparison's injectivity. Thus no unjustified assertion that a morphism zero on a cover is globally zero occurs. The middle group is recovered using the preceding overlap degree as well as degree n.

9. The existing qcqs distinguished-square induction node has exactly the affine and square hypotheses verified in steps 2–8, and its conclusion includes X_i itself. Our property is invariant under isomorphism because its cocone consists of canonical pullbacks. Taking n=0 gives the unchanged statement. I did not cite the scheme-only open-union induction principle for algebraic spaces.

I checked empty spaces and the zero ring, the zero source or target, constant systems, shifted sources and targets, targets unbounded in both directions, and nonflat transition ring maps (including quotients). The finite-coordinate argument still works because it only uses the colimit cocone and finite source splittings. In the new Mayer–Vietoris assertion U=W makes the overlap contribution cancel; U empty forces V=W and gives the same identity case. Arbitrary-base-change naturality refers to derived pullback, so it does not assert that underived pullback is exact for a nonflat base change.

I reviewed delivery-errors B–E against the final node files: the new statement introduces all spaces and functors and has explicit definitions/dependencies; every non-elementary proof input is a cited statement, with quotes in citations.json; the new lemma is excision for arbitrary objects and is not the limit-Hom assertion or one of its clauses; no proof uses a node's private construction. The finite-coordinate calculation and the diagram chase are written out as elementary steps instead of extra nodes. Every proof step is shorter than 2000 characters. No SGA source is used. A source-only dependency traversal found no path from a cited node back to the item; server DAG validation remains authoritative. Searches were run only through the required msearch command, with the exact query and actual results recorded for the new node. I read the Mathlib MayerVietoris sheaf-cohomology file: it concerns a single abelian sheaf and ordinary cohomology, so it is not a one-line specialization to the new two-complex structure-module assertion.

## Not duplicates

lem-sfb-space-derived-hom-mayer-vietoris vs lem-sc-derived-hom-mayer-vietoris: the existing statement is for two open subspaces covering a ringed space; the new statement is for an elementary distinguished square of algebraic spaces with an etale V, all integer degrees, and canonical derived-base-change boundary compatibility.

lem-sfb-space-derived-hom-mayer-vietoris vs lem-sfb-space-relative-mv-exchange-triangles: the existing statement is a triangle of relative derived direct images and its exchange morphism; the new statement is a long exact sequence of Hom between two arbitrary objects, with the contravariant source and covariant target both pulled back. It is not obtained by taking cohomology of the existing direct-image triangle alone.

lem-sfb-space-derived-hom-mayer-vietoris vs lem-sfb-space-elementary-shriek-exact: the existing statement gives an exact sequence of endofunctors on module sheaves and its base-changed versions; the new statement asserts derived Hom excision and the compatibility of its connecting maps with derived pullback. The existing statement is explicitly retained as a statement dependency of the new theorem.

lem-sfb-space-derived-hom-mayer-vietoris vs lem-sfb-space-distinguished-derived-gluing: the existing statement glues objects and compatible maps from local objects to one global target; it does not state the long exact Hom sequence, its negative-degree term, or naturality of connecting maps under derived base change.

## Remaining work

The one new excision theorem is statement-only, as required for a one-level split. No part of the item's natural-language proof is left implicit. The maintainer's independent mathematical review and subsequent formalization remain outside this delivery.
