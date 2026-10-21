# Worker report

Item: lem-weil-pbc-finite-intersection-limit-compatibility. Group: NS. Stage 1, direct delivery. Date: 2026-10-21.

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-intersection-limit-compatibility.json`: existing statement, now split into six proof steps. Mathlib verdict: no exact match.
- `citations.json`: one entry for every step/node citation, with its verbatim statement.
- `report.md`: this report.
- `searches.jsonl`: actual results logged by the prescribed msearch command.

There are **0 new nodes and 0 Mathlib leaves**. The supporting statements already exist; the remaining arguments are explicit applications of universal properties and pointwise joint surjectivity.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id, its blueprint docstring tag, finite-intersection/limit terminology, and ind-etale terminology. `WeilConjectures/AlgebraicGeometry/Morphisms/ProAffineEtale.lean` has `AlgebraicGeometry.proAffineEtale_Spec_iff`, `AlgebraicGeometry.proAffineEtale_iff_appTop`, `RingHom.IndEtale.of_comp` and presentation-projection facts. Those provide ingredients, not the full finite-cover statement with repeated intersections and deletion compatibility. I therefore claim no finished project declaration for this item. No compiler, Lake or build tool was run.

## Wanted literature

None. The source for this item and the supporting statements is present locally.

## Findings and changes

The imported item is true as written. No statement or hypothesis was changed. I preserved the pre-existing source, created metadata, blueprint reference, and all earlier Mathlib searches. There was no previous sandbox item or report to continue.

The proof follows Stacks `literature/stacks-project/proetale.tex`, Tag 099U, `lemma-affine-vanishing`, the first-limit paragraph beginning “First we write” and the displayed formula for intersections. I also read the current blueprint proof `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-lem-pe-injective-acyclicity/lem-weil-pbc-comparison-injective-acyclicity.proof.md`. Its first-limit paragraph asks for exactly this geometry. The second limit over presentations of U and both Cech-cohomology continuity statements are separate existing items and are not needed here.

The source abbreviates the main intersection calculation as “limits commute with fibred products.” Steps 4–6 spell out its universal-property proof, with coordinate reindexing, repeated factors, and deletion identities. This is not a citation of a theorem whose proof is hidden in another node: a cone is decomposed into its individual factor maps and reconstructed uniquely. No new generic commutation lemma is necessary for this few-line argument.

I searched the DAG and blueprint (`tools/blueprint_refs.py ancestor`, searches for “ind-étale”, “finite intersection”, and “limits commute”, and text searches across all DAG nodes). Existing ind-etale stability and basis closure already give the geometric facts. No blueprint node found states this full package in another form, so `same_as` remains empty. The nearest blueprint ancestor is `lem-weil-pbc-comparison-injective-acyclicity`, matching the unchanged `blueprint.from` record. The unit and chapter records were read and not changed; this item is not their key statement.

## Mathlib searches

The inherited records were read and retained. For this item I additionally ran all four prescribed tools, using its own id in msearch. The exact five queries and their result summaries are appended in the node and present in `searches.jsonl`:

- LeanFinder, full finite-cover/ind-etale/intersection statement: affine transition-limit implementation declarations and finite-type morphism descent.
- Loogle, `AlgebraicGeometry.Scheme, CategoryTheory.Limits.IsLimit`: scheme limit, pullback and affineness declarations.
- Grep, `indEtale|IndEtale|proAffineEtale|RelativeLimitPresentation`, in Mathlib/AlgebraicGeometry: no hits.
- LeanSearch, finite coverings and directed intersection limits: affine scheme limit existence, etale topology, affine covers and pullbacks.
- LeanFinder, second phrasing in terms of simultaneous approximations and Cech intersections: affine-transition-limit auxiliaries and affine refinements of open covers.

Every service returned successfully. I read the returned declaration types and descriptions. None gives the ind-etale finite-cover presentations together with the stated compatible intersection limits; generic limit existence, open-cover descent, and the existence of etale pullbacks do not state the item. The second phrasing confirmed this. I did not record any unrun search or call any unlogged Mathlib search.

## Not duplicates

No new node was created, hence there are no new/existing pairs to distinguish. In particular, ind-etale cancellation, composition, filtered-to-directed reindexing, affine morphisms between affines, and closure of basis objects under fibre products are all citations of existing nodes, not new special cases.

## Review by NS

I read delivery-errors B–E in full and checked the six steps against both their cited node statements and the local Stacks text. The item introduces its own affine X, basis object U, finite covering, indices, and all intersections. There is no unsplit new statement carrying an illicit proof and no new definition. All six steps are shorter than 2000 characters.

For step 1 I read `def-weil-pbc-ind-etale-basis` and `def-weil-pbc-ind-etale-algebra`. They identify affine basis objects with ind-etale A-algebras and give the finite-presentation etale filtered presentations. I read `lem-weil-pbc-ind-etale-stability`, whose precise clause “every A-algebra map B→C” between ind-etale A-algebras is what is needed to present V_a over U, rather than merely over X. In the Stacks source I checked Tag 097M (`lemma-ind-etale-permanence`) as well as the ind-etale definition. Both B and C_a have the required ind-etale A-structure, and the given V_a→U is over X. I read `lem-weil-pbc-filtered-category-directed-cofinal` and the corresponding Categories Tag 0032 (`lemma-directed-category-system`): it preserves the colimit, and dually the limit. Together with `def-weil-size-convention`, small filtered presentations and their directed replacements are taken inside the fixed larger universe. No large category of all schemes is used as an index. The directed replacement is a generic indexing tool; it is declared in `split_report.tool_uses` without changing the unit route.

For step 2 I reread `def-weil-pbc-ind-etale-basis`, `def-weil-pbc-proetale-covering` and `def-weil-pbc-etale-site`. The first two make the given family jointly surjective, and the last makes a jointly surjective etale family a covering. The step actually proves the needed joint surjectivity at every stage: lift u to a point v in some V_a and then map v to the chosen stage. It never requires individual stage projections to be surjective. The finite product of nonempty directed sets is proved nonempty and directed by finite coordinate choices; smallness is closure of the chosen universe under finite products. These elementary arguments justify the elementary flag, rather than hiding a geometric descent lemma.

For step 3 the single-object presentation shows that an etale finite-presentation U-stage is ind-etale over U; composition with U→X uses exactly the composition clause of `lem-weil-pbc-ind-etale-stability`. By the basis definition this puts the affine stage in the basis. I reread `lem-weil-pbc-ind-etale-basis`: it explicitly states that fibre products of basis objects over a basis object remain in the basis. Its finite iteration gives all the intersections here, including repetitions, and in particular their affineness. `lem-weil-pbc-morphism-affine-schemes-affine` explicitly says that every scheme morphism between two affine schemes is affine, so it applies to all the transitions and the projections once their sources and targets have been shown affine. None of these uses asserts that a stage is etale over X.

For step 4 I read the universal property in `def-weil-pbc-category-colimit` and used its dual. The proof explicitly handles the product reindexing: two tuples with equal a-coordinate have a common upper bound with that same coordinate, so their maps to V_{a,i} coincide. For i≤i′ choose the other coordinates identically; this proves compatibility and hence recovers precisely a cone over J_a. This argument supplies the needed result from the universal property itself; no cofinality lemma with missing hypotheses is invoked.

For step 5 I read `def-pc-fibre-product`, which gives existence, the projection universal property, uniqueness and functoriality of scheme fibre products, and again the dual of `def-weil-pbc-category-colimit`. Iterating the binary universal property gives the finite product over U. I checked that every cone of schemes carries one common map to U, since J is nonempty and directed. Each factor cone gives one map to its limit, and the resulting factor maps have that common structure map, so they reconstruct the unique map into T_alpha. For repeated labels the two occurrences remain two separate maps: sharing a stage index does not force the factors to be diagonally equal. Thus the elementary flag describes an explicit cone calculation, not an unsupported claim that a comparison is canonical.

For step 6 the same two definitions give uniqueness after every remaining projection. I wrote the exact equality d_{r,j} t_{alpha,j} = t_{alpha without r,j} d_r and checked both sides after each surviving factor projection. This also proves transition and limit compatibility. In degree zero, deletion goes to the empty product U; the equation reduces to equality of structure maps. The constant U diagram has limit U because J is nonempty and connected (any two indices have an upper bound).

I tested the following boundary cases. If U is empty, the stage covering condition is vacuous and the presentations/universal properties still apply. Empty individual V_a are allowed; the proof never assumes any source point exists unless lifting a chosen u. For m=1, J is the one chosen directed set. For p=0, the intersection is its sole factor. For a tuple (a,a), two arbitrary maps to V_a over U are allowed, not just the diagonal. A singleton directed presentation works. A non-surjective individual projection causes no difficulty, because only the image of a selected covering point is used. Finally X=Spec(F_p), U=Spec(algebraic closure of F_p) illustrates why finite-presentation etaleness is only over U and cannot be claimed over X; the split preserves that distinction.

The citations file contains the actual full statement of every cited node as a verbatim quote, so every clause used can be checked without relying on another node's proof. There is no additional C1 lemma hidden behind “standard,” “transport,” or “compatibility”: the relevant cone and projection calculations are written explicitly. All non-elementary geometry is a cited node, and no new statement merely repackages a clause of the item.

## Unfinished work

None within this stage-1 item. The existing supporting nodes retain their own statuses and obligations. Delivery is subject to the required server dry run and independent maintainer review.
