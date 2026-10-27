# Split of lem-sfb-semilinear-equivariant-chow-modification

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-semilinear-equivariant-chow-modification.json`: statement, split; no Mathlib match. Nine steps construct the finite product of semilinear translates and its integral closure component, using existing nodes only.
- `citations.json`: one verbatim statement quotation for each of the 36 step/node citations.
- `searches.jsonl`: five searches actually executed by msearch.py, covering grep, Loogle, LeanSearch and two distinct LeanFinder questions. The item retains its inherited search records as well.
- `report.md`: this report. `write_split.py` is a sandbox-only preparation script, not part of the delivery.

New nodes: 0. New Mathlib leaves: 0. No Lean files or unit/chapter records were written.

## Attachments

None for this item. I searched the project library for its literal blueprint tag, Chow, equivariant projectivity and semilinearity. The ordinary theorem `AlgebraicGeometry.exists_projective_modification`, in `lean/WeilConjectures/AlgebraicGeometry/ChowLemma/ProjectiveModification.lean:36`, gives ordinary proper/projective domination and the dense isomorphism open, but supplies no finite-group action. Its body was read; its existence does not finish the assigned item. The DAG already has the ordinary result as `lem-fin-noetherian-chow-modification`.

## Literature

WANTED: local copy of A. J. de Jong, *Families of curves and alterations* (1997), §2.10, printed p.605, for lem-sfb-semilinear-equivariant-chow-modification. I read the publisher PDF online at https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf, page 7 (zero-based). That paragraph prescribes Chow modification and finite-group averaging before flattening; it refers elsewhere for the averaging details. The averaging argument here is written out by the worker, not attributed as a complete proof in that paragraph. The node is explicitly `proof_origin.by = agent`.

The local mathematical sources actually read were Stacks `coherent.tex`, Tag 0200 (`lemma-chow-Noetherian`); `constructions.tex`, Tag 01WD (`lemma-segre-embedding`); and `morphisms.tex`, Tags 01R8 (`lemma-quasi-compact-scheme-theoretic-image`), 056B (`lemma-scheme-theoretic-image-reduced`), 01WF (`lemma-H-projective-base-change`), 01WC (`lemma-locally-projective-proper`), 0C4Q (`lemma-projective-permanence`), and the base-change/composition lemmas for closed immersions. The finite-projective-space version of the last permanence result is the statement of the existing `lem-per-h-projective-permanence`; it uses a closed graph and retains the same ambient dimension.

## Findings and corrections

The statement is mathematically sound for arbitrary fields, arbitrary finite groups and nonfaithful actions. I preserved every hypothesis and conclusion. The only statement-text edit replaces doubled backslashes by single TeX escapes. No mathematical statement correction or STATEMENT-DISPUTED claim is needed.

The semilinear point matters: the existing `lem-per-equivariant-projective-envelope` requires actions over a fixed base. I did not apply it to the present moving-field action. Instead the underlying copy $Y_g$ has structure morphism $b_gf\pi$ and map $a_g\pi$ to $X$. It is the isomorphic-base pullback along $b_g^{-1}$, which proves its projectivity without assuming triviality of the action on the field. The left action on Spec of a field is taken with the usual contravariant inverse convention.

The inherited `blueprint.from.node` is null. `tools/blueprint_refs.py ancestor` returns None: following `created.item` eventually reaches a Lean module name rather than an imported blueprint node. I retained that ancestry and its explicit existing place, which names the direct-image alteration route and de Jong §2.10. I read the current unit record, chapter record and available main-20261015 unit `_section.md`. The individual direct-image blueprint path recorded in the ancestor node is not a local file in this snapshot. Nothing in the chapter/unit route is changed. The item is not a unit key theorem and does not own a unit realization update.

The candidate `lem-chow-scheme-theoretic-closure` assumes the original open is already dense in the entire ambient scheme; that is not available for the product $P$. I instead use the general reduced-source image theorem and the general restriction-of-image theorem. This avoids quietly treating a dense open in $X$ as dense in $P$ before taking its closure.

## Not duplicates

No new nodes were created. Whole-DAG and whole-blueprint searches for Chow, equivariance, projective modification and Segre found the ordinary modification, product embeddings and generic image tools already present. I cite them rather than introducing duplicate nodes. The finite-field-linear projective-envelope node is not a replacement for the present semilinear construction.

## Review by NN

I checked the split against delivery-errors B–E with the node statements and the Stacks source open. The argument takes one ordinary modification, constructs actual twisted copies and an actual finite fibre product, and defines actual automorphisms by projections; no new node is a restatement of the desired equivariant conclusion. There are no new standalone statements whose hypotheses could be underspecified, no invented Mathlib searches, and no unsplit nodes containing proof sketches. Every non-elementary input is a named existing node. The longer computations have been kept as steps because they are explicit universal-property or quotient-ideal calculations; the longest step is 1071 characters, below the 2000-character review threshold.

Step 1 uses the field and locally-Noetherian definitions, the integral/reduced equivalence, the ordinary Chow modification, the projective-space convention, and the finite-type-over-Noetherian theorem. I verified that the base is affine Noetherian by the two-ideal argument for a field, that reducedness follows from integrality, and that the modification node supplies both the projective source and the dense isomorphism open. This step does not take any equivariance from that theorem, or assume its source is integral.

Step 2 uses only the fibre-product universal property, projective-space pullback and closed-immersion base change. Those statements allow arbitrary base maps, including field automorphisms; they do not require flatness. I checked the inverse: the pullback along $b_g^{-1}$ has structure morphism $b_gf\pi$, exactly as used. The invariant open is the finite intersection of all translates. Its density is proved by successive intersections with an arbitrary nonempty open, and invariance is the permutation of its finite indexing set.

Step 3 uses the actual two-base fibre-product closed-immersion statement, the product/composition statement for closed immersions, and the Segre closed immersion. The map whose separatedness is needed is $X\to\operatorname{Spec}k$, which is separated because it is proper. Induction first embeds the product over $X$ into the product over $k$, and then embeds the latter in a single finite-dimensional projective space. The projectivity definition therefore has exactly its finite-space meaning. No claim that an arbitrary product over $X$ is integral is used.

Steps 4 and 5 use the statement of `def-pc-fibre-product`, including its existence, uniqueness and functoriality, and the open-immersion definition. I checked the noncommutative indexing calculation: the $g$-projection of $A_hA_l$ has index $l^{-1}h^{-1}g=(hl)^{-1}g$. The common image is $a_hr$, so the universal property really constructs a morphism of schemes, with the specified semilinearity. The inverse is $A_{h^{-1}}$. Over the invariant open each factor is literally isomorphic to that open, so the product restriction is also isomorphic to it and the action restricts to the original action there.

Step 6 uses the general image definition, `lem-trf-reduced-scheme-image`, the integral-scheme equivalence, projective-implies-proper, proper-implies-finite-type, finite-type-over-Noetherian, Noetherian opens, and restriction of schematic image to opens. I read their statements and checked the hypotheses: $U$ is nonempty and integral, $P$ is Noetherian by its projective structure map, the open immersion $U\to P$ is quasi-compact and quasi-separated, and its restriction to $P\times_XU$ is the identity. The reduced-image statement gives a reduced scheme on precisely the closure of the irreducible set $U$, which is integral. The restriction theorem gives equality as schemes over $U$, not just an equality of points. No normality, perfection or geometric-integrality hypothesis is inserted.

Step 7 uses the explicit affine-kernel clause of `lem-weil-pbc-scheme-image-qc-kernel` and the affine quotient description of a closed immersion. Pullback of a function vanishing on $U$ again vanishes there; applying the inverse automorphism gives equality of ideals. Passing to quotient sheaves gives the restricted automorphism and the group law. This checks the scheme-theoretic invariance instead of relying on topological stability of the closure.

Step 8 uses closed-immersion composition, finite-space projectivity, `lem-per-h-projective-permanence`, projective-implies-proper, and the properness/surjectivity definitions. I checked the exact triangle: its separated map is $f:X\to\operatorname{Spec}k$, and its projective composite is $T\to\operatorname{Spec}k$. The cited permanence statement supplies an embedding over $X$ without a stronger hypothesis on $X$. Properness gives finite type and a closed image; since the image contains the dense open, it is all of $X$. Thus all existential clauses of the item are proved, including both projective embeddings.

Step 9 uses the function-field definition, including its final arbitrary-integral-scheme clause, and the generic-stalk/affine-fraction theorem. I checked that the same open is dense in both schemes and hence contains both generic points. Its isomorphism identifies the generic local rings by the morphism induced by $q$, so this is the required identification of function fields, not an arbitrary field isomorphism.

The citations file contains an actual verbatim statement for every cited node at each step. I did not use any cited node's proof as an implicit strengthening of its statement. Off-unit statements are generic tools, recorded with reasons in `split_report.tool_uses`; the maintainer-owned top-level tool_uses field is untouched.

I tested the construction for the trivial group (one factor and ordinary integral closure component), $X=\operatorname{Spec}k$ (no positive-dimensional argument), nonfaithful actions (the repeated factors cause no problem), noncommutative finite groups (the indexing formula above), and characteristic dividing $|H|$ (no division or averaging of functions occurs). The product may have extra components or nilpotents; passing to the reduced schematic closure of the integral open handles both.

The item Mathlib searches returned only unrelated linear projectivizations, representation-theoretic projectivity, ordinary Proj properness, invariant topological opens and basic scheme properness. Reading the returned signatures rules out an exact match or one-line specialization. The two distinct semantic phrasings asked first for the semilinear equivariant modification itself and then for the product-and-closure construction. All five searches succeeded; none is mislabeled as absence following an unavailable service.

Preliminary server `review_split` passed with zero new nodes. It notes the unit's previously unfilled realization record; this item does not own that record.

## Unfinished work

None within the stage-1 item. The reused unsplit Segre node remains the existing DAG's item; it was not replaced or split here. The independent maintainer review and eventual formalization are outside this worker delivery.
