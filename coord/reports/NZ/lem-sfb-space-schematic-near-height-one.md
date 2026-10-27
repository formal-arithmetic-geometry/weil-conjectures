# Stage-1 report: lem-sfb-space-schematic-near-height-one

1. Files written:
   - `dag/nodes/sec-six-functors-basics/lem-sfb-space-schematic-near-height-one.json`: item, statement, split into seven steps, not a Mathlib match.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-finite-groupoid-height-one-affine-open.json`: new statement-only node, full absolute version of Stacks 0ABI, unsplit; no Mathlib match.
   - `citations.json`: a verbatim statement quote for every node cited by every numbered step.
2. Attachments: none. Searches of `lean/WeilConjectures/` for the item id, AlgebraicSpace, algebraic space, schematic locus and codimension found no declaration proving this item. Existing scheme codimension results do not assert schematicity for algebraic spaces.
3. WANTED: none.
4. The item statement is unchanged and agrees with the pointwise local-ring hypothesis of Stacks 0ADD. The field-only existing invariant-affine node cannot be applied over a general scheme, nor can the field-only finite-cover node. I use the existing arbitrary-base 09YC finite cover and create only the full absolute 0ABI statement. I did not assume that local dimension at the chosen point bounds global dimension. The inherited blueprint ancestor is null: the ancestor command reports None. Its inherited chain and historical direct-images (3) place are retained. The latest blueprint's direct-images proof (3) still uses the proper/open compactification route; this is a historical prerequisite below that route, not a replacement of it. Neither the chapter nor unit record was changed.
5. Nothing remains unfinished in this split. The new dependency is intentionally statement-only and joins the stage-1 queue. No Lean was written and no compiler, Lake or build command was run.

## Sources and searches

I read the main proof, not the alternate flattening proof, of `literature/stacks-project/spaces-over-fields.tex`, Tag 0ADD, label `lemma-codim-1-point-in-schematic-locus`, lines 1439–1484. Its inputs were checked in `spaces-limits.tex` 09YC (`proposition-there-is-a-scheme-finite-over`), `decent-spaces.tex` 0ABW (`lemma-dimension-local-ring-quasi-finite`), `more-groupoids.tex` 0ABI (`lemma-find-affine-codimension-1`), and `spaces-cohomology.tex` 07VP (`lemma-image-affine-finite-morphism-affine-Noetherian`). The new node is exactly the absolute groupoid statement of 0ABI at lines 2806–2814, with orbit containment following from invariance. I also read 0BAM/04NA on chart independence, 03FY on affine-atlas opens mapping to an affine base open, 01T6 on local Noetherianity under local finite type, 034C on etale/fppf descent of local Noetherianity, 0414 on finite implies integral, 04NY on finite implies quasi-finite, and 03H4 on fibre-product points.

Before creating the node I searched the whole DAG for 0ABI, its source label, invariant affine opens and finite groupoids, and ran `tools/blueprint_refs.py search` for schematic, schematic codimension, invariant affine, invariant affine groupoid, 0ABI and 09YC. None of the blueprint hits states the new absolute groupoid result. I read the candidate existing nodes rather than inferring their contents from titles. The same-tag comparisons are below.

All new Mathlib searches ran through the prescribed `msearch.py` and are in `searches.jsonl`. For the new node I ran leanfinder with two phrasings (finite groupoid/invariant affine and saturated finite orbit), leansearch, loogle with Groupoid/IsAffine and a grep for invariant affine/groupoid. For the item I likewise ran two leanfinder phrasings, leansearch, loogle and grep. All services responded. Hits state affineness or local affine neighborhoods for already given schemes, finite morphism characterizations, and Noetherian/Artinian scheme properties. They do not state either groupoid invariance or an algebraic-space schematic neighborhood. I read the finite-morphism definition and instances in `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`, the local Noetherian definition in `Noetherian.lean`, and the single-point affine-open result in `AffineScheme.lean:272`. The extra grep recording the candidate declarations is also logged. No Mathlib leaf is claimed. The item's earlier search records have been retained along with the searches made for this split.

## Review by NZ

I checked delivery-errors B–E against the actual JSON and the sources. The new statement introduces its groupoid, orbit and point; it uses the existing definitions of absolute groupoid schemes, finite morphisms, separatedness, local Noetherianity, stalk dimension, affine schemes and open immersions. It has no proof or hidden proof sketch. It is not a clause of the item: it is a theorem about arbitrary finite groupoids, with no algebraic-space quotient hypothesis. Conversely the item's remaining steps construct the cover, verify its hypotheses, identify its orbit and descend its open.

For step 1 I read chart invariance (0BAM/04NA), the affine-atlas open cover (03FY), the open-image and point calculus statements, change of base to integers, and the affine-pair quasi-separatedness criterion. These give exactly the chosen open with affine base, its quasi-compactness and the chart test for its absolute diagonal. The closed-immersion definition makes a closed subscheme of an affine scheme affine; affine schemes are quasi-compact. I added the actual base-change-of-closed-immersion citation rather than silently treating it as a definition. Restricting the given pointed etale chart preserves its stalk; every chart of the open is a chart of X. This verifies both the local Noetherian and the pointwise dimension assertions without a global dimension assumption.

For step 2 I checked that the arbitrary-base 09YC node supplies a finite surjection from a scheme, not a Noetherian separated source as extra output. The cited fibre-product/etale-cover statement gives the surjective etale map from its pullback to the affine chart. The finite-morphism definition supplies local finite type (module generators are algebra generators), 01T6 makes that pullback locally Noetherian, and the existing 034C descent statement makes Y locally Noetherian. This is an explicit verification of a hypothesis of 0ABI, not an inference from the title of the cover node.

For step 3 I corrected an initial draft citation: the finite-space topology statement does not itself assert finite implies integral. The actual citation is now the existing Mathlib leaf `pqf-lem-finite-integral-lft`, applied on every scheme test. The integral permanence node states separatedness, the composition node states composition of separated morphisms, and the scheme-over-affine lemma explicitly yields absolute separatedness. The affine-base restriction in step 1 is essential here; no separatedness of S was added to the item.

For step 4 the finite-space topology node explicitly says locally quasi-finite, and the local-ring dimension node says precisely dim O(Y,y) <= delta(Z,f(y)). Chart invariance supplied delta(Z,x) <= 1 in step 1. The inequality is applied to every point over x, so the full orbit hypothesis of 0ABI is available. I deliberately do not cite the distinct global topological dimension inequality.

For step 5 I checked diagonal representability in the algebraic-space definition and base-change finiteness in the topology node. The displayed pair formulas directly give the identities, inverse and composition laws of the absolute groupoid definition. The fibre-product-point statement gives an arrow for any two points over x, including nonrational points after a common field extension, so the orbit is the whole fibre. The new 0ABI statement then applies with exactly the separatedness, local Noetherianity and orbit dimension proved in preceding steps.

For step 6 I checked the same point-lifting lemma, the finite map's closedness, and both open-subspace correspondence and pullback-open statements. Saturation gives f^(-1)(f(W))=W; closed surjectivity makes its image open by the displayed complement formula. This proves that the scheme W is the actual pullback over the open, not merely a scheme whose point image happens to lie there. Thus finiteness survives as a base change and surjectivity is on field-point classes as required by 07VP.

For step 7 I checked that 07VP requires the target to be Noetherian. It is locally Noetherian by open restriction, quasi-compact by the explicit finite-subcover argument applied to W, and quasi-separated by the stated open-subspace permanence clause. The affine source hypothesis is the conclusion of 0ABI. The finite-affine-descent node therefore gives a scheme, with the induced original S-structure; x lies in this open because its entire fibre was in W. Each citation quote is the referenced node's full verbatim statement, so all the portions used can be read without looking into that node's proof.

Small cases: a generic point (dimension zero) satisfies the same orbit bound; a height-one point with arbitrarily high global-dimensional components is allowed; a nonreduced Noetherian scheme is allowed by 0ABI and 07VP without reduction; empty U in the new node supplies no point u and is vacuous, and the identity groupoid recovers an affine neighborhood of a single height-at-most-one point. In the item the given v ensures a nonempty fibre. No algebraic closure, rationality, flatness of the finite cover or finite type over the base has been assumed. A mixed-characteristic base such as Spec Z cannot be fed to the field-only old lemma, which is why the absolute version is a genuine additional input. Every step is below 2000 characters, with the groupoid formulas and saturated-open argument written out instead of hiding further lemmas. The split contains no SGA source.

## Not duplicates

lem-sfb-finite-groupoid-height-one-affine-open vs lem-sfb-finite-groupoid-almost-dense-flat-locus: the existing node gives invariant almost-dense open/closed subschemes carrying finite locally free restrictions; it does not place a specified low-height orbit in an invariant affine open.

lem-sfb-finite-groupoid-height-one-affine-open vs lem-sfb-finite-groupoid-almost-invariant-function: the existing node constructs a function after a specified immersion in an affine scheme, for generic-point orbits and finitely presented arrows; no such immersion, genericity or finite presentation is assumed in the new node.

lem-sfb-finite-groupoid-height-one-affine-open vs lem-sfb-finite-groupoid-codimension-one-invariant-affine: the existing node assumes a groupoid over a field K; the new absolute version allows mixed characteristic and schemes admitting no field structure, as required over an arbitrary affine scheme base.

lem-sfb-finite-groupoid-height-one-affine-open vs lem-sfb-finite-groupoid-generic-affine-flat-thickening: the existing node treats generic-point orbits with finitely presented arrows and a thickening; the new node also treats height-one nongeneric orbits without finite presentation of the arrows.

lem-sfb-finite-groupoid-height-one-affine-open vs lem-sfb-finite-groupoid-invariant-rank-filtration: the existing node gives invariant closed rank strata, not an invariant affine neighborhood of a specified orbit.

lem-sfb-finite-groupoid-height-one-affine-open vs lem-sfb-finite-groupoid-orbit-incomparability: the existing node prohibits specializations between distinct points of an orbit; it supplies no invariant affine open.

lem-sfb-finite-groupoid-height-one-affine-open vs lem-sfb-finite-presented-groupoid-rank-filtration: the existing node gives invariant finitely presented rank strata and assumes finitely presented arrows; the new node gives an affine neighborhood under local dimension bounds.

lem-sfb-finite-groupoid-height-one-affine-open vs lem-sfb-flat-group-space-fpqc-scheme-cover: the existing node concerns a flat group algebraic space over a discrete valuation ring and an fpqc schematic cover, not a finite groupoid on schemes.

lem-sfb-finite-groupoid-height-one-affine-open vs lem-sfb-generic-point-fp-closed-interior: the existing node concerns a finitely presented closed immersion at a generic point and contains no groupoid or invariant-affine conclusion.

lem-sfb-finite-groupoid-height-one-affine-open vs lem-sfb-groupoid-subset-saturation-invariant: the existing node proves invariance of the set-theoretic saturation of a subset, not openness or affineness of a neighborhood.

lem-sfb-finite-groupoid-height-one-affine-open vs lem-sfb-immersion-principal-affineness: the existing node is an affine-immersion criterion involving a principal open and a closed complement, not a groupoid neighborhood assertion.

lem-sfb-finite-groupoid-height-one-affine-open vs lem-sfb-integral-orbit-affine-descent: the existing node descends an already-given invariant affine neighborhood along an integral map meeting every orbit; the new node needs no such auxiliary map or pre-existing neighborhood.

lem-sfb-finite-groupoid-height-one-affine-open vs lem-sfb-locally-free-groupoid-invariant-affine: the existing node assumes finite locally free source and target and an affine open already containing the orbit; our finite arrows need not be flat, and the orbit has only local dimension bounds.

lem-sfb-finite-groupoid-height-one-affine-open vs lem-sfb-separated-space-dimension-one-scheme: the existing node concerns an algebraic space locally of finite type over a field with a global topological dimension bound, not arbitrary finite groupoids with one low-height orbit.
