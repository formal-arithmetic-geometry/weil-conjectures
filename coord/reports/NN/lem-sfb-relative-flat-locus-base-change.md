# Stage 1 delivery: lem-sfb-relative-flat-locus-base-change

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-flat-locus-base-change.json`: item, split into six steps; original statement and hypotheses retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-fibrewise-flatness-criterion.json`: new statement-only prerequisite, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-pointwise-flatness-base-change.json`: new statement-only prerequisite, unsplit; no Mathlib match.
- `citations.json`: one entry for each step/node citation, quoting the cited statement verbatim. Full statements are quoted to keep the hypotheses visible alongside their conclusions.
- `searches.jsonl`: actual Mathlib search records produced by the prescribed msearch command. No searches were fabricated. Supplemental `write_split.py` is a sandbox-only preparation script, not project tooling.

Two new nodes, zero new Mathlib leaves. Existing Mathlib leaves, especially finite presentation over an intermediate finite-type algebra, are reused.

## Attachments

None. I searched the live read clone under `lean/WeilConjectures/` for the item id, flat-locus names, and pointwise flatness/fibre-flatness terminology. The algebraic openness declaration is already represented by `lem-weil-pbc-openness-of-flatness`. The private `flat_stalk_of_flat_test` in `AlgebraicGeometry/Morphisms/SmoothLocalDepthTwoClosedFiberFlat.lean` assumes global flatness of the test map and of the pulled-back map; it does not state the two pointwise implications in the new base-change prerequisite. It is not an attachment for either the item or the new node. No Lean was written or compiled.

## WANTED

None. All sources used are present in the read-only literature tree.

## Problems found and changes made

The item was an unsplit statement of Stacks 05VK. Its own source proves it by specializing 05VJ to the structure sheaf. I expanded the actual proof of 05VJ instead of making a new node for that full generalization. In particular, neither new node asserts openness or arbitrary parameter-base-change equality, and there is no new lemma merely restating a clause of this item.

The inherited ancestry has `blueprint.from.node = null` and unit `sk-thm-sf-ctf-stability`, while the current chapter record describes the related six-functor basics chapter. `python3 tools/blueprint_refs.py ancestor lem-sfb-relative-flat-locus-base-change` returns exactly `None`. I retained that inherited ancestry and chapter/unit, gave the new nodes the same ancestor and extended via lists, and located the prerequisites in the inherited direct-image/alteration, de Jong/Hilbert-scheme route. This is not the key node of the unit; no unit realization field is changed.

I searched the whole DAG and blueprint by tags 039C, 047C, 02FV, 0561 and by flat-locus, flatness, finite-presentation and base-change concepts. This found the existing finite-presentation cancellation node, so no third node was created. The existing algebraic fibre criterion 00R7 needs the intermediate local ring essentially finitely presented; here Y is only locally of finite type. The new geometric criterion uses the version 039C, whose algebraic input is 05UV, and does not silently strengthen Y's hypothesis.

## Not duplicates

lem-sfb-fibrewise-flatness-criterion vs lem-weil-pbc-criterion-flatness-fibre: the existing 00R7 result assumes both intermediate local algebras essentially finitely presented; the new 039C scheme criterion allows Y only locally of finite type, with no Noetherian hypothesis.

lem-sfb-fibrewise-flatness-criterion vs lem-sbc-polynomial-chart-stalk-flat-comparison: the existing node is for a specified affine-space chart over an affine base; the new node is a pointwise criterion for an arbitrary map of S-schemes and also concludes flatness of Y over S at the image.

lem-sfb-pointwise-flatness-base-change vs lem-weil-pbc-flat-morphism-base-change: the existing node assumes global flatness and only asserts ascent; the new 047C node has pointwise ascent and reflection when the base map is flat at the specified image point.

lem-sfb-pointwise-flatness-base-change vs lem-pc-flat-source-descent: source descent is a global theorem for a surjective flat source map; the new statement is at one chosen point in a cartesian base-change square, imposes no global surjectivity, and includes arbitrary-base-change pointwise ascent.

No existing node has 039C or 047C as its mathematical source. These comparisons also explain the nearby concept matches. The imported item itself is the only node stating its full relative locus assertion. Whole-blueprint searches for `flat locus`, `047C`, `039C`, `02FV` and `criterion flatness` found no corresponding imported node; the broader searches were read and did not supply either prerequisite.

## Review by NN

I read Stacks `more-morphisms.tex`, Tag 05VK (lemma-base-change-flatness-fibres) and its cited Tag 05VJ (lemma-base-change-criterion-flatness-fibre), including the full fibre-square argument. For the new fibre criterion I read Tag 039C (theorem-criterion-flatness-fibre), both its statement and proof, and checked its non-Noetherian algebra input 05UV in `algebra.tex`. The specialization uses the structure sheaf, whose stalk at a point is nonzero and which is free of rank one over itself. Its pointwise flatness over S and fibre-flatness hypotheses are exactly the ones stated in the new node. The node carries only implication (1) to (2), without the theorem's separate openness conclusion. For the other new node I read Tag 047C (lemma-flat-locus-base-change), both pointwise clauses and the proof via localized tensor products and 00MQ. Its structure-sheaf specialization has no finiteness hypothesis, and the reflection clause retains the indispensable flatness of the base map at the image point.

Step 1 uses the actual pointwise finite-presentation definition and the locally-finite-type affine cover definition, then the statement of `lem-weil-pbc-finite-presentation-over-finite-type-algebra`. I corrected an initial draft that implicitly treated the pointwise definition as an all-affine-charts theorem. The delivered step chooses a compatible basic open explicitly and gives the extra-variable equation presenting its localization; thus it does not invoke an unstated affine characterization.

Step 2 uses `lem-weil-pbc-openness-of-flatness` with B as base ring, C as finitely presented algebra, and M=C. Its statement gives precisely the open set of source primes where C_r is B-flat. I read `lem-weil-pbc-affine-open-stalk-localization`: clause (c) identifies both local rings, and the argument on fractions checks the map between them. I read `lem-weil-pbc-flat-over-localization`, whose equivalence identifies B-flatness of C_r with B_b-flatness; `def-weil-flat-morphism` then identifies this with the item's pointwise condition. The affine chart opens cover X; their union proves openness. This uses no Noetherian or separatedness assumption.

Step 3 uses `def-pc-scheme-fibre` for the correspondence of fibre points, and `def-pc-fibre-product` for the explicitly verified cartesian square. Clause (1) of the new pointwise base-change node gives f-flat implies fibre-flat. The new fibre criterion gives the reverse implication because p is flat at the point and the stated finiteness hypotheses hold. I did not try to infer the reverse solely from the general criterion's equivalence or assume that q is flat globally.

Step 4 reads the statements of `lem-weil-pbc-flat-morphism-base-change`, clause (3) of `lem-weil-pbc-qcqs-morphism-permanence`, and `lem-weil-pbc-lft-base-change`. These give respectively p_T flat, p_T locally finitely presented, and q_T locally finite type for arbitrary h. The quasi-compactness clauses elsewhere in the permanence node impose no extra hypotheses on its separate clause (3). The step cites both new pointwise prerequisites again, giving the fibrewise characterization over T directly.

Step 5 reads `def-weil-residue-field`, the entire statement of `lem-weil-pbc-fibre-of-base-change`, and the fibre-product universal property. Applying the fibre theorem to X and Y separately gives the two cartesian identifications. Their compatibility with f is checked by the projection equations and uniqueness, not an assumed extra naturality clause of the cited node.

Step 6 reads `lem-weil-pbc-field-extension-base-change-faithfully-flat`, with D equal to the smaller field. The tensor-unit isomorphism is written out. `def-weil-pbc-faithfully-flat-ring-map` expressly includes flatness; `def-weil-affine-spectrum` identifies the unique field-spectrum stalks; `def-weil-flat-morphism` identifies the scheme condition. The existing flat-morphism base-change theorem then makes the horizontal Y-fibre map flat. Both clauses of the new pointwise base-change node apply at the actual chosen fibre point, so fibre flatness is equivalent in both directions. Combining steps 3 and 4 yields equality of subsets, without a surjectivity assumption on T to S or any claim about points that have no lift.

I checked edge cases: empty X or T gives empty loci; f an identity has the entire source as flat locus; S a field reduces the equality to flat field-extension ascent/reflection at each lifted point; nilpotents and non-Noetherian bases are allowed throughout. The necessity of p-flatness can be tested with X=Spec k, Y=S=Spec k[t], f the origin and T=Spec k over the origin: f is not flat while f_T is the identity. This does not violate the item because p is then not flat. The same example shows why the new 047C reflection clause must retain base-map flatness. For the new fibre criterion, the empty source is vacuous and points always have nonzero local rings, meeting 039C's structure-sheaf nonvanishing requirement.

I checked B--E of delivery-errors against the files and the cited sources: statements introduce all objects and notions, new nodes have no proof sketch, sources give tags and exact labels, real searches are retained with actual results, no item clause has been hidden in a new node, and every non-elementary input is a node citation. I read all cited statements and generated citations.json from those exact statements. All steps are below 2000 characters. Existing off-unit generic tool uses are listed under split_report.tool_uses, without changing maintainer-owned tool_uses. No source or target statement was changed, and no statement dispute was found.

## Unfinished work

The two new prerequisites are deliberately unsplit, as required by the one-level stage-1 brief. Their independent future splits remain queued. There is no unfinished part of this item's natural-language proof.
