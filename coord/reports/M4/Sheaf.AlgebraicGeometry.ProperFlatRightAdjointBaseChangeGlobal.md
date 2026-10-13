## What changed

The existing signature of
`AlgebraicGeometry.proper_flat_rightAdjoint_baseChange_global` is unchanged.
Its proof now chooses affine V around g(f'(x)), affine W inside g⁻¹(V) around f'(x),
and applies the chart assertion to the open f'⁻¹(W) containing x. Ambient derived
locality then gives the global isomorphism; the fully faithful D_QCoh inclusion
reflects it. This is a reduction with the covering and descent argument proved.

Added `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart`, stating the
single-chart portion of Stacks Tags 0AAB/0E9S. Its conclusion is an isomorphism
only after restriction to the particular preimage of W; it has no global or cover
conclusion. The existing affine-case hypothesis remains explicit and unchanged.
The source supplies compatibility under pasting and the open-unit comparisons.

Added `Sheaf.AlgebraicGeometry.DerivedOpenRestrictionDetectsIso` with a complete
proof of the pointwise-neighbourhood criterion. It uses the source library's
proved `mapDerivedCategoryHomologyFunctorIso`, the proved sheaf-module open-cover
criterion, and Mathlib `DerivedCategory.isIso_iff`. The cover is indexed by all
opens on which the morphism is invertible, so no arbitrary data are selected from
an unproved existence theorem. It applies to empty schemes, arbitrary complexes,
and morphisms with non-quasi-coherent cohomology as well.

All three modules compile in sandbox import order without non-sorry warnings.
The node route is updated to the chart assertion followed by derived locality.
No definitions, public imports of the existing module, or target signatures change.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.proper_flat_rightAdjoint_baseChange_global`
(node `lem-sc-proper-flat-right-adjoint-basechange-global`).

Added one hole:
`AlgebraicGeometry.proper_flat_rightAdjoint_baseChange_chart`
(node `lem-sc-proper-flat-right-adjoint-basechange-chart`). Its complete proof
in words and source are in the declaration docstring and node. This is a
one-for-one decomposition, not a net reduction in the closure's hole count.
The original module has no remaining sorry.

The new theorem `AlgebraicGeometry.schemeDerived_isIso_of_openRestriction`
(node `lem-sc-derived-open-restriction-detects-iso`) is proved with no sorry.
There are no other added holes and no holes in definitions or private declarations.

## No longer needed

No existing DAG node or module is pruned from the target closure.
The original direct proof import of
`Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen` is replaced in
the global module by imports of the chart and locality modules. It remains a
needed dependency of the chart obligation; this is a relocation, not pruning.
The source library's homology comparison is reused instead of adding a duplicate
comparison construction. No separate holed locality theorem remains.

## Where the brief, the DAG or earlier work was wrong

The old node grouped chart restriction, mate compatibility, applying the affine
hypothesis, constructing the cover and descent into one step. The stated dependency
`proper_flat_rightAdjoint_restriction_open` only supplies invertibility of the
restricted open-unit maps; its signature does not itself compare the global
canonical base-change mate to the chart mate. That glue is isolated in the chart
obligation rather than treated as a directly applicable lemma.

A public two-open derived criterion already exists, but uses derived categories
on over-sites rather than the open-subscheme family in this item. The exact
arbitrary-cover detection argument also appears in private helpers of
`RelativelyFlatCanonicalModuleBaseChange` and `PerfectDirectImageBaseChange`.
Their proved homology and sheaf-locality inputs are reused here.

The local literature tree contains only metadata on this machine. The cited
primary source was read at https://stacks.math.columbia.edu/tag/0AAB,
https://stacks.math.columbia.edu/tag/0E4J and
https://stacks.math.columbia.edu/tag/0E9S. No source was invented or weakened.
LeanSearch returned Internal Server Error; LeanFinder, Loogle and source grep
were used and the unavailable service is recorded without a mathematical verdict.

## New nodes

`lem-sc-proper-flat-right-adjoint-basechange-chart` is the strictly local chart
portion of the original argument. Its single remaining hole preserves the
proper-flat open-restriction dependency and the same affine-case hypothesis.

`lem-sc-derived-open-restriction-detects-iso` is the proved generic descent step.
It depends on the existing proved sheaf locality node, used as a generic tool.
Both new nodes inherit the original chapter and unit, and the unit's realized
route is unchanged. There are no change records or forced adaptations.

## Second reading by M4

1. Compared the existing module with the repository by diff and compared its entire
   theorem signature byte for byte, through the proof delimiter. Verdict: unchanged
   after removing an accidental extra space before `:=`. All existing public imports,
   visibility and docstring remain unchanged. No definitions or other existing modules
   are changed, so no change record or forced adaptation is needed.
2. Compiled all three modules locally in import order using lcompile.py. Scratch copies
   with `#print axioms` show only propext, Classical.choice and Quot.sound for
   schemeDerived_isIso_of_openRestriction; the chart and global theorems also show
   sorryAx. Scanned all delivered Lean files: precisely the named chart theorem has
   `sorry`; no forbidden declaration or hollow definition is added. Verdict: valid
   conditional reduction, not an axiom-free proof of the original hole.
3. Read the chart docstring, its node and the restriction dependency. Checked Stacks
   Tags 0AAB, 0E4J and 0E9S directly: the last explicitly compares the restricted
   global map with the chart map, and proper flatness supplies the needed open
   comparisons and Tor independence. Empty charts, the identity square and arbitrary
   unbounded K cause no missing hypothesis. The chart assertion is strictly the local
   comparison/application step, without the covering and descent step; it is not the
   original global conclusion under another name. Repeated LeanFinder, Loogle and
   Mathlib grep searches with different queries and searched the repository by rg.
   No exact public duplicate was found. The existing two-open criterion uses over-site
   categories; the arbitrary-cover helpers are private. Verdict: true and appropriate
   split with a sourced proof in words; closing it requires formal restriction/mate
   comparison infrastructure and is not a few-minute repair.
4. Read the proof top down: two affine-neighbourhood choices, the single-chart
   assertion, the proved homology/sheaf-locality criterion, and reflection by the
   fully faithful inclusion. The locality cover indexes all good opens and selects
   no data from unproved existence. Checked all imports against signatures and proof
   uses; proof-only imports are non-public. The sole old proof dependency is retained
   by the chart module, so No longer needed correctly reports relocation and no
   pruning. Read dag/units/sk-thm-picard-duality.json; its realized route is unchanged.
   Verdict: the unit route and the shortest available descent route are preserved.
5. Compared all node proofs, proof_deps and proof_origin with the declarations and
   proof bodies. Verified the new nodes' sources, complete statements, creation,
   blueprint, chapter/unit and verbatim Lean signatures. The original dependency
   remains below the chart node and the generic locality input is marked as a tool.
   Verdict: consistent. Added the independent locality search to its node record.

Second-reading changes: restored exact signature whitespace; recorded the independent
search and this review. No proof repair, added hole, removed hole or pruning was needed.
The original hole is closed conditionally by the one split chart hole, as already
reported: one-for-one decomposition with zero net holes closed.
