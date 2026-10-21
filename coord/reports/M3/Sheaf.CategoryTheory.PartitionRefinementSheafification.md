## What changed

Filled `CategoryTheory.bijective_toSheafify_of_partition_refinement` in
`Sheaf.CategoryTheory.PartitionRefinementSheafification`, preserving its full signature,
public imports and existing docstrings. Added one proved private helper
`covering_refinement`, by induction on the generated topology, using exactly
`Precoverage.IsSiteForCoverings`. Its proof reuses the argument already present in
`Sheaf.CategoryTheory.BoundedConstantChainMapLocal` and `Sites.FpStalkRealization`.

Replaced the private proof import of
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal` by
`Mathlib.CategoryTheory.Sites.Equivalence`, with private imports of
`Mathlib.CategoryTheory.Comma.StructuredArrow.Small` and
`Mathlib.CategoryTheory.Limits.EssentiallySmall` for limits on the small-model
comparison comma categories. Mathlib local injectivity and local
surjectivity, transported from the small model into `Type (max u v w)`, give covering
sieves of local equality and local lifts. The helper extracts actual covers to which
`hrefine` applies. The product bijection proves injectivity and assembles lifts for
surjectivity; sheaf separatedness along the component cover completes surjectivity.
Naturality is evaluation of `toSheafify_naturality`.

Updated the existing node's proof, proof dependencies and proof origin to describe
this implementation. No definitions, target statements or source-library modules change.
The unit route is unchanged. The delivery compiler verified the proof;
final warning cleanup explicitly references the three retained, unused hypotheses
without changing their binder names or types.

## Proved and sorry left

Closed: `CategoryTheory.bijective_toSheafify_of_partition_refinement`
(node `lem-zl-partition-refinement-sheafification`), 1 of 1 original holes.
Added holes: none. Sorries left in the item and delivery: zero.
The private helper `covering_refinement` is also proved.

Edge cases: the proof uses function extensionality and the product bijection even for
`Fin 0`; the empty product supplies a section and separatedness on the empty cover
supplies equality. No inhabitedness of a covering index set or section set is assumed.
For a singleton decomposition the same argument applies. Initial objects require no
separate branch. The original extra disjointness, stability and empty-value hypotheses
are retained verbatim, although the direct proof does not need them.

## No longer needed

Removed proof import:
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`.
Removed proof dependency: `lem-weil-pbc-site-sheafification-sections-local`.
This item uses Mathlib local bijectivity and the proved cover-extraction helper instead.
No other dependency nodes or public imports were removed. No modules are withdrawn;
the removed dependency may remain needed by other parents.

## Where the brief, the DAG or earlier work was wrong

The planned application of `CategoryTheory.sheafification_sections_local` does not
fit the item's hypotheses: that theorem requires indexed stability under composition
and stability under all choices of base change, whereas `IsSiteForCoverings` supplies
bind composition and existence of covering pullbacks. It also fixes the set universe
to the maximum of the site universes. The item allows a further value universe `w`.
Neither stronger site axioms nor a universe restriction was added: induction on
`Precoverage.Saturate` extracts actual covers under the given axioms, and Mathlib's
`WEqualsLocallyBijective.ofEssentiallySmall` handles the larger value universe.

The local-equality/local-lift descriptions in the preserved original docstring should
be read via this direct Mathlib implementation rather than as a literal invocation
of the stronger theorem. The updated node and the proof comment record that distinction.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
