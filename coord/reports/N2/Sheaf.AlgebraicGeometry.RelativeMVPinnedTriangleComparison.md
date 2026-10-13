## What changed

Replaced the hole in `AlgebraicGeometry.relativeMV_pinned_triangle_comparison`
with an explicit proof. It obtains distinguished image triangles and the raw
connecting equation from `derivedBaseChange_mayerVietoris_connectingSquare`.
The new vertex-comparison lemma supplies four isomorphisms, four first/second
arrow identities and the overlap mate identity, without asserting any boundary
or distinguishedness. The proof constructs the two boundaries, transports
both distinguishedness claims with `Triangle.isoMk`, proves the connecting square
by cancellation and associativity, and uses the existing restriction squares to
construct `Triangle.homMk`. All existing signatures and visibility are unchanged.
The node proof and proof dependencies now reflect this construction.

## Proved and sorry left

Closed: `AlgebraicGeometry.relativeMV_pinned_triangle_comparison`
(lem-pc-relative-mv-pinned-triangle-comparison), the sole original hole.
No sorry remains in the item module.

Added: `AlgebraicGeometry.relativeMV_pinned_vertex_comparisons`
(lem-pc-relative-mv-pinned-vertex-comparisons), in its own new module, with exactly
`:= by sorry`. This is a decomposition, not a net hole reduction: one hole closed,
one added. The existing connecting-square dependency is still sorry and is used
as intended by stage 3; it is not changed or added by this delivery.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris`
(lem-pc-rf-mv-triangle-naturality). This proof uses its earlier canonical
connecting-square interface directly, so the full raw triangle morphism,
its arbitrary adjunction witnesses, its middle component and projection equations,
and lem-pc-rf-mv-base-change-first-two-squares are unnecessary for this item.
Their modules may remain reachable through other targets; no global pruning claim
is made. The former direct proof edge to lem-pc-derived-mayer-vietoris-triangle
is unnecessary here; its content remains below the connecting-square theorem.
The pinned maps and pinned restriction-square dependencies remain required.

## Where the brief, the DAG or earlier work was wrong

The apparent shorter proof through `RelativeMVBoundaryCompletion` or
`RelativeMVCanonicalTriangles` is circular: boundary completion imports
RelativeMVSESPresentation, which imports RelativeMVConePresentation, which imports
this item. The import-direction tool refused that route. The new dependency goes
back to the earlier exact-restriction connecting-square theorem and does not
close this cycle. No existing statement or definition was changed.

The unit sk-thm-picard-semicon has no realized statement or step nodes in its
record; this is a refinement inside the existing relative Mayer--Vietoris route,
not a departure from a unit route. Blueprint searches for relative Mayer Vietoris
and Mayer found no duplicate vertex-comparison node. The ancestry helper did not
traverse this newly created item's ancestry; the new node uses the existing
cone-presentation node's recorded nearest blueprint ancestor.

The local literature files are absent on this machine. Read the source directly
at https://stacks.math.columbia.edu/tag/08BV,
https://stacks.math.columbia.edu/tag/08HZ and
https://stacks.math.columbia.edu/tag/08HY. The new comparison lemma is the
vertex/mate portion of those constructions, expanded in its docstring.

## New nodes

lem-pc-relative-mv-pinned-vertex-comparisons:
`lean/Sheaf/AlgebraicGeometry/RelativeMVPinnedVertexComparisons.lean`.
It supplies only comparison isomorphisms and identities between the canonical
exact-restriction rows and the pinned rows. It has no affine, qcqs, compactness,
cover, quasi-coherence, boundary or distinguishedness hypothesis or conclusion.
It is strictly part of the original argument; the distinguished boundaries and
their connecting equation come from an independent existing theorem, and the
triangle transport and assembly are proved in the item. Empty opens, equal opens,
zero objects, zero object maps, and arbitrary opens not covering X were checked
mathematically: the comparison formulas continue to apply, without an exactness
claim for an uncovered row. No new definition chooses arbitrary data.

## Second reading by N2

1. Compared the delivered triangle module with the repository version. The theorem statement and all existing declaration signatures are byte-for-byte unchanged; only proof imports, the proof, and its DAG proof metadata differ. The new vertex-comparison module and node are explicitly declared as additions.

2. Compiled both sandbox modules with `lcompile.py --all`; compilation succeeds without errors or warnings. The triangle theorem has only the expected `sorryAx` inherited from the split vertex-comparison and connecting-square dependencies; the new split theorem has `sorryAx` as declared. No `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition occurs.

3. Checked the split-off vertex-comparison statement and node. It is a strict intermediate comparison result, with no added cover, compactness, quasi-coherence, boundary, or distinguishedness assumptions or conclusions. Its docstring gives the source and construction, and its node records the matching statement, proof dependencies, and provenance. No duplicate declaration was found in the local library.

4. Read the proof from the target downward. It uses the canonical connecting-square theorem, the new vertex comparisons, and the existing restriction squares; it transports distinguishedness with `Triangle.isoMk` and assembles the triangle morphism with all three commutativity equations. The attempted route through boundary/canonical triangle completion is circular, so the earlier exact-restriction connecting-square route is the shortest available route. The old broad proof import was pruned.

5. The DAG proof steps, dependencies, and origin now match the Lean proof, and the unit route remains the relative Mayer--Vietoris route. The new node is marked split and tied to the same unit/chapter. No target or definition was changed.

Changed during second reading: no Lean proof or statement changes were needed; this report section records the checks. The delivery consists of the repaired proof, the split vertex-comparison module/node, and the pruned proof import as described above.
