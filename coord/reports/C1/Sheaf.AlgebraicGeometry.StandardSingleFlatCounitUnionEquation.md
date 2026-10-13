## What changed

Replaced the sorry in `AlgebraicGeometry.standardSingleFlatCounitUnionEquation` by a
proof of the remaining categorical argument, with its signature unchanged. Added
`Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionTriangles`, which states only
Steps 1 and 2 of the original plan: the canonical Mayer--Vietoris diagram, with its
literal union, member and overlap comparison maps. Its triangle vertices and all
three component equalities are specified; it does not assert invertibility of the
union map or any factorization at a supplied complex.

The original module proves invertibility of the middle component by identifying it
with `biprod.mapIso` of the two local isomorphisms. Mathlib's
`Pretriangulated.isIso₁_of_isIso₂₃` then proves invertibility of the union comparison.
The existing bounded-flat K-flat theorem and `SingleComplexBaseChange.counit_isIso_kFlat`
prove invertibility of the pinned counit at the supplied K. Compose `mapIso e` with
that counit, and compose its inverse with the canonical union comparison. Cancellation
proves the required equation for exactly the supplied K and e. Proved private
biproduct, equality-transport and factorization helpers keep the geometric vertices
out of the generic isomorphism calculations.

Updated the original node's proof, proof dependencies and proof origin to this argument.
No existing definition, statement or public import changed. All work is in the item
sandbox; delivery is a dry run only.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.standardSingleFlatCounitUnionEquation`
(node `new-pc-standard-single-flat-counit-union-equation`), by reduction to the named
triangle-construction step and the existing bounded-flat and pinned-counit lemmas.
The item's module has no sorry left.

Added exactly one hole: `AlgebraicGeometry.standardSingleFlatCounitUnionTriangles`
(node `new-pc-standard-single-flat-counit-union-triangles`). Its proof is exactly
`by sorry`, with a complete construction in its docstring and node. This is a
one-hole-for-one-hole decomposition, not a net sorry reduction. It leaves the
geometric triangle construction and local comparison identifications; the biproduct
argument, triangle two-out-of-three, computation at the supplied K and inverse
factorization are proved in Lean. No new data construction uses a holed existence
statement, and the witnesses are destructured only in a theorem proof.

## No longer needed

Removed these proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation`:
  `lem-pc-kinjective-mayer-vietoris-presentation` remains a proof dependency of the
  new diagram node; it is not globally pruned.
- `Sheaf.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare`:
  `lem-pc-mayer-vietoris-underived-open-counit-square` remains a proof dependency
  of the new diagram node; it is not globally pruned.
- `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`:
  `lem-pc-flat-complex-derived-pullback` is no longer needed on this route.
  Its indirect existential comparison is replaced by the existing direct APIs
  `CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace` and
  `SingleComplexBaseChange.counit_isIso_kFlat`, which already computes the pinned counit.

No new union complex, no cone flat replacement, and no alternative choice of e is
needed for the equation. The separately assigned union-core item remains needed by
its caller; it has not been imported or changed here. None of the compact-open
`RelativeMayerVietoris`, `RelativeMVCanonicalTriangles`,
`DerivedBaseChangeMayerVietoris`, or `SingleComplexOpenUnionTriangles` modules is
imported; their compactness assumptions cannot be discharged for the arbitrary
opens in this statement. No additional global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original unrestricted signature has no compactness assumptions on U, V or their
intersection, or on the union morphism. The existing relative Mayer--Vietoris
naturality theorems impose these extra assumptions and cannot implement Step 2 as
written. The general K-injective presentation and underived counit square do not
impose them, but stop before the needed derived triangle diagram and boundary
identification. The new node isolates that missing construction rather than adding
compactness to the original statement.

The general `standard_flat_single_baseChange` theorem cannot be imported: the import
direction tool reports that it already reaches this item. The same cycle occurs for
`RelativeMayerVietoris`. This is why the proof uses the original downward route.

The ordinary-to-derived comparison in `flatComplexDerivedPullback` is existential
and not immediately the pinned counit. The existing public `counit_isIso_kFlat`
proves precisely the needed uniqueness transport, so that part does not need a
new lemma or a copy of its proof.

Mathlib searches: Lean Finder returned generic sheaf gluing and short complex
results; Loogle found the triangle two-out-of-three lemma used in the parent;
Mathlib grep found generic Mayer--Vietoris square/cohomology infrastructure. LeanSearch
returned Internal Server Error, recorded as unavailable, without an absence verdict.
Read the related library signatures and DAG nodes before making the new statement.

## New nodes

`new-pc-standard-single-flat-counit-union-triangles` is the exact geometric diagram
needed before the two-out-of-three step, in the same chapter and unit as the item.
Its single new module and theorem give the actual local tensor restrictions, both
triangles, all three component equations, and local invertibility. The source is
Stacks Tags [0DJ9](https://stacks.math.columbia.edu/tag/0DJ9),
[08BV](https://stacks.math.columbia.edu/tag/08BV) and
[08FE](https://stacks.math.columbia.edu/tag/08FE), read on 2026-10-14.
Tag 0DJ9 states the compact-open induction diagram; the extension to arbitrary
opens here uses the general sheaf-module triangle of 08BV, whose hypotheses have
no compactness requirement, as the original item's docstring prescribes.

Edge cases checked before stating it: empty members give zero vertices and the
remaining restriction comparison; repeated or nested members give the split
restriction-difference short exact sequence; N = 0 gives zero comparisons.
No nonempty-open or nonzero-object hypothesis is introduced. The unit record's
`realized` lists are empty, and the existing relative Mayer--Vietoris route stays.
There are no change records or forced adaptations.

## Second reading by C1

1. Compared the delivered equation module against the repository version. The public theorem signature is byte-for-byte unchanged; only proof imports and proof text changed. Verdict: pass.
2. Compiled both delivered modules with lcompile.py. The equation has no sorry, and the only remaining sorry is the named split theorem `standardSingleFlatCounitUnionTriangles`; no forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. Checked the split theorem statement and node against the Lean declaration. It is a genuine, strictly simpler triangle-construction lemma, with source, proof description, and edge cases documented. Verdict: pass.
4. Checked the proof route and imports. The route uses the new triangle node, the existing bounded-flat K-flat and pinned-counit results, and Mathlib two-out-of-three; the removed flat-complex-derived-pullback import is unused. Verdict: pass.
5. Checked DAG proof, proof_deps, proof_origin, and the unit route. The equation node records exactly the declarations used, and the new triangle node records its own dependencies; no unit realized route is bypassed. Verdict: pass.

Changed during second reading: added this review section only; no Lean or DAG content was altered.
