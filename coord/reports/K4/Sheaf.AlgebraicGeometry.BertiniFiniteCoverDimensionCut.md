## What changed

Filled `AlgebraicGeometry.exists_smooth_finiteCover_dimension_cut` with the single-cut
assembly, preserving its signature and all original public imports. The proof forms the
finite closed-point image of the prescribed rational sections, obtains a smooth linear
system in basis coordinates, applies the existing finite-cover irreducibility theorem,
intersects the two coefficient opens, and selects a rational coefficient tuple. The
private coefficient-point lemma is proved using Jacobson closed points, the algebraically
closed residue-field isomorphism, and polynomial ring-map extensionality. It also works
for zero variables.

The final argument converts pure dimension of the smooth connected member to its smooth
relative dimension and factors each original section through the closed immersion using
the proved field-point factorization theorem. No source-library module, target, existing
signature or definition was changed.

Added `Sheaf.AlgebraicGeometry.BertiniSmoothAffineLinearSystem` for the remaining paragraph-2
construction: the projective compactification, restriction of the existing high-twist
system, and reindexing into the exact coordinate interface used by the finite-cover
irreducibility theorem. This statement has no covering scheme and asserts no irreducibility
or connectedness for any member. Its sole hole is a whole public theorem with a source,
full proof plan and node. It is strictly the smooth-system input, not the assigned
finite-cover conclusion under another name.

## Proved and sorry left

Closed one of one assigned holes:
`AlgebraicGeometry.exists_smooth_finiteCover_dimension_cut`
(node `lem-zl-bertini-finite-cover-dimension-cut`). The private rational coefficient-point
helper is fully proved.

Added one hole:
`AlgebraicGeometry.exists_smooth_affine_prescribedPoint_linearSystem`
(node `lem-zl-bertini-smooth-affine-linear-system`). No other hole remains in the packet. Both delivered Lean modules compile with no errors
or warnings (single-file times 8.3 s and 9.9 s).
This is a decomposition: one upper hole closed and one strictly smaller smooth-system
construction left, net zero. The finite-cover application, parameter intersection and
rational-point selection, relative-dimension conversion, and section factorizations are
complete Lean arguments.

## No longer needed

Removed the new helper’s provisional import of the finite-cover irreducibility module;
its signature now imports only smooth-system notions. The assigned proof imports the
finite-cover theorem directly. No original public import is removed. Neither of the two original mathematical inputs is
pruned: the finite-cover irreducibility theorem is used directly, and the prescribed-point
smooth-system theorem remains the dependency of the new affine-coordinate interface.
The assigned node now cites that interface instead of directly citing the projective
smooth-system theorem. No module or declaration is withdrawn. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The shared source mirror initially lacked the assigned item even though its DAG record and
queue entry existed. There was no rework row or quarantine entry. The current source was
read from the project server and copied directly into the authorized sandbox; its signature
and docstring are retained.

The original plan correctly identifies the two geometric inputs but their existing Lean
interfaces do not directly fit: the smooth-system theorem requires a projective closure
and returns a basis indexed by an arbitrary finite type on the closure; the finite-cover
theorem takes sections of an invertible module on X and basis coordinates Fin r. The new
helper records precisely this omitted construction and conversion.

Edge cases checked mathematically: d = 2 gives relative dimension one; singleton S works;
positive characteristic is allowed; the identity cover causes no change; finite sets of
sections can collapse to closed points without losing the required factorizations. The
new smooth-system statement is independent of the cover and is valid for arbitrary affine
smooth connected X with the stated pure dimension. The parameter-point lemma also allows
r = 0. No statement is disputed.

## New nodes

`lem-zl-bertini-smooth-affine-linear-system`, in
`Sheaf.AlgebraicGeometry.BertiniSmoothAffineLinearSystem`, isolates paragraph 2 of the current
finite-cover-curve proof (Stacks 0FD5 and 0FD6): choose a compactification and high twist,
restrict its kernel basis to X, and present its smooth coefficient open in finite basis
coordinates. The original smooth-system node is retained as its proof dependency. Actual
LeanSearch, LeanFinder and grep searches found no existing affine-coordinate existence
interface; the existing smooth-system and arbitrary-family smooth-member statements were
read and require the construction this helper supplies. The blueprint search found no
separate duplicate.

Change record: `coord/changes/K4-bertini-dimension-cut-assembly.md`.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
