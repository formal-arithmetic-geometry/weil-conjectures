## What changed

Proved `AlgebraicGeometry.koszul_powers_orthogonal_of_orthogonal` in
`Sheaf.AlgebraicGeometry.KoszulPowersOrthogonality`, preserving its signature,
visibility, and existing docstring. Added the proof-only import
`Sheaf.AlgebraicGeometry.KoszulCoordinateMulTriangle`.

Added `Sheaf.AlgebraicGeometry.KoszulCoordinateMulTriangle`, proving
`AlgebraicGeometry.koszul_coordinate_mul_triangle` from a coordinate-cone
isomorphism and Mathlib's distinguished triangle of cones of composable maps.
The proof constructs the transported arrows and verifies their triangle.
Its only proof imports are the coordinate-cone module and Mathlib's homotopy
category triangulated module.

Added `Sheaf.AlgebraicGeometry.KoszulCoordinateConeIso`, stating the smaller
coordinate-cone identification. This is the sole unfinished algebraic step.
It has a source and a complete construction in words, including permutation,
exterior-power splitting, differential matrices, degree-zero behavior,
extension, and additive termwise sheafification.

The main theorem strongly inducts on the sum of the exponents. It proves the
positivity and strict sum inequalities for both modified exponent tuples,
identifies their powered generators by function extensionality, and applies
Hom exactness to the shifted multiplication triangle. No definitions or
existing statements changed; no forced adaptations or change records.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.koszul_powers_orthogonal_of_orthogonal`
(node `lem-pc-koszul-powers-orthogonality`). The assigned module has no remaining
`sorry`. Also proved the new theorem
`AlgebraicGeometry.koszul_coordinate_mul_triangle`
(node `lem-pc-koszul-coordinate-mul-triangle`).

Added exactly one hole:
`AlgebraicGeometry.koszul_coordinate_cone_iso`
(node `lem-pc-koszul-coordinate-cone-iso`), in its own new module. Its proof is
exactly `by sorry`. It asserts only a cochain-complex isomorphism for one scalar;
it has no orthogonality hypotheses, object E, positive-exponent tuple, or derived
category localization. The two complete combining proofs use it three times for
a, b, and a*b, then carry out the exponent induction and exactness argument.
This is a decomposition: one original hole closed, one lower hole added, net
zero holes, not an axiom-free proof of the original theorem yet.

All three delivery modules compile cleanly through `lcompile.py --all`.
Edge cases checked mathematically: the main induction includes an empty tuple
vacuously; the multiplication theorem eliminates a nonexistent coordinate at
r=0; the cone statement includes a one-element sequence at its r=0 and gives
the usual two-term scalar complex. Zero scalars, unit scalars and the zero ring
are consistent with the cone description. No regular-sequence assumption is
used. No object is defined by choosing a witness from an unproved existence
statement; all complex data are the existing explicit constructions.

## No longer needed

None of the assigned module's four original imports is removed. Its two original
proof dependencies remain the definitions used by its statement and proof.
No existing node or module can be pruned from this route. The newly proved
multiplication triangle needs only the scalar-cone identification and Mathlib's
cone-composition triangle, rather than a separately unproved Koszul product
triangle. No additional tensor, perfectness, quasi-coherence, or open-detection
module is imported. The existing tensor-cone coordinates remain a useful tool
for the next worker on the coordinate-cone isomorphism; they are recorded in
that node's proof plan, not claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The parent node's first non-elementary step named only definition nodes; none
stated the asserted multiplication triangle. The new nodes make this gap
explicit. Its second step also had no dependency for Hom exactness; that step
is now fully proved with Mathlib's `Triangle.yoneda_exact₂` and shift stability.

Local literature TeX files and blueprint section text are absent in this clone.
Read the unit record `sk-thm-picard-duality.json` and the primary Stacks pages
for Tags 09IR, 062C, 062B, and 0629. The unit has no realized nodes in its record;
this delivery retains the parent's route and changes no unit or chapter file.
Searches found no exact Koszul theorem in Mathlib or the source library.
LeanSearch returned an Internal Server Error, recorded as unavailable without
a mathematical verdict; LeanFinder, Loogle and local grep were also run.

## New nodes

`lem-pc-koszul-coordinate-mul-triangle` records the proved single-coordinate
multiplication triangle. It depends on the coordinate-cone isomorphism and
uses Mathlib's distinguished cone-composition triangle and the triangulated
localization functor. Its module is
`lean/Sheaf/AlgebraicGeometry/KoszulCoordinateMulTriangle.lean`.

`lem-pc-koszul-coordinate-cone-iso` records the sole new unfinished statement,
a cochain-level coordinate-cone isomorphism from Stacks Tags 0628/0629.
Its proof plan identifies the existing
`ExteriorAlgebra.exists_koszulTensorConeCoordinates` as a tool for the
last-coordinate matrix calculation. Its module is
`lean/Sheaf/AlgebraicGeometry/KoszulCoordinateConeIso.lean`.

No change records are needed: every existing interface stays identical.

## Second reading by T1

1. I compared the delivered `KoszulPowersOrthogonality` module with the repository
version. The theorem signature, visibility, and docstring are byte-for-byte unchanged;
the added import is proof-only. The two new modules and their declarations are new
nodes recorded in the DAG, so they do not alter an existing interface.

2. I compiled all three modules with `lcompile.py --all`. Compilation succeeds with no
errors. The only remaining `sorry` is the named theorem
`AlgebraicGeometry.koszul_coordinate_cone_iso`; it is a public split-off theorem with
the required source, proof plan, docstring, and DAG node. There are no definitions with
`sorry` and no forbidden declarations.

3. I checked the split-off statements against the coordinate-cone construction and the
standard cone-composition triangle. The cone isomorphism has exactly the data needed by
the multiplication theorem and no orthogonality or regularity assumptions. The
multiplication theorem has the exact three localized Koszul objects and distinguished
triangle required by the induction. Edge cases `r = 0`, zero scalars, and the zero ring
are handled by the statements or construction.

4. I reviewed the proofs from the target downward. The induction uses the multiplication
triangle and Mathlib's shifted distinguished-triangle exactness; the multiplication proof
uses only the coordinate-cone isomorphism, functorial scalar composition, and Mathlib's
mapping-cone triangle. No shorter existing declaration was found, and the unit route is
retained. The proof-dependency lists match these uses; no imports or nodes can be pruned.

5. I checked the new DAG nodes against their Lean declarations, including statements,
proof dependencies, source, and split status. The unit record remains unchanged because
this delivery realizes the existing route below the unit level.

I changed only the proof of the assigned theorem, added the two required theorem modules
and DAG nodes, and added this second-reading record. No existing statement or definition
was changed.
