## What changed

Proved `AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_integer_twist_separation`
in `Sheaf.AlgebraicGeometry.ProjectiveBundleIntegerTwistSeparation`, with its original statement
unchanged. Added the proof-only import `Sheaf.AlgebraicGeometry.ProjectiveBundleFiberDegree`
and a proved private helper establishing invertibility of every integer power.

The proof factors the fibre inclusion at s through p⁻¹U using the range formula for a
scheme-theoretic fibre and the open-immersion lifting property. Tensor-pullback composition
then pulls the given isomorphism to that fibre. The existing fibre-degree theorem, applied
to the m-th power, equates both m and n with its unique exponent.

The changed DAG node records these steps and their actual dependencies. No other existing
module or node changes. `lcompile.py` compiled the module without errors or warnings in
5.1 seconds. The scheme, rank, normalized quotient, open, point and all integer exponents
are unchanged; the proof applies uniformly to negative and zero powers and nonreduced bases.

Searches through msearch (LeanFinder, Loogle and grep) found no Mathlib projective-bundle
integer-degree separation theorem. Repository inspection found the more directly applicable
`projective_bundle_fiber_degree`; this avoids reconstructing a field model here.
The current server queue marks this item `proof`, and there is no current rework or return.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_integer_twist_separation`.
No sorry remains in the item. No holes were added and no statements were split off.
The private helper `invertible_integerLinePower` is fully proved.
This is a proof from the existing fibre-degree declaration; its existing dependencies,
including the admitted fibre-twist-model theorem, are unchanged.

## No longer needed

No existing import was removed: the three original public imports supply statement data.
The originally planned proof dependencies
`lem-sfb-projective-bundle-local-normal-form`
(`Sheaf.AlgebraicGeometry.ProjectiveBundleLocalNormalForm`) and
`lem-sfb-locally-constant-line-twist-identities`
(`Sheaf.AlgebraicGeometry.LocallyConstantLineTwistIdentities`) are not needed by this proof
and are not imported. Unique fibre degree already encapsulates the field normalization
and integer-power compatibility; only pullback composition is needed here.
The node `lem-trf-projective-bundle-quotient-geometry` remains a statement dependency
through `TautologicalQuotient`, but its geometric conclusions are not used in this proof.
These dependency removals concern this item only; no module is withdrawn or claimed
unnecessary to all targets. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan calls for applying local normal form over the residue field and
separately commuting pullback with integer powers. The existing stronger fibre-degree
interface already gives uniqueness for the fibre pullbacks of the original integer
powers. Its direct use closes this obligation with no further splitting.
The existing statement is correct: the point hypothesis excludes the empty neighbourhood,
and r>=2 is precisely the hypothesis required for fibre-degree uniqueness.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
