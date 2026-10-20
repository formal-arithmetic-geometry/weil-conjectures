## What changed

Proved `AlgebraicGeometry.Scheme.Hom.smooth_zeroLocus_of_relativeDifferentialValue`
without changing its signature or `relativeDifferentialValue`.

The proof identifies the stalk kernel with the principal ideal of the local equation.
A functional detecting the residue differential gives a stalk derivation, so the algebraic
Kähler differential is nonzero. The tensor of the principal kernel is cyclic; its generator
has nonzero image under the cotangent map, making that map injective. Mathlib's
`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange` then gives formal smoothness
of the quotient stalk. Local finite presentation and the open smooth locus finish the proof.
Both private helpers are fully proved in this module. The stalk helper works with an arbitrary
sheaf derivation, avoiding repeated unfolding of the concrete sheafification; stricter
transparency and explicit additive/germ rewrites keep the clean compile at 13.0 seconds.

Added four private proof imports: `Mathlib.RingTheory.Smooth.Local`,
`Mathlib.LinearAlgebra.Dual.Lemmas`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, and
`WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier`.
The original public imports and public interface are unchanged. Updated the node and theorem
proof explanation to follow the argument actually implemented.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Hom.smooth_zeroLocus_of_relativeDifferentialValue`.
Added zero holes; zero `sorry` remain in the delivery. The existing definition
`relativeDifferentialValue` is unchanged. This is a proof, not a decomposition.

## No longer needed

No original imports were removed: the public import interface is preserved, including the
stalk module instances. No new Sheaf dependency module is imported and no module is withdrawn.

The explicit standard-smooth chart/Jacobian/localization route is unnecessary. These original
proof dependencies were removed from the node:

- `lem-pc-open-immersion-smooth-composition`
- `lem-weil-pbc-smooth-locally-standard-smooth`
- `def-weil-pbc-standard-smooth-algebra`
- `lem-weil-pbc-spec-tilde-stalk-localization`
- `lem-weil-pbc-affine-open-stalk-localization`
- `lem-weil-pbc-standard-smooth-kahler-basis`
- `def-weil-ring-localization-away`
- `lem-weil-pbc-standard-smooth-is-smooth`
- `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`
- `lem-weil-pbc-principal-localization-open-immersion`

Their former tool-use approvals were removed where obsolete. These are dependencies pruned
from this item's proof; no claim is made that other parents no longer use them.

## Where the brief, the DAG or earlier work was wrong

The longer Jacobian plan is mathematically sound, but unnecessary given Mathlib's local
cotangent criterion. No unit statement or unit proof step is bypassed: this node is a tool
below the unit, and its unit record does not list it as a realized statement or step.
The zero-scheme property's existing DAG attachment names an unrelated Picard theorem;
the actual local equation used here is `Scheme.Modules.Hom.ideal_zeroLocus`, together with
`Scheme.Modules.Hom.isLocallyPrincipal_zeroLocus`, in the already imported ZeroLocus module.

The nonvanishing assumption handles the degenerate cases: a zero equation or zero differential
cannot meet it. The argument requires neither a nonzerodivisor assumption nor flatness of the
zero scheme. The principal conormal tensor can have relations; cyclicity and a nonzero image
suffice for injectivity.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
