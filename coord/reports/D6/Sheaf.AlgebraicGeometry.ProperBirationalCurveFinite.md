## What changed

Proved `AlgebraicGeometry.isFinite_of_isProper_birational_curve` in
`Sheaf.AlgebraicGeometry.ProperBirationalCurveFinite`, preserving its signature.
The surjective generic stalk map is finite by `RingHom.Finite.of_surjective`.
Apply the existing `quasiFiniteAtPoint_of_dominant_integral_curves`, convert its
pointwise Stacks condition with `Scheme.Hom.isLocallyQuasiFinite_iff`, then apply
`IsFinite.of_isProper_of_locallyQuasiFinite`. Properness supplies local finite type.
The comparison module is a private proof import. The existing DAG node now
records this exact argument. No definition or statement was changed.
Validated by `lcompile.py`: exit code 0, 5.9 seconds, no warnings.
The import-direction check permits the comparison import.

## Proved and sorry left

Closed one of one item holes:
`AlgebraicGeometry.isFinite_of_isProper_birational_curve`
(node `lem-trf-proper-birational-curve-finite`).
Zero holes remain in the item; zero holes added; zero split off.
The proof uses the existing, still-unproved
`AlgebraicGeometry.quasiFiniteAtPoint_of_dominant_integral_curves`
(node `lem-trf-birational-curve-quasifinite`) as authorized by stage 3.

## No longer needed

Removed the private `Mathlib.AlgebraicGeometry.Noetherian` import and the direct
proof dependency `lem-weil-pbc-finite-type-over-noetherian`: the existing curve
quasi-finiteness lemma directly accepts all the item's geometric hypotheses.
No separate Noetherianity construction is needed in this module.
Replaced the private `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`
import with `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison`,
which publicly imports those definitions and provides the needed comparison.
All public imports are preserved. No module was withdrawn and all other planned
dependencies remain in use. The removed direct dependency can remain necessary
elsewhere, including within the curve lemma's proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The DAG's separate Noetherianity step
is redundant when applying its already-stated curve quasi-finiteness dependency.
The Stacks-to-Mathlib comparison theorem lives in
`WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison`, rather than the
definitions-only module imported before this change. The unit route is preserved;
no unit statement or proof step is bypassed. No return or rework entry applied.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
