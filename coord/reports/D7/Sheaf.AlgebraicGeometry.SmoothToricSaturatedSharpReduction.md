## What changed

Completed `AlgebraicGeometry.smooth_toric_saturated_sharp_reduction` in the item module without
changing its statement, its universe or any of its three definitions. The module now has the
required module header and exposed public section. The five new helpers are private and proved.
The import/header change is recorded in `coord/changes/D7-smooth-toric-proof-imports.md`.

The proof obtains regularity and local Noetherianity from smoothness, and integral closedness
from normal stalks and the existing local-to-global theorem. The existing affine monoid algebra
normalization statement supplies domains, the common fraction field and integral monomials.
Coefficient comparison then proves saturation. Sharpening exactness gives the unit kernel and
canonical quotient equivalence. Lifting a root in the sharp completion and correcting it by a
unit proves saturation of the sharpening directly. Applying this to an element and its inverse
proves torsion-freeness, and a finite integral basis gives the requested quotient lattice.
The existing fine-monoid unit-splitting theorem supplies the section and unit lattice.
`MonoidAlgebra.domCongr` and `curryAlgEquiv` construct the Laurent equivalence with its required
monomial formula, and `Localization.localRingEquiv` transports regularity.

The vertex calculation is proved here. Sharpness defines evaluation of the coefficient monoid
at its vertex; the Laurent augmentation sends the group exponents to one. The map kills the
specified ideal. Conversely, the standard exponent vectors become one in the quotient, hence
so do all their integer linear combinations. Induction on finite monoid-algebra sums shows
that the scalar map to the quotient is surjective, and evaluation gives its left inverse.
Its inverse is the residue algebra equivalence, and the quotient-field criterion gives
maximality. This argument includes trivial sharp monoids, rank zero and either empty family
of generators.

Read ILO VIII, Lemma 3.2.12(ii) and proof, printed pp. 104-105. Updated only the item's node
`proof`, `proof_deps` and `proof_origin` to reflect the implementation. All new proof dependencies
are existing statements in the same unit; no source-library module is modified.

Validation: `lcompile.py` compiled the item cleanly in 11.9 seconds, with no warnings, below
the 60-second limit. The delivery parser confirms zero changed existing statements, zero
removed declarations, zero new public declarations and zero remaining direct holes. All Lean
lines are at most 100 characters. There are no current direct importers to adapt or compile.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.smooth_toric_saturated_sharp_reduction`
(node `lem-trf-smooth-toric-saturated-sharp-reduction`). Added zero holes; no `sorry` remains in
any delivered Lean declaration. This is a proof from existing declarations, including the
previously stated normalization, sharpening-exactness and unit-splitting theorems, whose own
existing holes are not claimed closed by this delivery. No new nodes or split-off statements.

## No longer needed

Removed direct imports:

- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`: Mathlib supplies all monoid-algebra maps.
- `Sheaf.AlgebraicGeometry.RegularNormalDecomposition`: the existing upstream regular-stalk
  normality theorem supplies exactly the normality clause needed.
- `Sheaf.TraceFormula.FsFaceSharpening`: sharp saturation and the completion quotient are proved
  directly from sharpening exactness, avoiding transport through localization at units.
- `WeilConjectures.AlgebraicGeometry.Regular`: already publicly supplied by `IsRegularScheme`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: already publicly supplied by the statement imports.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: supplied by the local-properties import.
- `Mathlib.LinearAlgebra.FreeModule.PID`: supplied by the unit-splitting import.

Removed `lem-trf-fs-face-sharpening` from the item's proof dependencies: its face-localization
presentation is unnecessary. Removed the direct dependency on
`lem-trf-fine-monoid-unit-generators`: the existing unit-splitting statement supplies the unit
lattice. The latter lemma remains a transitive dependency of that statement, so it is not
claimed pruned globally. None of the statement dependencies or unit statements is withdrawn.
The normalization theorem replaces the original separate leading-term and integral-monomial
constructions, reusing existing declarations rather than creating new obligations.
No source-library declarations or modules are removed.

## Where the brief, the DAG or earlier work was wrong

No false mathematical statement was found. The original file had a legacy header despite the
required module format. The original DAG's unit-face sharpening step is mathematically valid,
but its declaration concerns `Associates (faceLocalization P F)`, requiring extra equivalences
to use it for `Associates P`. The exactness-based proof avoids those conversions. The original
unit-splitting construction and normalization argument already have stated library interfaces;
using those makes the proof shorter. The latest blueprint's curve-vanishing unit no longer
uses the historical toric ancestry, as already documented by this node's split report; this
delivery proves the assigned retained auxiliary statement and withdraws no parent.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
