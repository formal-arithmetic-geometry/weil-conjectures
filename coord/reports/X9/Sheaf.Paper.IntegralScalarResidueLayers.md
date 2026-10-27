## What changed

The assigned module now combines two strictly smaller residue-layer statements, one for
constructibility and one for vanishing outside the interval.  Its three explicit power
filtration declarations remain unchanged.  The two lower statements are in
`Sheaf.Paper.IntegralScalarResidueLayerConstructible` and
`Sheaf.Paper.IntegralScalarResidueLayerVanishing`; their proofs remain named obligations
with the finite-residue and local-model arguments documented in their docstrings.

## Proved and sorry left

The original `integralScalarResidueLayers_bounds` hole is closed by a real Lean proof that
applies the two lower clauses pointwise and pairs their conclusions.  The existing
`integralScalarPowerFiltration_antitone`, `integralScalarPowerFiltration_zero`, and
`integralScalarPowerFiltration_last` proofs remain complete.

Two strictly smaller holes are split off:

- `WeilConjectures.integralScalarResidueLayer_constructible`, in
  `Sheaf.Paper.IntegralScalarResidueLayerConstructible`;
- `WeilConjectures.integralScalarResidueLayer_vanishing`, in
  `Sheaf.Paper.IntegralScalarResidueLayerVanishing`.

Each lower theorem isolates one clause of the residue-layer argument and has a complete
source and proof description in its docstring.  No definition contains `sorry`.

## No longer needed

No existing public import or declaration is withdrawn.  The parent’s direct lower-level
proof dependencies are represented by the two new residue-layer clause modules.  The
DVR, finite-field scalar-extension, change-of-rings, and constructibility declarations
remain dependencies of those modules.

## Where the brief, the DAG or earlier work was wrong

The earlier finite-level delivery correctly left the residue-layer comparison as the
remaining mathematical step, but the single displayed conjunction hid two independent
claims.  The delivery separates those claims before the finite-filtration induction;
no target statement or protected unit step is changed.

## New nodes

- `lem-sf-integral-scalar-residue-layer-constructible`, module
  `Sheaf.Paper.IntegralScalarResidueLayerConstructible`.
- `lem-sf-integral-scalar-residue-layer-vanishing`, module
  `Sheaf.Paper.IntegralScalarResidueLayerVanishing`.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
