## What changed

Proved `AlgebraicGeometry.Etale.finiteP1CoordinateKernel` in
`Sheaf.SmoothPurity.FiniteP1CoordinateKernel` with its existing signature and
public imports unchanged. Added private proof imports of
`Sheaf.AlgebraicGeometry.SfP1IntegralTransport` and
`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor`.

Explicit private graded polynomial renamings give inverse Proj morphisms and
an isomorphism of the two projective-line models over the arbitrary base S.
These constructions reuse the proved argument in SfP1CoordinateIntegrals,
without importing that affine-base theorem. Apply sfP1IntegralTransport to
the supplied splitting family, base-change equations and supported Ext witness
from hi. Its two comparison equations become identities by functoriality and
the two integral equations in hi. The coefficient isomorphism is the inverse
of the existing normalized shifted-line pullback. No positivity, affineness,
Noetherian, nonempty-base or nonzero-coefficient assumption is added.

The node proof now records this route through the existing comparison theorem.
No other existing module or node changes, and no new statement is introduced.
The local namespace opening and grading registration are documented in
`coord/changes/S1-finite-p1-coordinate-proof-commands.md`; these are elaboration
commands for the private construction and change no public definition.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.finiteP1CoordinateKernel`
(node `lem-sp-finite-p1-coordinate-kernel`).

Holes closed: 1 of 1. Holes added: 0. No sorry remains in the item or is added
elsewhere by this delivery. Existing downstream proof obligations inside the
imported transport theorem's dependencies are reused, not asserted closed.

## No longer needed

No existing Lean import is removed; both public imports support the unchanged
signature. No entire module is claimed globally prunable.

The item's direct proof dependencies no longer separately include
`def-sp-unbounded-proper-shriek-star-comparison`,
`lem-asd-ordinary-supported-kummer`,
`lem-kun-proper-base-change-torsion-ring`, or
`lem-sfb-ringed-derived-monoidal-comparisons`.
The existing theorem `lem-sf-p1-integral-transport` packages the necessary
support, exchange and coefficient comparisons. Those lower declarations may
remain needed transitively by its proof; they are not withdrawn or modified.

`Sheaf.AlgebraicGeometry.SfP1CoordinateIntegrals` is not imported: its theorem
requires an affine base and constructs its own family. Its explicit private
coordinate-isomorphism construction is sufficient here together with the
strictly more applicable existing transport comparison.

## Where the brief, the DAG or earlier work was wrong

The planned coordinate and support transport was already available in
`AlgebraicGeometry.Etale.sfP1IntegralTransport`, which takes an arbitrary base
and the supplied splitting family. The affine restriction on
sfP1CoordinateIntegrals therefore does not require another split of this item.
The original mathematical statement and the unit route are preserved.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
