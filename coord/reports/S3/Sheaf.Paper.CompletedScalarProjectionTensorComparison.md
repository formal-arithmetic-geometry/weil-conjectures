## What changed

Replaced the hole in
`AlgebraicGeometry.Scheme.completedScalarProjectionTensorComparison` by a complete
assembly proof. It constructs the tensor models from the existing native derived
tensor and uses the first clause of
`DerivedScalarMate.derivedScalarMateThickLocus`, which already identifies the scalar
mate with the tensor projection for arbitrary ring sheaves with literal
inverse-image coefficients. Two new statements isolate the remaining coefficient
transport arguments. No existing signature, definition, attribute or public import
is changed. The original module privately imports the two transport modules and
`RingedDerivedTensorNative`.

The Lean assembly composes the two scalar transport isomorphisms, the existing
scalar-to-tensor source/target isomorphisms, and the tensor transport isomorphisms.
It cancels the source inverse in the existing normalization equation and pastes
the two squares by associativity. It uses no projection invertibility.

Validation: `lcompile.py --all` compiled all three final Lean files cleanly:
scalar transport 13.0 s, tensor transport 8.8 s, assembly 16.9 s. The original
theorem signature, existing docstring and public imports were checked unchanged;
new node signatures and proof-dependency unions match the Lean and proof steps.

## Proved and sorry left

Closed the original named hole
`AlgebraicGeometry.Scheme.completedScalarProjectionTensorComparison` from two
strictly separate transport statements and the existing general normalization.
There are zero holes left in the item module.

Added two holes:

- `AlgebraicGeometry.Scheme.completedScalarMateCoefficientTransport`
  (`lem-pbc-completed-scalar-mate-coefficient-transport`). This is scalar and
  geometric coefficient conjugation, with no tensor or projection arrow.
- `AlgebraicGeometry.Scheme.completedTensorProjectionCoefficientTransport`
  (`lem-pbc-completed-tensor-projection-coefficient-transport`). This is tensor
  projection invariance under a coefficient isomorphism and an arbitrary
  coefficient-object isomorphism, with no scalar extension or scalar mate.

This is a decomposition, not a net proof gain: one hole closed, two added,
net -1 within the delivered files. Closure-wide figures belong to the project ledger.
The existing general normalization remains an imported project obligation;
its holes were neither copied nor added by this delivery. Both new theorem bodies
are exactly `by sorry`, with source, complete proof in words and matching nodes.
The private tensor model is a real construction from the native tensorator and
its proved representative comparison, with no witness chosen from mere existence.

## No longer needed

No existing public imports removed. No module is withdrawn or globally pruned.
The item no longer directly expands the ordinary extension/tensor comparison,
profinite coefficient inverse image, ring-sheaf adjunction comparison, or generic
tensor-pullback descent. These remain needed by the existing generic normalization
or by the two transport lemmas; they are not globally obsolete. Accordingly the
item's immediate proof dependencies are the two new transport nodes,
`lem-sfb-derived-scalar-mate-thick-locus` and
`lem-sf-ringed-derived-native-tensor`.

## Where the brief, the DAG or earlier work was wrong

The original plan overlooked the already stated arbitrary ring-sheaf normalization
in `DerivedScalarMateThickLocus`. Reusing it avoids another scalar/tensor or K-flat
normalization split. Its literal inverse-image coefficient convention does require
transport: neither the arbitrary target-ring isomorphism nor the constant-system
completed coefficient identification is definitionally that presentation.

The scalar-mate theorem from another unit is used as a generic ring-sheaf tool,
only its normalization clause; no constructibility, shift, thickness or stability
result is used, and the proper-base-change unit route is preserved. This generic
tool use is recorded for the maintainer's independent approval; no maintainer-owned
`tool_uses` field has been changed.

The current latest blueprint's direct-image-limits proof now concerns derived
completeness rather than the older finite-projection expansion. This delivery
preserves the currently landed Lean statement and its attachment and works on the
explicit scalar/tensor comparison still called by the landed parent. The source
for the comparison itself is the projection-map construction in Stacks 0B56 and
the existing general ring-sheaf normalization, not an assertion that the refreshed
blueprint includes the older expanded finite-level argument verbatim.

## New nodes

`lem-pbc-completed-scalar-mate-coefficient-transport`, module
`Sheaf.Paper.CompletedScalarMateCoefficientTransport`, records transport to the
literal inverse-image scalar mate, including the given ordinary-section and
derived-unit normalization hypotheses. Its helper `CompletedProjection.inverseObject`
is exact scalar restriction along the specified coefficient isomorphism. It
asserts no tensor identification.

`lem-pbc-completed-tensor-projection-coefficient-transport`, module
`Sheaf.Paper.CompletedTensorProjectionCoefficientTransport`, records the
coefficient-isomorphism tensor transport. Its input coefficient objects and their
isomorphism are arbitrary. The main proof supplies the degree-zero restricted
ring coefficient and the original r. Neither transport lemma is the original
scalar/tensor identification under a new name. Edge cases checked in their
mathematical statements: K=0, coefficient object=0, zero rings and empty sites;
all use the same equivalences and adjunction equations, with no nonzero or
faithful-tensor cancellation assumption. No change record is needed because no
existing shared interface changes.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
