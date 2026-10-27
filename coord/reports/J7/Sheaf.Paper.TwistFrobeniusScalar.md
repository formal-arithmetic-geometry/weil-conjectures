## What changed

Filled six helper theorem proofs in `Sheaf.Paper.TwistFrobeniusScalar`, preserving
all existing declarations, their signatures, and all definition bodies. The sheaf
scalar comparison is the inverse canonical ordinary tensor-model comparison followed
by the existing normalized twist-line isomorphism. The least-stage embedding uses
the algebra equivalences from the small bottom intermediate field to the base field.
The two tensor comparison isomorphisms use actual ULift/tensor linear equivalences,
with naturality and uniqueness proved on pure tensors. The integral point sections
equality is proved by unfolding the existing unchanged-object operation wrappers.
Derived reduction follows from K-flatness of the locally free signed line and the
existing universal reduction counit, followed by the prescribed single-line map.

Added the proof-only import `Sheaf.Paper.IsomorphismComparisonScalarExtension` and
the flat-single normalization and reduction-counit imports, and recorded the helper
proof dependencies in the existing node. No target statement,
public import, definition body, coefficient comparison map, or normalization changed.

## Proved and sorry left

Original module: 10 named theorem holes. Closed 6; added 0; split off 0.
All following names are in `WeilConjectures.TwistFrobeniusScalar` and attached to
`lem-pur-twist-frobenius-scalar`.

Closed:

- `scalarSheafLine_existsUnique`
- `baseEmbedding_existsUnique`
- `coefficientModulesIso_existsUnique`
- `integralPointSections_eq`
- `localizationTensorIso_existsUnique`
- `reductionDerivedLine_existsUnique`

Remaining, with their original statements and complete proof docstrings retained:

- `scalarIntegralLine_existsUnique`
- `signedQuotients_existsUnique`
- `reductionSheafLine_existsUnique`
- `twist_frobenius_scalar`

These are existing holes, not newly introduced assumptions. The final scalar/action
assembly remains unfinished; this is a partial delivery closing genuine helper holes,
not a decomposition or a claim that the final Frobenius theorem is now proved.

Validation: all six changed proofs compiled individually through `lcompile.py`.
The complete item module compiled successfully in 56.2 seconds, under the unchanged
60-second limit. Delivery preflight is run by `deliver3.py`.

## No longer needed

None. No imports, nodes or modules are withdrawn. The final theorem still needs the
root-coordinate, point-transport, signed-action and coefficient-comparison route of
the existing DAG, so those dependencies and all existing imports are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction. The generic signed-reduction theorem needs
prime invertibility on the scheme, while the two ordinary quotient helper signatures
here do not take `hl`; it cannot simply be specialized to close them.
Mathlib already supplies the tensor/ULift
linear equivalences needed by the two coefficient-size helpers. The library also
already provides a proved ordinary-to-completed tensor-model comparison, so the
sheaf scalar helper needs no fresh root-basis construction. A first full-file proof
attempt timed out while typeclass inference tried to reconstruct the module action
on the lifted field; explicitly specifying that action and its scalar-tower law
resolved the isolated localization proof without raising the compile limit.
After adding the derived reduction imports, the earlier scalar sheaf proof also
unfolded its chosen witnesses too aggressively. Destructing the existing unique
existence theorems and using the exact isomorphism cancellation lemma keeps their
witnesses abstract. The proof body uses stricter `respectTransparency true` settings
to avoid expensive unfolding while leaving statement elaboration unchanged.
The complete six-proof module then compiled in 56.2 seconds. No transparency
check is disabled beyond the original file settings, and no definition changed.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
