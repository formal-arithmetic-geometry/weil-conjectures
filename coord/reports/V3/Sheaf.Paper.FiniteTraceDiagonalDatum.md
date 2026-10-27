## What changed

Proved the three finite-Tor preservation clauses and counit naturality in
`Sheaf.Paper.FiniteTraceDiagonalDatum`. Reduced unit naturality to canonical
contraction naturality and canonical self-square exchange naturality, composing
their equations with tensor naturality for the fixed diagonal class. The combining
proof is complete Lean, and no hypothesis or component formula changes.

Native pullback preservation, etale-origin tensor closure plus Tor/monoidal
comparison, native compact-support preservation with the fixed coefficient
quotient's invertible exponent, and comparison of the tensor unit provide the
three typing proofs. Counit naturality composes the projection, signed symmetry,
fixed-trace tensor and unitor squares.

Extracted the original generic canonical data verbatim into
`Sheaf.Paper.FiniteTraceDiagonalCanonicalMaps` and publicly reexported it from the
item. This avoids an import cycle for the two independent lower statements.
Every old name, signature, data body, attribute and public import stays; only
blueprint docstring identifiers of moved declarations point to the extraction
node. No definition repair from the earlier performance experiments remains.

Added proof-only imports of `Sheaf.Paper.FiniteDiagonalContractionNaturality` and
`Sheaf.Paper.FiniteDiagonalExchangeNaturality`, alongside native preservation and
comparison proof imports. The two lower statements each have their source and
complete proof in words. Both are strictly parts of the unit argument: neither
contains the datum trace or diagonal class, and neither states unit naturality.

The move and the consumer check are recorded in
`coord/changes/V3-finite-trace-diagonal-naturality.md`. There are zero existing
external importers, and no forced adaptation is needed.

## Proved and sorry left

Four original holes proved directly, under node `def-pur-td-datum`:

- `AlgebraicGeometry.ProEtale.FiniteTraceDiagonal.twisted_preserves`
- `AlgebraicGeometry.ProEtale.FiniteTraceDiagonal.shriek_preserves`
- `AlgebraicGeometry.ProEtale.FiniteTraceDiagonal.diagonal_inputs`
- `AlgebraicGeometry.ProEtale.FiniteTraceDiagonal.Datum.counit_naturality`

The fifth original hole,
`AlgebraicGeometry.ProEtale.FiniteTraceDiagonal.Datum.unit_naturality`, is closed
by a genuine decomposition into two smaller statements. It is reported as a
decomposition, not an additional completed proof of all its ingredients.

Zero holes remain in the item module and the extracted canonical-data module.
Two holes are added, exactly these public statements:

- `AlgebraicGeometry.ProEtale.FiniteTraceDiagonal.contractionCore_naturality`
  in `Sheaf.Paper.FiniteDiagonalContractionNaturality`, node
  `lem-pur-finite-diagonal-contraction-naturality`.
- `AlgebraicGeometry.ProEtale.FiniteTraceDiagonal.exchangeCore_naturality`
  in `Sheaf.Paper.FiniteDiagonalExchangeNaturality`, node
  `lem-pur-finite-diagonal-exchange-naturality`.

Thus five original holes close and two lower holes are added; four clauses are
proved and one decomposed. No hole is placed in a definition or private lemma.

## No longer needed

Removed private proof imports `Sheaf.Paper.PullbackTorAmplitude` and
`Sheaf.Paper.FiniteCoefficientTensorCtf`. Their nodes
`lem-sf-pullback-tor-amplitude` and `lem-sf-tensor-ctf` are no longer proof
dependencies of this item; their obsolete top-level tool approvals are removed
in order. Completed native pullback preservation and native etale tensor closure
with comparison replace those intrinsic wrappers. No module is withdrawn and
no adopted source declaration is removed.

All unit statements and realized proof steps remain. The maintainer can check
whether other target routes still need the two removed wrapper modules.

## Where the brief, the DAG or earlier work was wrong

The item began in quarantine under the current rework row, and was restored
from its archive. During work the shared checkout restored the same original
source to its live path. Its absence was never treated as withdrawal.

The planned intrinsic preservation declarations do not directly have the native
fixed-module signatures used here; the completed native API supplies a shorter
proof. Canonical contraction/exchange naturality is mathematically a composition
of naturality squares, but direct formal conversions repeatedly exceeded the
compile limit, even after profiling, isolating the contraction proof, using
abstract coefficients, and trying natural-isomorphism packaging. The delivered
reduction preserves the original canonical data and makes these two precise
remaining tasks independently available, with full proofs in words.

Identity morphisms, empty schemes, the tensor unit and zero datum arrows require
no additional hypothesis. No invertibility or nonvanishing assertion is inserted
into either lower statement, and no triangular identity is used.

## New nodes

`def-pur-finite-trace-canonical-maps` records the verbatim extraction of the
generic canonical constructions into `FiniteTraceDiagonalCanonicalMaps`; its
Lean declarations are moved from the original node's attachment to this node.

`lem-pur-finite-diagonal-contraction-naturality` records the first canonical unit
isomorphism's naturality for arbitrary maps between its original input objects.
Its proof is the five-square symmetry/projection/unit/pullback/section argument.

`lem-pur-finite-diagonal-exchange-naturality` records naturality of inverse
projection followed by inverse compact-support self-square exchange. Its proof
inverts the two native naturality squares and tensors the latter with the fixed
complex L.

Change record: `coord/changes/V3-finite-trace-diagonal-naturality.md`.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
