## What changed

Filled `WeilConjectures.TwistFrobeniusScalar.scalarIntegralLine_existsUnique`
in `Sheaf.Paper.TwistFrobeniusScalar`. The existing normalized ordinary derived scalar-model
comparison makes the specified scalar counit invertible by cancellation.
Its intrinsic completeness gives invertibility of the specified completion map.
Their inverse/composite with the existing normalized sheaf comparison constructs
the required isomorphism. Isomorphism cancellation proves its equation and
uniqueness. Existing declaration signatures, public imports and definition bodies
are unchanged.

Added the proof-only import `Sheaf.Paper.SfDerivedCompleteLegacyComparison`.
Updated the existing node `lem-pur-twist-frobenius-scalar` with this helper argument
and the existing dependencies it uses. No new node or intermediate assumption.

## Proved and sorry left

Original module: four named theorem holes. Closed one, added zero, split off zero.
Closed: `WeilConjectures.TwistFrobeniusScalar.scalarIntegralLine_existsUnique`.

Three existing holes remain, with their original statements and proof docstrings,
all attached to `lem-pur-twist-frobenius-scalar`:

- `WeilConjectures.TwistFrobeniusScalar.signedQuotients_existsUnique`
- `WeilConjectures.TwistFrobeniusScalar.reductionSheafLine_existsUnique`
- `WeilConjectures.TwistFrobeniusScalar.twist_frobenius_scalar`

This is a partial delivery closing a helper hole; the final Frobenius assembly
remains unfinished. The proof uses the existing declared normalized scalar-model,
completeness comparison and completion theorems, as intended by stage 3.

## No longer needed

None. No import is removed and no node or module is withdrawn. The unfinished
Frobenius theorem retains its root-coordinate, transport-normalization,
cyclotomic-action and coefficient-comparison dependencies. The added proof import
is used by the intrinsic-to-legacy completeness step.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction. The unrestricted completeness predicate
quantifies over an auxiliary finite-field datum in universe zero; the supplied D
has arbitrary universe u. Constructing an auxiliary prime distinct from l and its
finite-field datum avoids imposing an unintended universe equality.

The generic `signedTwistReduction_comparison` requires prime invertibility on the
scheme, while the two remaining quotient helper signatures omit hl. A direct
specialization cannot close them without another argument; their signatures are
preserved. The final scalar theorem is not replaced by a renamed assumption.

The shorter normalized scalar-model route avoids unfolding the generic K-flat
change-of-rings witness. Proved private helpers isolate the generic counit and completeness arguments.
A generic cancellation lemma avoids repeating expensive conversions between the
expanded categorical terms. Local irreducibility attributes prevent accidental
unfolding of the existing scalar choices within this module.
Validation: the complete module compiled in 51.1 seconds with profiling enabled.
The delivered source removes all profiling options and the temporary diagnostic
module. Three original `sorry` declarations remain; none was added.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
