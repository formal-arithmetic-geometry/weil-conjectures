## What changed

Proved `WeilConjectures.ConstructibleExceptionalCoefficients.ring_refinement_scalar_word`
without changing its statement or public imports. The proof identifies each supplied
normalized open component with the canonical refinement map, inverts its scalar square,
transports the input along `e`, and pastes the outer proper-composition square.

Added two proved auxiliary modules. `Sheaf.Paper.ProperScalarComposition` proves
`properComparison_inverse_composition` by taking geometric mates of scalar/pullback
composition coherence and cancelling the proper compositors. Its private mate
identification reuses `geometric_scalar_mate` from `IntegralFiniteProperMate` through a
proof-only `import all`.

`Sheaf.Paper.RefinementOpenScalarSquare` proves `refinementOpenMap_scalar`. It extends
refinement restriction to all derived modules, proves its scalar naturality using the
proper counit and pullback-composition identities, and applies the generic
`coefficient_refinement_of_restriction` from `ProperOpenCoefficientRefinement`.
The required inverse open-unit identity follows from `coefficientOpen_unit` in
`IntegralOpenScalarUnitSquare`; these private helpers are accessed by proof-only imports.

The item assembles these identities through private generic categorical lemmas and
`comparison_factorization`. Destructing the compactification records and eliminating
their triangle equalities keeps the equality transports reflexive during kernel
checking. No existing definition, instance, attribute, public import, target statement,
or other existing module is changed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.ConstructibleExceptionalCoefficients.ring_refinement_scalar_word`.

Added no holes. Both new public auxiliary theorems,
`WeilConjectures.PurCompactSupport.properComparison_inverse_composition` and
`WeilConjectures.PurCompactSupport.refinementOpenMap_scalar`, are proved.
Every private helper is proved. No delivered file contains `sorry`, and no data is
chosen from an unproved mere existence theorem. Existing dependency declarations
are used as permitted by stage 3; this does not claim to close their obligations.

Validation: the final sandbox compiled in import order without warnings: proper scalar
composition 9.6 s, inner open scalar square 27.4 s, and the item 18.6 s. All are below
the 60-second limit. No compile limit was raised and profiling options are removed.

## No longer needed

The item's old planned proof dependencies are not used:

- `lem-sf-system-proper-open-scalar-square`, module
  `Sheaf.SixFunctors.SystemProperOpenScalarSquare`;
- `lem-sf-integral-compactification-system-realization`, module
  `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`.

They are removed from this node's proof dependencies. They are not withdrawn from the
library: other consumers may still need them. No module is deleted. The original file
had no private proof imports to remove. The new proof needs neither a finite integral
basis, ramified reduction systems, cofinal realization nor finite-level detection of
equality. The unit record's realized statement and proof steps are untouched.

## Where the brief, the DAG or earlier work was wrong

The DAG planned a system-level argument followed by realization. The refinement-word
identity follows directly from ordinary derived adjunction identities. No extra absolute
separatedness assumption on X or Y is needed. The superficially similar
`comparison_refinement` theorem has stronger absolute hypotheses and is not used;
only its generic categorical helper is reused. The existing target docstring describes
the former route; its text is preserved.

At startup the shared item was quarantined for an unavailable `RingOpenRefinement`
import. The live snapshot subsequently restored both sources and removed the rework
row; the current queue lists the original one-hole proof obligation. This delivery
preserves the restored item and its Lean attachment. No quarantine file is deleted.

## New nodes

`lem-sf-proper-scalar-composition` records the inverse proper-compositor coefficient
identity, proved from inverse scalar/pullback coherence by geometric mates. It is valid
for arbitrary coefficient systems and arbitrary scheme maps, including identities.

`lem-sf-refinement-open-scalar-square` records the inner forward open-refinement
square, proved by transposition under the open adjunction, coefficient naturality of
the restriction transformation, and cancellation of that invertible restriction.
Empty opens, identity refinements and zero objects satisfy the same calculation.

No change record is required: the delivery changes only the item's proof and node,
and adds two proved auxiliary modules with their nodes.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ProperScalarComposition": "b210f2942df7d67cc70467223ab96a5aab3185a0", "Sheaf.Paper.RefinementOpenScalarSquare": "ad0b833b92cc782d8495b6ca37dc8523aeb25ce5", "Sheaf.Paper.RingRefinementScalarWord": "9d74f5273331b7db8762dbcbccd1515cb23ff34b"}, "results": {"Sheaf.Paper.ConstructibleRingLeftRefinement": {"hash": "c6962d01f0cc3a8929471d26a8bcf99ede72ba08", "status": "OK"}}, "seconds": 40, "time": "2026-10-28T05:35:12+0800", "transitive": 0, "version": 1}
```

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
