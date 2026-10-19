## What changed

Proved `AlgebraicGeometry.Scheme.finiteCoefficientRingIso_coherent` with its existing
statement and coefficient definitions unchanged. The private proved helper
`finiteCoefficientRingIso_comp` specializes the existing profinite coefficient
composition identity to the constant finite tower and cancels the intermediate
constants-to-functions isomorphism. Applying it to the two paths of the chosen square
reduces coherence to the square's commutativity equality.

The delivered change is confined to the assigned module. The other original theorem
and all public definitions and signatures are unchanged.

## Proved and sorry left

Original holes closed (1 of 2):
`AlgebraicGeometry.Scheme.finiteCoefficientRingIso_coherent`.

Original holes left (1):
`AlgebraicGeometry.Scheme.finiteLevelProEtaleBaseChange`, node
`thm-weil-pbc-finite-level-proetale`. Its existing docstring gives its source and proof.

New holes added: zero. This is a proof of coefficient coherence, with no decomposition
or new proof obligation. The closed proof uses the existing declaration
`proEtale_profinite_coefficient_inverse_image`, whose own dependencies are unchanged.

## No longer needed

Removed the following unused proof imports; none is needed by the delivered
coefficient-coherence proof or by the existing public statements:

- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`
- `Sheaf.Paper.CondensedAmbientExchange`
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`

This prunes imports from this module, not the unfinished proper-base-change argument:
its recorded DAG dependencies remain available to its next proof attempt. No DAG node
is withdrawn and no new module or node is delivered.

## Where the brief, the DAG or earlier work was wrong

The retained report claimed both original holes had been closed and described a new
coefficient-exchange lemma as the sole remaining hole. The actual retained files had
already moved that hole again, into `finiteFunctionCoefficientCompatibility`, and the
concrete exchange proof did not pass the current compiler: its generic mate application
caused a deterministic kernel timeout. That draft is preserved only in the scratchpad,
not delivered.

The broader attempt checked the fixed-scalar proper-base-change step and witness
transport, and constructed scalar restriction with its realization unit and equivalence.
It did not finish the comparison of the independently defined ringed exchange with the
fixed-scalar exchange. Finishing the remaining original theorem requires that normalized
comparison, including compatibility with the canonical derived composition comparison.
No target or intermediate statement has been weakened, and no definition is changed.

Validation: on resuming this retained sandbox on 2026-10-19, the actual pruned module
compiled through the project remote compiler in 6.2 seconds, with exit code zero.
Earlier dry runs passed; the required current dry run is being rerun before delivery.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
