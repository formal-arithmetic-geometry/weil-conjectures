## What changed

Proved the five existing theorem bodies of
`Sheaf.Paper.SemilinearFieldOperationLifts`, retaining every public signature and
all definitions. The covariant and tensor lifts reuse the adopted IsoAlgebra
transport. The partial Hom lift explicitly constructs the functor on the original
permitted pairs, with inverse structure in the contravariant variable.

The supplied-stage proof makes the specified ordinary mate and the specified
compactification composite invertible. The actual pullback comparison uses exactly
the canonical components stated in the module. Its rational naturality is tensor
induction, adapting the proved private argument in LocalFrobeniusWeilMorphismNaturality;
its common-stage naturality is a calculation on representatives. The final theorem
assembles the existing Cartesian square and the exact field-transport records,
then the canonical tensor and Hom comparisons. New helpers are private and proved. Explicit category instances keep representative
calculations folded; proof-context attributes prevent broad sheaf instance search.
The complete item compiles without warnings in 37.4 seconds via lcompile.py.

The current item source exists; no rework row or current return names this item.
All declarations and both node attachments are preserved. No module is withdrawn.

## Proved and sorry left

Five existing holes replaced, by declaration name:

- `WeilConjectures.pod_covariant_field_operation_lift`
- `WeilConjectures.pod_tensor_hom_field_operation_lifts`
- `WeilConjectures.pod_supplied_field_operation_lifts`
- `WeilConjectures.pod_actual_pullback_field_lifts`
- `WeilConjectures.semilinearFieldOperationLifts`

Zero holes remain in the item module. Zero holes added or split off.
The imported field-transport and comparison statements remain existing proof
dependencies; this delivery does not claim to prove them.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`
- `Sheaf.Paper.IntegralOperationsScalarComparisons`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`
- `Sheaf.Paper.FrobeniusCompactSupportExchange`

The direct dependency on `lem-pod-weil-frobenius-compact-support-exchange` is
unnecessary: the stipulated supplied-stage compactification exchange is itself
an invertible proper mate followed by the supplied open comparison. The theorem
preserves this exact composite. No deletion of that module, or of any adopted
source declaration, is requested.

The proof also does not need `lem-pod-frobenius-pullback-ordinary-exchange`
or its module: quotient-arrow induction and the published pullback representative
formula prove the compositor naturality directly. This is a dependency pruned
from this item only; neither module is withdrawn.

Removed obsolete tool approvals for
`lem-weil-proetale-isomorphism-inverse-image`,
`lem-pur-integral-operations-scalar-extension`,
`lem-weil-pbc-proetale-derived-pullback-composition`, and `fix-prop-adjunctions`.
The first is encapsulated by existing transport statements, the scalar compatibility
and representative action are already stated in the retained coefficient modules,
and the supplied adjunctions are fields of the operation stage. No unit statement
or realized unit step is bypassed; the unit record has no realization on this item.

## Where the brief, the DAG or earlier work was wrong

The Lean file predates the DAG's field-transport re-split. The proof now imports
and uses IsomorphismFieldTransport rather than rebuilding its coefficient theory.
FrobeniusPullbackOrdinaryExchange is not required: its square packaging is replaced
by a direct naturality calculation from the already specified compositors.
The generic supplied-stage conclusion already follows from its explicit equivalence and compactification fields.
The node proof is updated to match the actual argument. No mathematical statement,
definition, public import, target signature or consumer interface changes.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
