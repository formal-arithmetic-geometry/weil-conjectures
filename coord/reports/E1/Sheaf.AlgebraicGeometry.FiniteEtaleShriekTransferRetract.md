## What changed

Proved `AlgebraicGeometry.Etale.exists_finiteEtale_shriek_transfer_retract` in
`Sheaf.AlgebraicGeometry.FiniteEtaleShriekTransferRetract`, preserving its complete signature
and all public imports. Added only proved private helpers and private proof imports.

The trace is the counit of the existing finite-etale reverse adjunction. The private
`exists_trace_algClosed` adapts the already proved stalk argument in
`WeilConjectures.AlgebraicGeometry.FiniteEtaleModuleTraceData`: the unit is diagonal, the trace
is the sum, and their composite is multiplication by the geometric fibre cardinality.
It uses the assigned algebraically closed degree hypothesis directly. The private
`primary_unit_split` normalizes this trace by the integer Bezout coefficient, using only
annihilation of the sheaf and coprimality.

For the comparison isomorphism, finite direct image is already proved exact with ModuleCat
coefficients. Identify extension by zero along the identity with the identity using the
existing adjunction comparison, apply the specialized exact-derived API, and use the proved
qcqs shriek composition comparison for the three prescribed compactifications. Transport
both sheaf maps through these functors and conjugate by the comparison isomorphism.
The final identity follows from functoriality and the sheaf-level splitting.

Updated the assigned node's proof, proof dependencies, proof origin and obsolete tool-use
entry to match this route. No other module, statement or definition was changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.exists_finiteEtale_shriek_transfer_retract`
(blueprint: `lem-weil-pbc-finite-etale-shriek-transfer-retract`).

Added 0 holes; split off 0 statements. The assigned module contains zero `sorry` occurrences.
All four private helpers are proved. No new axioms or definitions were introduced.
The proof compiled through `lcompile.py`; delivery runs the final compile and axiom probes.

## No longer needed

Removed the following private proof imports and their direct planned dependency edges:

- `WeilConjectures.AlgebraicGeometry.FiniteEtaleModuleTraceDegree`, node
  `lem-weil-pbc-finite-etale-module-trace-degree`: its public statement asks for degrees over
  every separably closed field. The proved private stalk argument uses exactly the given
  algebraically closed degree hypothesis, via `finiteEtaleUnit_stalk_inclusion` and the
  finite stalk formula. The source declaration is preserved in the library.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`, node
  `lem-weil-pbc-module-sheaves-colimits-forgetful`: coefficient lifting is unnecessary because
  the finite-direct-image exactness instance already accepts ModuleCat coefficients.
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`, node
  `lem-weil-pbc-module-direct-image-left-exact`: the same existing exactness instance avoids
  the proposed change of coefficient category. Removed this obsolete top-level `tool_uses`
  approval from the assigned node.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`, node
  `lem-weil-pbc-exact-functor-derived-functor`: the proved source specialization
  `rightDerivedFunctorPlusIsoMapDerivedCategoryPlus` supplies the required comparison
  directly, together with `mapDerivedCategoryPlusSingleFunctor`.

These dependencies are unnecessary for this item's proof. No module is withdrawn and no
claim is made that other consumers can prune these source declarations or their imports.
The unit statement and realized unit steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original step 3 proposed lifting exactness from abelian sheaves, although the current
finite-direct-image source instance already covers the module category used here.
The existing trace-degree API takes a separably closed degree hypothesis while this item
supplies only algebraically closed degrees. Rather than assume a field-change comparison,
the proof repeats the existing trace computation only at algebraically closed points,
which already detect equality. No statement repair or additional hypothesis is needed.

The theorem's hypotheses `hn` and `hd` are retained under local names in the proof: the algebraic
splitting and comparison work without their positivity, but the assigned signature stays
verbatim. Empty schemes and zero sheaves are covered by the same stalk and functor formulas;
the integer normalization does not require the degree to be a unit in the coefficient ring.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
