## What changed

The item module retains the six completed helper proofs from the earlier landing and
now proves `primitiveQuotientRealizationComparisons` by assembling two strictly simpler
conjunct theorems. Added modules are
`Sheaf.Paper.PrimitiveQuotientPullbackModelExistence` and
`Sheaf.Paper.PrimitiveQuotientScalarModelExistence`; each isolates one model-existence
conjunct and records the unresolved whole-system normalization argument as its own
named theorem. The parent node copy is retained and two new stage-3 node files describe
the split statements.

## Proved and sorry left

The following six declarations were already proved and are preserved:

- `WeilConjectures.primitiveQuotientReductionGood`.
- `WeilConjectures.primitiveQuotientScalarAssociation`.
- `WeilConjectures.primitiveQuotientSystemGood`.
- `WeilConjectures.primitiveQuotientScalarTransition`.
- `WeilConjectures.primitiveQuotientScalarTriple`.
- `WeilConjectures.primitiveQuotientScalarUnit`.

The parent declaration `WeilConjectures.primitiveQuotientRealizationComparisons` is
closed by a real conjunction proof. Two strictly simpler holes are added:

- `WeilConjectures.primitiveQuotientPullbackModelExistence`, node
  `lem-trf-primitive-quotient-pullback-model-existence`.
- `WeilConjectures.primitiveQuotientScalarModelExistence`, node
  `lem-trf-primitive-quotient-scalar-model-existence`.

No `sorry` occurs in a definition. This is a decomposition of one disputed hole into
its pullback and scalar conjuncts; no claim is made that the disputed normalization has
been proved by the assembly.

## No longer needed

The direct proof import `Sheaf.Algebra.Homology.ChangeOfRingsKFlat` remains replaced by
`Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients`, as in the prior
landing. The four unused direct imports removed there remain removed:
`Sheaf.AlgebraicGeometry.ProEtaleConstantExact`,
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`,
`Sheaf.CategoryTheory.FlatRoosFunctorDescent`, and
`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`.

No additional existing dependency is pruned by this decomposition. The parent proof
still uses the six helper routes, and each split node records the parent proof
dependencies needed by the unfinished normalization argument.

## Where the brief, the DAG or earlier work was wrong

`STATEMENT-DISPUTED: primitiveQuotientRealizationComparisons` remains in force. The
`CoefficientReductionPresentation` interface constrains its comparison map only after
finite coefficient evaluations. Those evaluations are conservative but do not make
morphisms faithful, so they do not force the required equality after the total derived
limit. The nonclosed-image example for derived-complete Z_p-modules in the earlier T6
report exhibits an automorphism invisible at every finite level but visible after
realization. The two new nodes make this exact missing normalization argument explicit
without weakening the original statement.

## New nodes

`lem-trf-primitive-quotient-pullback-model-existence` states existence of the normalized
pullback model for one supplied calculus and Roos comparison. Its source is Stacks Tags
099N(2),(5), 06YS, 0G7E and 0941; it is the pullback conjunct of the parent plan.

`lem-trf-primitive-quotient-scalar-model-existence` states the corresponding scalar model
existence for one coefficient inclusion. Its source is Stacks Tags 03EK, 06YY and 0941;
it is the scalar conjunct of the parent plan. Both nodes have their own modules and
named `sorry` theorems, so the remaining work is independently claimable.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
