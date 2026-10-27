## What changed

Proved `WeilConjectures.WfTensorCompletion.integral` from the declared
`wfConstructibleTensorKoszulUnit`: this supplies ordinary and completed tensor closure,
invertibility of the actual unit, and its naturality.
Proved `WeilConjectures.WfTensorCompletion.integral_equivariance` from
`wfTensorPullbackCompletionUnitSquare` and the unit's naturality, lifting the equations
through the full constructible inclusion. Its isomorphism instance is constructed from
the actual completion-unit isomorphism. Existing signatures and definition bodies stay
unchanged. Added only the two proof-dependency imports and local irreducibility controls.

## Proved and sorry left

Original holes: four. Closed two, added zero:

- `WeilConjectures.WfTensorCompletion.integral` — proved.
- `WeilConjectures.WfTensorCompletion.integral_equivariance` — proved.
- `WeilConjectures.wfTensorCompletionFrobenius` — original `sorry` retained;
  node `lem-wf-tensor-completion-frobenius`.
- `WeilConjectures.wfTensorCompletionCommonField` — original `sorry` retained;
  node `lem-wf-tensor-completion-frobenius`.

A full rational construction was attempted using unique raw bilinear extension and
transport along the actual unit. Generic localization naturality, component equations,
conjugation and Weil-isomorphism helpers compiled in diagnostic probes. The complete
geometric specialization did not pass the 60-second file limit; repeated profiles
identified expensive concrete conversions and dependent record equalities. That attempt
is excluded from the delivery. No new theorem or definition containing `sorry` is added. The delivery module compiles
cleanly with `lcompile.py` in 41.5 seconds.

## No longer needed

Removed redundant direct proof imports:
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
`Sheaf.Paper.TwFrobeniusAction`,
`Sheaf.Paper.IntegralStratifiedPerfectCharacterization`,
`Sheaf.SixFunctors.ConstructibleTensorCompletion`,
`Sheaf.Paper.IntrinsicCompletionCompleted`,
`Sheaf.Paper.IntegralOperationsPreserveConstructible`,
`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`,
`Sheaf.Paper.ConstantCompletionEquivalence`,
`Sheaf.Paper.PbcRationalCategory`,
`Sheaf.Paper.PbcWeilCategory`, and
`Sheaf.Paper.WeilCompletedTensorReflector`.
Their definitions are available through the existing public tensor import; the two
new proof imports package the integral obligations. No DAG dependency or module is
withdrawn: the original rational holes and their planned dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

The conditional rational-descent declaration requires normalized raw rational functors
as input. It does not itself construct the uniquely normalized package required by
`wfTensorCompletionFrobenius`. Constructing and efficiently checking that package
remains unfinished. No statement is changed.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
