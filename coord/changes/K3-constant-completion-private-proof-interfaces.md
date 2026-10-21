# CategoryTheory.ConstantCompletion.resCompIso (private proof interfaces)

## Reason

Stage-3 preflight requests a change record because its static command comparison sees
new `variable`, scoped option and `attribute` commands. These commands support newly
proved private helpers. Every existing public declaration signature, public definition
body and public import is unchanged. There is no target-meaning change and no forced
adaptation.

The first integrated module exceeded the 60-second compile limit. Profiling identified
repeated normalization of chosen tensor and restriction comparisons. Private section
APIs are proved first, and their underlying constructions are then marked irreducible.
Subsequent proofs use the APIs. The already proved Kan-extension transport uses `as_aux_lemma` for its factorization
and uniqueness proofs and an abstract cochain-counit transport lemma. The already proved
`pull_additive` argument is factored through an abstract additive algebraic-lift lemma.
The scalar-insertion uniqueness proof is similarly factored through generic extensionality
for maps of sheaves. Their arguments and statements are unchanged. The resulting full module compiled cleanly
in 52.0 seconds;
the delivery compile also passed before the change-record gate.

## Old

The base module has no declarations named `resCompIso`, `transitionLift`,
`scalarTransition`, `quotientRestrictionHomEquiv`, `quotientTensorAdjunction`, or
`extensionTensorComponent`, and hence no attribute command for these names.
No existing attribute, variable or option command is removed or replaced.

## New

The only added nonlocal attribute commands, verbatim, are:

```lean
attribute [irreducible] resCompIso transitionLift scalarTransition
  quotientRestrictionHomEquiv quotientTensorAdjunction

attribute [irreducible] extensionTensorComponent
```

All six referenced definitions are new and private. Their proved section formulas,
linearity and naturality laws precede the irreducibility attributes. No public definition
contains one of these private constants. Their only downstream uses are theorem proofs
within the item module.

The helper sections also introduce these section-local variable commands, verbatim:

```lean
variable {R S T : Sheaf J CommRingCat.{u}}
variable {R B S : Sheaf J CommRingCat.{u}}
```

Each is enclosed in a newly named section that ends before the next existing declaration.
The two backward-definitional-equality options in these sections are likewise scoped.
The module also adds, after the existing `synthInstance.maxSize` option:

```lean
set_option backward.isDefEq.respectTransparency.types false
```

This changes elaboration's transparency behavior when comparing types. It reduces the
cost of checking the existing representative formulas and changes no kernel checking
or compile limit. Other new option uses have `in` and apply to one theorem. All existing
public signatures are preserved exactly.

## Users

`tools/downstream.py Sheaf.Paper.ConstantCompletionEquivalence --uses resCompIso
transitionLift scalarTransition quotientRestrictionHomEquiv quotientTensorAdjunction
extensionTensorComponent` scans 301 transitive importers and reports zero users of
each new private name in the baseline. Its `--direct` result contains the 21 modules
listed below. Private names cannot be referenced by ordinary importers. The public constructions and
statements used by the consumers remain unchanged, so no consumer adaptation is needed.
The following table includes the assigned item and every direct Lean importer found by
a complete source scan; current holders are taken from the claim records. Transitive
importers inherit exactly the same public interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantCompletionEquivalence | K3 | Five complete proofs; private proof interfaces and proof checking optimization. |
| Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedConstantAlgebraFlatQuotients | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedConstantCoefficientEquivalence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedConstantFiniteComplexRealization | E4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedConstantPresentationTransport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedExtensionZeroComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedKoszulConstantTransport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedPullbackAdjunction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedPullbackUnitTower | V1 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletionMateComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstantCompletionUnitNormalization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstantDirectImagePreservesComplete | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstantInverseImageSection | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstantPullbackScalar | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstantReductionsFiniteProjectiveModel | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstantScalarDirectImageCompleteness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ExactPullbackDerivedAdjunction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompletedScalarComparison | V8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.LisseNormalizedTowerLocalModels | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalThickEvaluation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WContractibleConstantReductionsML | unclaimed | Public interface unchanged; no adaptation. |

## Status

landed 20261021T005738-L-1887539 2026-10-21 (merge of deliver/K3/Sheaf.Paper.ConstantCompletionEquivalence)
