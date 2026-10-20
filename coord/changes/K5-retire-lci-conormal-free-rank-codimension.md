# Ideal.exists_basis_cotangent_localization_of_completeIntersection

## Reason

Retire the duplicate Sheaf module as assigned by coord/retire-items.tsv and the human's
2026-10-20 hand-off in coord/changes/retire-sheaf-twins-20261020.md. The public theorem
already exists with the identical signature in the official upstream twin. The inventory
marks the pair DIFFERENT only because the copy additionally contains the private helper
Ideal.principal_ci_presentation_dimension. No other module uses this helper; the official
proof performs its presentation and dimension argument inline. Both modules also have
private proofs of basis_of_stably_free. No public helper or definition needs replacement.

## Old

In Sheaf.RingTheory.LciConormalFreeRankCodimension:

```lean
theorem exists_basis_cotangent_localization_of_completeIntersection {k : Type u} [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k)) (q : PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I)) (hci : ∃ g : MvPolynomial (Fin n) k ⧸ I, g ∉ q.asIdeal ∧ Algebra.IsGlobalCompleteIntersection k (Localization.Away g)) : ∃ d : ℕ, topologicalKrullDimAt q = (d : WithBot ℕ∞) ∧ d ≤ n ∧ Nonempty (Module.Basis (Fin (n - d)) (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl I.Cotangent))
```

## New

The identical theorem in WeilConjectures.RingTheory.LciConormalFreeRankCodimension:

```lean
theorem exists_basis_cotangent_localization_of_completeIntersection {k : Type u} [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k)) (q : PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I)) (hci : ∃ g : MvPolynomial (Fin n) k ⧸ I, g ∉ q.asIdeal ∧ Algebra.IsGlobalCompleteIntersection k (Localization.Away g)) : ∃ d : ℕ, topologicalKrullDimAt q = (d : WithBot ℕ∞) ∧ d ≤ n ∧ Nonempty (Module.Basis (Fin (n - d)) (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl I.Cotangent))
```

Withdraw the old module through deleted.txt. The existing DAG node
lem-weil-pbc-lci-conormal-free-rank-codimension now points at the official theorem.
Both direct consumers replace their private import with the official module. All
consumer declarations, public imports and existing proof bodies stay verbatim.
No upstream file, definition, target, or statement changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictlySemistableCurve | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.RingTheory.LocalCompleteIntersectionFieldChange | unclaimed | Replace the private import by the official twin; no declaration changes. |
| Sheaf.SixFunctors.TraceFormula.NodalEtaleChart | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.NodalLogRegularity | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.CompleteIntersectionFibresLimitDescent | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.ContractedComponentGenericData | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.LciFieldChangeLocal | unclaimed | Replace the private import by the official twin; no declaration changes. |
| Sheaf.TraceFormula.LocalCompleteIntersectionScheme | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.MarkedCurveFiniteTypeModel | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.NodalFamilyNoetherianApproximation | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.NodalOpenLocus | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.StableModificationStabilityFieldDescent | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.SyntomicGeometricFibresAffineCriterion | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.SyntomicLocusBaseChange | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |
| Sheaf.TraceFormula.ValuationSymmetricNodalBlowup | unclaimed | Transitive consumer; identical theorem and public import closure; no adaptation. |

This table includes all 27 transitive consumers from tools/downstream.py. Its --uses
check finds no external occurrence of either the public theorem or the private
principal_ci_presentation_dimension helper. The two current direct importers above
are the complete set from the source scan; the retirement inventory's syntomic
consumers have already migrated to their official twins. No quarantined Lean file
imports the retired module. DAG parents retain the same node and mathematical
statement, including unfinished parents; they now resolve its Lean attachment to
the official theorem. No unit realization is removed or bypassed.

## Status

landed 20261020T221236-L-4162976 2026-10-20 (merge of deliver/K5/Sheaf.RingTheory.LciConormalFreeRankCodimension)
