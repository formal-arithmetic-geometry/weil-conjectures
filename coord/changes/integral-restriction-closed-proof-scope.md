# integralRestrictionClosed proof scope

## Reason

The completed proof adds private comparison helpers and proof elaboration commands
(`universe`, `variable`, `open`, and local notation resolution) to the item module.
The static stage-3 checker therefore requires a change record. These additions support
only the proof; all existing public declarations, definitions, signatures, visibility,
and public imports retain their meanings. The delivery also adds the strictly smaller
prerequisite module `IntegralComplementFiniteness`, whose public theorem is recorded by
its new DAG node.

## Old

```lean
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
```

## New

```lean
universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
```

These commands are inserted after the unchanged open commands, followed by private
comparison helpers. All existing declarations retain their signatures verbatim.

The six proof imports are replaced by the exact-coefficient recollement,
integral-model, Yoneda and derived-functor interfaces used by the proof. Private
`comparisonEquiv`, `comparisonEquiv_left`, `comparisonEquiv_right`, `comparison`,
`generators_mem_localizing`, and `closedCompactificationComparison` helpers are fully
proved. The original theorem signature and all existing public definitions are
unchanged. `IntegralComplementFiniteness` is a new public prerequisite module with its
own node and a fully proved theorem.

## Users

The read-only downstream query lists the following 32 consumers. A declaration-use
query finds no consumer that mentions integralRestrictionClosed by name. Their imported
public API is unchanged, and the added private helpers cannot occur in public signatures.
No target statement or definition changes, so no target statement review is reopened.
No consumer is adapted by this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Unchanged public signatures and definitions; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Unchanged public signatures and definitions; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Unchanged public signatures and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Unchanged public signatures and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Unchanged public signatures and definitions; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| TargetsCheck | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Unchanged public signatures and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Private proved helpers and local proof scopes only. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | U3 | New prerequisite theorem, consumed only by the item proof. |

## Status

landed 20261019T034308-L-418551 2026-10-19 (merge of deliver/U3/Sheaf.SixFunctors.IntegralRestrictionClosed)
