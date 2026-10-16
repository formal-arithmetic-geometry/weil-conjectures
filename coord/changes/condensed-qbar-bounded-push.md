# AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper

## Reason

The old instance asserts invertibility on the entire unbounded ambient category. Its supplied
argument uses an ambient exceptional right adjoint that the library does not construct; the
existing dispute comment already records this gap. No counterexample to this exact internal
condensed coefficient instance is claimed. The target route only uses its components on bounded
constructible inputs. Retire the unused stronger declaration after adapting that consumer, and
supply a distinctly named bounded-below component theorem. This is pruning and an interface
repair, not a proof of the retired statement and not a silent weakening under the same name.

The new proof combines a scalar-basis decomposition with the exact condensed qcqs filtered
continuity theorem. The copower-continuity step is fully proved in this delivery. The independent
scalar-basis construction is the one remaining named obligation. No definition changes, and no
statement of Challenge.lean, its definitions, or the constructible consumer changes.

The anonymous all-unbounded Omega shriek example used the retired instance and is removed.
The finite-extension shriek example and every finite-extension result remain unchanged.
The module documentation is corrected to describe the surviving public interface.

H10 performance repair of returned head 514ede3d3: the added bounded comparison keeps its
statement unchanged. A private wrapper of its unchanged copower helper fixes both indexing families explicitly;
its reflection proof is checked generically in the same file; local irreducibility keeps the
chosen adjunction and pullback implementations folded, with the mate unfolded explicitly.
Only the item proof changes in this retry. The scalar-basis and bounded-copower modules and
all consumer adaptations remain exactly as returned. No additional module requires adaptation.

The current second reader also repaired a consumer timeout reproduced by `lcompile.py --all`:
the item passed in 52.5 seconds, but the consumer exceeded 60 seconds. Keeping `derivedPushHom`
locally irreducible in the consumer avoids expanding the ambient mate while transferring its
component to the full subcategory. This is a local elaboration attribute only; all retained
signatures, definitions, imports, and proof arguments are unchanged. The consumer then compiled
in 9.5 seconds. The original consumer independently reproduced precisely its two missing ambient
instances at lines 106 and 111 (13.0 seconds).

## Old

```lean
instance isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper [IsProper f]
    (E : FiniteIntermediateField ℓ) :
    IsIso (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f)
```

## New

The old declaration is removed. The new, separately named declaration is:

```lean
theorem isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE [IsProper f]
    (E : FiniteIntermediateField ℓ)
    (M : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (N : ℤ) [M.IsGE N] :
    IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app M)
```

## Users

`tools/downstream.py` found the following 50 downstream modules. Text search for the old name
finds only its own module. Search for the actual Omega push comparison finds the two ambient
instance requests in the adapted consumer and the unchanged comparison definition in
CondensedQbarComparisons. That definition and every target keep exactly the same meaning.
The table records current holders when the audit was run.

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | F3 | Retire the unused disputed ambient instance; add the distinctly named bounded component theorem. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexColimit | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexCompatibility | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDerivedTransport | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexModel | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexUnderivedCompatibility | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedLfpCoefficientModel | A4 | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Proof adapted to componentwise bounded comparison; statement and definitions unchanged. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | G1 | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenClosed | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenPiece | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | C4 | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| TargetsCheck | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | No semantic change: definitions and all retained signatures unchanged; no other use of the retired instance found. |

The original consumer was compiled against this changed dependency and fails at original
lines 106 and 111: `failed to synthesize instance of type class IsIso (derivedPushHom ... f)`
and the analogous request for f'. The adapted consumer compiles (31.6 seconds). It imports
the component theorem directly and proves one private restriction lemma, extracting a lower
bound from the existing bounded-constructibility property. The square proof reuses this
lemma twice. All retained signatures and visibility are identical.

## Status

landed 20261016T093726-L-2050850 2026-10-16 (merge of deliver/F3/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility)
