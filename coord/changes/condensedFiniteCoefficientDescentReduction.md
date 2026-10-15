# condensedFiniteCoefficientDescentReduction

## Reason

Replace the undelivered nonzero-case restatement with two genuine intermediate statements:
local finite-presentation coefficient descent, and assembly given models on all strata.
The existing target theorem, its hypotheses, its conclusion, and every existing definition
are unchanged. The target's unused public `MorphismDefs` import is removed: its signatures
need only `Def`, `Compatibility`, and `FiniteCoefficientFields`. The new helper modules
are imported only for the proof, so their declarations are not re-exported by the target.

## Old

The target imported:

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
```

The two helper declarations did not exist on the delivery base.

## New

The target retains its other three public imports. Its two new imports are private to proofs:

```lean
import Sheaf.Paper.CondensedLfpCoefficientModel
import Sheaf.Paper.CondensedStratumModelAssembly
```

The new declarations are, verbatim:

```lean
theorem exists_lfp_finiteCoefficient_model_on_immersion
    (T X : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (f : X ⟶ T) [IsImmersion f] (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (hM : IsLocallyFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)) M) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (M_E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))),
      IsLocallyFinitelyPresented
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)) M_E ∧
      Nonempty ((Mod.extendScalars
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E))).obj M_E ≅ M)
```

```lean
theorem exists_finiteCoefficient_model_of_stratum_models
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ))
    (S : Scheme.Stratification T)
    (hS : ∀ a : Fin S.n,
      ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
        (M_E : Mod (Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1})
          ((upperStar Ab.{u + 1} (S.immersion a)).obj (padicSubfieldRingObj T ℓ E))),
        IsLocallyFinitelyPresented
          ((upperStar Ab.{u + 1} (S.immersion a)).obj (padicSubfieldRingObj T ℓ E)) M_E ∧
        Nonempty ((Mod.extendScalars ((upperStar Ab.{u + 1} (S.immersion a)).map
          (padicSubfieldRingObjToPadicAlgCl T ℓ E))).obj M_E ≅
            (((upperStar Ab.{u + 1} (S.immersion a)).mapMod
              (padicAlgClRingObj T ℓ)).obj M))) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (M_E : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)),
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) M_E ∧
        Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).obj M_E ≅ M)
```

## Users

All transitive importers of the target are listed below, from `tools/downstream.py`.
None mentions either new declaration. No existing target or downstream signature is changed.
No adapted module is delivered. Claims are from this machine's read-only coordination snapshot.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.CondensedFinitePresentationDescent` | B3 | Proof now combines the two helper statements; unused public import removed. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | No statement or definition changes; proof-only helper imports are not re-exported. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | A4 | No statement or definition changes; proof-only helper imports are not re-exported. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | No statement or definition changes; proof-only helper imports are not re-exported. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | No statement or definition changes; proof-only helper imports are not re-exported. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | No statement or definition changes; proof-only helper imports are not re-exported. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | A2 | No statement or definition changes; proof-only helper imports are not re-exported. |
| `TargetsCheck` | unclaimed | No statement or definition changes; proof-only helper imports are not re-exported. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | No statement or definition changes; proof-only helper imports are not re-exported. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | No statement or definition changes; proof-only helper imports are not re-exported. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | B2 | No statement or definition changes; proof-only helper imports are not re-exported. |

The sole direct importer, `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`,
was checked textually: it calls the same target theorem and does not mention any declaration
introduced by `MorphismDefs`. Compiling its full unchanged source exceeded the wrapper's 60-second
limit both against the baseline and against this sandbox overlay; neither run reported a Lean
error. This is a verification limit, not an adaptation failure. All three delivered modules compile
individually well within the limit, and their axiom probes are included in the second reading.

## Status

landed 20261015T183808-L-842976 2026-10-15 (merge of deliver/B3/Sheaf.Paper.CondensedFinitePresentationDescent)
