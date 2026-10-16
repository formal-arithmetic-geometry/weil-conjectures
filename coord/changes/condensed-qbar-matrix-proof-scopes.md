# AlgebraicGeometry.ProEtale.exists_condensedQbar_finiteFree_refinement

## Reason

The stage-3 static check classifies added command scopes as a visible change and requires
this record. The proof introduces the namespace `CondensedQbarMatrixRefinement`, local
instance attributes, additional universe names for generic private helpers, scoped opens,
and a section of universe-transport helpers. Every helper in the existing item module is
private. The existing theorem keeps its exact signature and visibility, and the four
public imports are identical. Added imports are proof-only. No existing mathematical
statement or definition is changed, and no target statement acquires a new meaning.

The two new public function ring homomorphisms and the remaining theorem are confined to
`Sheaf.Paper.CondensedQbarFunctionPresentations` and documented by the new node
`lem-weil-pbc-condensed-qbar-compatible-function-presentations`.

## Old

```lean
theorem exists_condensedQbar_finiteFree_refinement
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (f : Y ⟶ X) (hf : WeaklyEtale f)
    (P : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hP : Mod.IsFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
      (((upperStar Ab.{u + 1} f).mapMod
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj P)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i : C.I₀,
      ∃ r : ℕ, Nonempty
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (C.f i ≫ f)).obj P ≅
          Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (C.X i)) r)
```

Original command context: `universe u`, `open CategoryTheory`,
`open scoped CategoryTheory.Obj`, namespace `AlgebraicGeometry.ProEtale`.

## New

```lean
theorem exists_condensedQbar_finiteFree_refinement
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (f : Y ⟶ X) (hf : WeaklyEtale f)
    (P : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hP : Mod.IsFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
      (((upperStar Ab.{u + 1} f).mapMod
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj P)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i : C.I₀,
      ∃ r : ℕ, Nonempty
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (C.f i ≫ f)).obj P ≅
          Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (C.X i)) r)
```

Additional private proof context: universes `v w z`, `open CategoryTheory.Limits`,
namespace `CondensedQbarMatrixRefinement`, section `CoefficientUniverse`,
`open Opposite CategoryTheory.MonObj CategoryTheory.MonoidalCategory`, local variable
binders for the lifted field, `noncomputable section`, and local finite-biproduct instances.
The namespace and sections are closed. No global instance or notation is added.

## Users

`tools/downstream.py Sheaf.Paper.CondensedQbarLfpMatrixRefinement --uses
`exists_condensedQbar_finiteFree_refinement` found fifteen downstream modules.
Only the local-triviality parent and the item itself mention the declaration.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | G2 | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedQbarLfpLocalTriviality` | unclaimed | uses unchanged theorem; no adaptation |
| `Sheaf.Paper.CondensedQbarLfpMatrixRefinement` | E3 | proof replaced; signature unchanged |
| `Sheaf.Paper.CondensedStratumModelAssembly` | unclaimed | transitive importer; no adaptation |
| `Sheaf.Paper.CondensedStratumModelInductionStep` | M3 | transitive importer; no adaptation |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | transitive importer; no adaptation |
| `TargetsCheck` | unclaimed | transitive importer; no adaptation |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | transitive importer; no adaptation |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | transitive importer; no adaptation |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | transitive importer; no adaptation |

No downstream module is adapted. The old and new public theorem signatures above are
byte-for-byte equal. The changes affect the proof and its private elaboration contexts.

## Status

landed 20261016T054834-L-156276 2026-10-16 (merge of deliver/E3/Sheaf.Paper.CondensedQbarLfpMatrixRefinement)
