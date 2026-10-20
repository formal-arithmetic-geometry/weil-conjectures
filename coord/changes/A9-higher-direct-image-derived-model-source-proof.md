# AlgebraicGeometry.Scheme.Modules.exists_derived_model_higherDirectImage

## Reason

Restore the quarantined module assigned by coord/rework.tsv (sync 5f7b33eac).
The archive publicly imports the former Sheaf derived-pullback construction while
its private canonical-base-change dependency imports the adopted construction;
the recorded failure is a duplicate AlgebraicGeometry.derivedPullback declaration.
The adopted source now also contains this item's exact, completely proved theorem.
Redeclaring the theorem would introduce another same-name duplicate when combined
with its existing source consumer. Re-export the adopted proof instead.

This is a substantive import/declaration-ownership repair with zero original holes.
The quarantined archive is preserved unchanged; no source-library file changes.
The item is restored as a nonempty public compatibility import, not withdrawn.

## Old

The missing library module's authoritative archived source is
quarantine/Sheaf/AlgebraicGeometry/HigherDirectImageDerivedModel.lean.
It declares the following theorem, with a complete proof:

```lean
theorem exists_derived_model_higherDirectImage
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation] (hF : F.IsFlatOver f) :
    ∃ E : schemeDerivedCategory T,
      (∀ n : ℤ, n < 0 → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj E)) ∧
      (∀ q : ℕ, Nonempty ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj E ≅
          (higherDirectImage f q).obj F)) ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f g → ∀ q : ℕ,
        Nonempty ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) q).obj
            ((derivedPullback g).obj E) ≅
              (higherDirectImage f' q).obj ((Modules.pullback g').obj F))
```

Its public imports are Mathlib.AlgebraicGeometry.Morphisms.Proper,
Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation,
Sheaf.AlgebraicGeometry.DerivedPullback, and
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic.
Its private imports are RightDerivedFunctor.PlusCompatibility and
RelativelyFlatCanonicalModuleBaseChange under WeilConjectures.

## New

```lean
module
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageDerivedModel
```

The restored module re-exports the adopted theorem and its public statement imports;
it declares no second copy of the theorem. The canonical source module has exactly
the same binders and conclusion, explicitly qualifying AlgebraicGeometry.derivedPullback
to distinguish it from Scheme.Modules.derivedPullback in the new source environment.
Proper, FinitePresentation, DirectImage.Basic and the canonical DerivedPullback are
public imports of that source module. Its proof still constructs Rf_*(F[0]), uses the
right-derived-functor connectivity and homology comparisons, and obtains base change
from exists_isIso_canonicalModuleBaseChange_of_isFlatOver and adjunction uniqueness.
No definition, source signature, target signature or mathematical meaning changes.

The existing DAG node lem-pc-higher-direct-image-derived-model is reattached to
WeilConjectures.AlgebraicGeometry.HigherDirectImageDerivedModel and the same fully
qualified theorem name. Its Lean signature is recorded verbatim from that source.
All stmt_deps, proof_deps and numbered proof steps remain unchanged, including the
parent's use from lem-pc-flat-rf-open and the unit sk-thm-picard-perfect.
No new dependency or node is introduced.

## Users

The required tools/downstream.py query with --allow-missing and
--uses exists_derived_model_higherDirectImage reports zero current transitive
importers and zero callers of the missing Sheaf module. A source search of both
lean/ and quarantine/ finds no importer of that path. The live call is in the
source PerfectLocusOfRank module, which already imports the canonical source.
Its direct source importer set is listed below for completeness; none is adapted.
The DAG parent is preserved regardless of that absence of current Sheaf importers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.HigherDirectImageDerivedModel | A9 | Restore public access to the canonical proof; no second declaration. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocusOfRank | unclaimed | Existing caller already uses the canonical source declaration; no change. |
| WeilConjectures | unclaimed | Existing public import of the canonical source module; no change. |

Verification: the restored module compiles in 1.5 seconds. A separate sandbox
signature probe applies the existing theorem with the original hypotheses and
all three conclusions, using the explicit canonical derived pullback. Its
#print axioms output contains only propext, Classical.choice and Quot.sound.
A separate consumer probe imports the restored compatibility module together
with the unchanged source PerfectLocusOfRank and checks both theorem names.
There are no consumer signatures or proofs to adapt.

## Status

landed 20261020T211626-L-3480233 2026-10-20 (merge of deliver/A9/Sheaf.AlgebraicGeometry.HigherDirectImageDerivedModel)
