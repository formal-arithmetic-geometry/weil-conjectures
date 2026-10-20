# AlgebraicGeometry.ProEtale.constructibleComparison

## Reason

Restore the rework item recorded in coord/rework.tsv from its preserved archive at
quarantine/Sheaf/AlgebraicGeometry/ConstructibleProEtaleComparison.lean. The active
module is absent. The archive fails the remote compiler at line 158 with:

```text
Unknown constant `AlgebraicGeometry.Scheme.LocallyClosedStratification`
```

The current upstream API is Scheme.Stratification, already publicly available through
the existing imports. The retirement record retire-sheaf-twins-20261020.md explicitly
records this name migration, and G3-coefficient-affine-constructible-stratification-api.md
uses it for this theorem's affine-local predicate. Its fields retain finite locally
closed strata, their realizing schemes, and immersion maps; constructibility is now a
field as well. The theorem already explicitly requires constructibility for every
stratum, and that conjunct remains. Thus this migration does not change the mathematical
condition, including on non-Noetherian schemes or the empty scheme. No extra hypothesis
on X or A is introduced. The three canonical functor/ring-map constructions are restored
verbatim. All public and private imports and the other theorem clauses are retained.

This is the assigned missing-module/API repair. The existing single named theorem
hole is retained, rather than moved, decomposed, or claimed as proved. No target statement
or mathematical meaning changes. The node's Lean signature and note are updated to
record the current API; the node's statement, proof, dependencies and unit route stay.

## Old

The active module is absent. The archived theorem signature is:

```lean
theorem constructibleComparison (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    (∀ F : ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
      Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A F ↔
        ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
          ∃ S : Scheme.LocallyClosedStratification U.toScheme,
            (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
            ∀ a : Fin S.n, IsCoefficientModelLocallyConstantFinite
              (Scheme.coefficientProEtaleModelTopology.{u, v} (S.domain a)) A
              ((Scheme.coefficientProEtaleFixedModulePullback.{u, v}
                (S.immersion a ≫ U.ι) A).obj
                  ((coefficientModelFixedScalars _ A).obj F))) ∧
    (∀ [CompactSpace X] [QuasiSeparatedSpace X],
      (∀ F : ConstantCompletion.Mod (ConstantCompletion.constant
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
        Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A F →
          ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
            (P : AffinePresentation X I),
            IsIso (continuityMap P
              ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
                ((coefficientModelFixedScalars _ A).obj F).obj))) ∧
      (∃ e : Scheme.CoefficientConstructibleEtaleModuleCategory.{u, v} X A ≌
          ObjectProperty.FullSubcategory
            (Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A),
        Nonempty (e.functor ⋙
          ObjectProperty.ι
            (Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A) ≅
            ObjectProperty.ι (Scheme.IsCoefficientConstructibleEtaleModule X A) ⋙
              constructibleComparisonPullback X A)) ∧
      (∃ D : ConstantCompletion.D (ConstantCompletion.constant
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
            ConstantCompletion.D (ConstantCompletion.constant
              (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
        Nonempty (ConstantCompletion.Q _ ⋙ D ≅
          constructibleComparisonComplexPullback X A ⋙
            ConstantCompletion.Q _) ∧
        ∃ e : Scheme.CoefficientBoundedConstructibleEtaleCategory.{u, v} X A ≌
            (coefficientBoundedConstructibleProEtale X A).FullSubcategory,
          Nonempty (e.functor ⋙ (coefficientBoundedConstructibleProEtale X A).ι ≅
            ObjectProperty.ι (Scheme.IsCoefficientBoundedConstructibleEtale X A) ⋙ D)))
```

## New

The archived module is restored, with this theorem signature:

```lean
theorem constructibleComparison (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    (∀ F : ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
      Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A F ↔
        ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
          ∃ S : Scheme.Stratification U.toScheme,
            (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
            ∀ a : Fin S.n, IsCoefficientModelLocallyConstantFinite
              (Scheme.coefficientProEtaleModelTopology.{u, v} (S.domain a)) A
              ((Scheme.coefficientProEtaleFixedModulePullback.{u, v}
                (S.immersion a ≫ U.ι) A).obj
                  ((coefficientModelFixedScalars _ A).obj F))) ∧
    (∀ [CompactSpace X] [QuasiSeparatedSpace X],
      (∀ F : ConstantCompletion.Mod (ConstantCompletion.constant
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
        Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A F →
          ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
            (P : AffinePresentation X I),
            IsIso (continuityMap P
              ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
                ((coefficientModelFixedScalars _ A).obj F).obj))) ∧
      (∃ e : Scheme.CoefficientConstructibleEtaleModuleCategory.{u, v} X A ≌
          ObjectProperty.FullSubcategory
            (Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A),
        Nonempty (e.functor ⋙
          ObjectProperty.ι
            (Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A) ≅
            ObjectProperty.ι (Scheme.IsCoefficientConstructibleEtaleModule X A) ⋙
              constructibleComparisonPullback X A)) ∧
      (∃ D : ConstantCompletion.D (ConstantCompletion.constant
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
            ConstantCompletion.D (ConstantCompletion.constant
              (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
        Nonempty (ConstantCompletion.Q _ ⋙ D ≅
          constructibleComparisonComplexPullback X A ⋙
            ConstantCompletion.Q _) ∧
        ∃ e : Scheme.CoefficientBoundedConstructibleEtaleCategory.{u, v} X A ≌
            (coefficientBoundedConstructibleProEtale X A).FullSubcategory,
          Nonempty (e.functor ⋙ (coefficientBoundedConstructibleProEtale X A).ι ≅
            ObjectProperty.ι (Scheme.IsCoefficientBoundedConstructibleEtale X A) ⋙ D)))
```

## Users

The active-source downstream query with --allow-missing and all four declaration names
reported zero modules. The import/name scan also covered the quarantine tree, where the
following direct consumers remain preserved and needed. No consumer uses the changed
first clause. Named uses refer to the unchanged canonical constructions or the unchanged
bounded-derived clause. Import-only consumers retain the same public interface. No
consumer adaptation or withdrawal is needed. All three construction bodies are identical
to the archive. No source-library file is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison | Q4 | Restore all four declarations; migrate the retired stratification name. |
| Sheaf.AlgebraicGeometry.ConstructibleComparisonFlatPullback | unclaimed | Archived; named uses of canonical constructions or bounded-derived clause are unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleComparisonModuleExact | unclaimed | Archived; named uses of canonical constructions or bounded-derived clause are unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleComparisonTensorTestReflection | unclaimed | Archived; named uses of canonical constructions or bounded-derived clause are unchanged. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | unclaimed | Archived; import and public interface preserved. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian | unclaimed | Archived; named uses of canonical constructions or bounded-derived clause are unchanged. |
| Sheaf.Paper.AdicConstructibleFiniteReductions | unclaimed | Archived; import and public interface preserved. |
| Sheaf.Paper.AdicStratifiedPerfect | unclaimed | Archived; import and public interface preserved. |
| Sheaf.Paper.FiniteProperBaseChange | unclaimed | Archived; import and public interface preserved. |
| Sheaf.Paper.IntegralModels | unclaimed | Archived; import and public interface preserved. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Archived; import and public interface preserved. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Archived; import and public interface preserved. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Archived; import and public interface preserved. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Archived; import and public interface preserved. |
| Sheaf.SixFunctors.FlatModelGeneration | unclaimed | Archived; import and public interface preserved. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Archived; import and public interface preserved. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | unclaimed | Archived; import and public interface preserved. |

The restored item compiled without errors or warnings on the remote compiler in 16.5 s.
A temporary importing module checks the four public declarations and the exact
bounded-derived-clause projection used by ProEtaleFiniteTorComparisonNoetherian.
That check compiled in 6.5 s against the restored item compiled first in the same
sandbox; its temporary source was removed before delivery. The independent reader should compare the
single changed stratification type and its retained explicit constructibility conjunct
with the recorded definition and Stacks Tag 09AJ. The dependency attachment and every
DAG parent remain in place; restoration does not prune any unit or argument.

## Status

landed 20261020T235618-L-1195889 2026-10-20 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison)
