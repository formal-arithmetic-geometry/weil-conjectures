# ModuleCat.exists_kFlatLocalizedTensorComparison_natural

## Reason

Execute the listed retirement item in coord/retire-items.tsv. The Sheaf module
repeats a complete upstream construction under the same declaration name. The
upstream theorem gives the identical conclusion without the explicit flatness
hypothesis or the A-module derived-category instance. It therefore proves every
use of the former statement by specialization. Keep the upstream file verbatim.

The old module has zero holes; this is duplicate retirement, not a new proof.
Reattach lem-pc-kflat-localized-tensor-comparison-natural to upstream. Its
mathematical statement and all parent-node dependencies remain valid. No unit
statement or step is bypassed; this node is not in the unit's realized fields.

## Old

The removed Sheaf module declared, with the ambient rings, algebra structures,
derived-category instances over R, A, B and Q, N, t as in the original file:

```lean
theorem exists_kFlatLocalizedTensorComparison_natural
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    (i : ℤ) :
    let m := fun U : CochainComplex.KFlat (ModuleCat.{u} A) ↦
      baseDerivedTensorCohomologyModel R A B (U.obj ⊗ Q) C
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let T := CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ F ⋙ tensorRight N ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) i
    ∃ (S : CochainComplex.KFlat (ModuleCat.{u} A) ⥤ ModuleCat.{u} C)
      (η : S ⟶ T),
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).WKFlat.IsInvertedBy S ∧
      ∀ U : CochainComplex.KFlat (ModuleCat.{u} A),
        ∃ e : (extendScalars (algebraMap (A ⊗[R] B) C)).obj ((m U).cohomology i) ≅
          S.obj U,
          e.hom ≫ η.app U = (m U).localizedComparison i ≫
            HomologicalComplex.homologyMap
              ((Functor.Monoidal.μIso F U.obj Q).inv ≫ (F.obj U.obj ◁ t)) i
```

The direct consumer imported:

```lean
import Sheaf.Algebra.Homology.KFlatLocalizedTensorComparisonNatural
```

and obtained its witnesses with:

```lean
    exists_kFlatLocalizedTensorComparison_natural R A B C Q N t hC hQ i
```

## New

Remove the duplicate Sheaf module via deleted.txt. The unchanged upstream
module supplies this theorem (with the same ambient rings, algebras, Q, N, t;
derived-category instances over R and B suffice):

```lean
theorem exists_kFlatLocalizedTensorComparison_natural
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    (i : ℤ) :
    let m := fun U : CochainComplex.KFlat (ModuleCat.{u} A) ↦
      baseDerivedTensorCohomologyModel R A B (U.obj ⊗ Q) C
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let T := CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ F ⋙ tensorRight N ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) i
    ∃ (S : CochainComplex.KFlat (ModuleCat.{u} A) ⥤ ModuleCat.{u} C)
      (η : S ⟶ T),
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).WKFlat.IsInvertedBy S ∧
      ∀ U : CochainComplex.KFlat (ModuleCat.{u} A),
        ∃ e : (extendScalars (algebraMap (A ⊗[R] B) C)).obj ((m U).cohomology i) ≅
          S.obj U,
          e.hom ≫ η.app U = (m U).localizedComparison i ≫
            HomologicalComplex.homologyMap
              ((Functor.Monoidal.μIso F U.obj Q).inv ≫ (F.obj U.obj ◁ t)) i
```

The consumer instead imports:

```lean
import WeilConjectures.Algebra.Homology.KFlatLocalizedTensorComparisonNatural
```

and uses:

```lean
    (fun (_ : Module.Flat (A ⊗[R] B) C) ↦
      exists_kFlatLocalizedTensorComparison_natural R A B C Q N t hQ i) hC
```

Its own declaration signature, visibility and docstring remain verbatim. The
lambda specializes the stronger upstream assertion to the consumer's retained
flatness assumption hC, explicitly consuming that argument to avoid an unused
variable warning. No assumption is added or removed from the consumer. The theorem application has exactly the same
witness types and component equation. No source-library declaration changes.

## Users

`tools/downstream.py` reports the following three downstream modules and the
item itself as the only other textual declaration occurrence. There is one
direct importer. No claim file exists for any of the three consumers in the
shared snapshot inspected for this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.KFlatLocalizedTensorComparisonNatural | B9 (assigned) | Retired duplicate; DAG attachment moves to upstream. |
| Sheaf.Algebra.Homology.LocalizedTensorComparisonDerivedArrow | unclaimed | Import and theorem application migrate; public signature stays identical. |
| Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetractCore | unclaimed | Transitive importer only; unchanged interface, no adaptation. |
| Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetract | unclaimed | Transitive importer only; unchanged interface, no adaptation. |

The DAG parent lem-pc-localized-tensor-comparison-derived-arrow still uses the
same node, now realized upstream. The base-tensor-cohomology node names this
node only in historical created/blueprint metadata. No quarantined parent or
unit realization requires the duplicate Lean module. No target statement or
definition changes, so no target-meaning review is reopened.

## Status

landed 20261020T233058-L-891579 2026-10-20 (merge of deliver/B9/Sheaf.Algebra.Homology.KFlatLocalizedTensorComparisonNatural)
