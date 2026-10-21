# AlgebraicGeometry.sfProEtaleClosureGenerators and sfEtaleClosureGenerators

## Reason

Restore the quarantined rework item recorded in coord/rework.tsv. The archive still
uses the retired LocallyClosedStratification API. Its canonical replacement is
Scheme.Stratification, already used by intrinsic constructibility and the restored
FlatModelGeneration source. All archived declarations and proof dependencies remain.
No source-library file or target statement changes.

On a Noetherian scheme every locally closed subset is constructible, so the new
stratification's constructibility field adds no restriction in either generation theorem.
The flat-stratification theorem already extracts the canonical Stratification from
intrinsic constructibility. Arbitrary stratum scheme structures and immersion maps
remain allowed. The singleton trivial stratification still works for an empty scheme,
and zero strata remain permitted by Stratification itself.

Both generator predicates expose the current Stratification type. The theorem
proEtaleFlatStratification uses the same replacement in its existential conclusion.
The generation theorem conclusions and the flat model theorem are unchanged.

The retired empty public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
is removed. A proof import of WeilConjectures.ConstructibleSheaf.OpenClosedStratification
supplies Stratification.trivial, replacing the retired identityStratification construction.
Two declaration-local backward.isDefEq.respectTransparency options permit the existing
scalar-restriction identification and the dependent filtration proof to elaborate.
These options do not change declaration types or the kernel's checking rules.

## Old

```lean
def sfProEtaleClosureGenerators (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty (proEtaleDerivedCategory X A) :=
  fun K ↦ ∃ (str : LocallyClosedStratification X) (i : Fin str.n)
    (j : str.domain i ⟶ (str.immersion i).image) (_ : IsOpenImmersion j)
    (L : proEtaleRingModules (str.domain i) (proEtaleConstantRing (str.domain i) A)),
    j ≫ (str.immersion i).imageι = str.immersion i ∧
    IsLisseProEtaleFixedModuleSheaf (str.domain i) (ULift.{u + 1, u} A)
      ((sfIntrinsicModuleEquivalence (str.domain i) A).inverse.obj L) ∧
    SheafOfModules.IsFlatOnSite (J := ProEt.topology (str.domain i))
      (R := proEtaleConstantRing (str.domain i) A) L ∧
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((sfIntrinsicModuleEquivalence X A).functor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (str.immersion i).imageι).obj
          ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
            ((sfIntrinsicModuleEquivalence (str.domain i) A).inverse.obj L)))))

def sfEtaleClosureGenerators (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A] :
    ObjectProperty (Etale.DerivedCategoryModule A X) :=
  fun K ↦ ∃ (str : LocallyClosedStratification X) (i : Fin str.n)
    (j : str.domain i ⟶ (str.immersion i).image) (_ : IsOpenImmersion j)
    (L : Sheaf (str.domain i).smallEtaleTopology (ModuleCat.{u + 1} A)),
    j ≫ (str.immersion i).imageι = str.immersion i ∧
    IsFiniteLocallyConstantSheaf L ∧ ObjectProperty.flat L ∧
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} A) (str.immersion i).imageι).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj L)))
```

## New

```lean
def sfProEtaleClosureGenerators (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty (proEtaleDerivedCategory X A) :=
  fun K ↦ ∃ (str : Stratification X) (i : Fin str.n)
    (j : str.domain i ⟶ (str.immersion i).image) (_ : IsOpenImmersion j)
    (L : proEtaleRingModules (str.domain i) (proEtaleConstantRing (str.domain i) A)),
    j ≫ (str.immersion i).imageι = str.immersion i ∧
    IsLisseProEtaleFixedModuleSheaf (str.domain i) (ULift.{u + 1, u} A)
      ((sfIntrinsicModuleEquivalence (str.domain i) A).inverse.obj L) ∧
    SheafOfModules.IsFlatOnSite (J := ProEt.topology (str.domain i))
      (R := proEtaleConstantRing (str.domain i) A) L ∧
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((sfIntrinsicModuleEquivalence X A).functor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (str.immersion i).imageι).obj
          ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
            ((sfIntrinsicModuleEquivalence (str.domain i) A).inverse.obj L)))))

def sfEtaleClosureGenerators (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A] :
    ObjectProperty (Etale.DerivedCategoryModule A X) :=
  fun K ↦ ∃ (str : Stratification X) (i : Fin str.n)
    (j : str.domain i ⟶ (str.immersion i).image) (_ : IsOpenImmersion j)
    (L : Sheaf (str.domain i).smallEtaleTopology (ModuleCat.{u + 1} A)),
    j ≫ (str.immersion i).imageι = str.immersion i ∧
    IsFiniteLocallyConstantSheaf L ∧ ObjectProperty.flat L ∧
    Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} A) (str.immersion i).imageι).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj L)))
```

## Users

The item is absent from active sources, so tools/downstream.py reports an unknown
module. A direct import/name scan of lean/ and quarantine/ found exactly the two
archived direct consumers below, in addition to the item. Both archives are preserved.
Neither consumer changes or requires an adaptation: the compact-generator proof
unpacks the same immersion and lisse-flat data, and the trace-formula proof applies
the unchanged thick-envelope equality. No live consumer imports the absent item.
No statement in Challenge.lean is changed. The generation results are still required
by quarantined parents; their absence is not treated as permission to withdraw them.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.FlatModel | B2 | Restored and migrated to canonical stratification API. |
| Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators | quarantined | Same generator destructuring and generation theorem application; archive unchanged. |
| Sheaf.Paper.TrfDevissageGeneration | quarantined | Same generator predicate and unchanged equality application; archive unchanged. |

## Status

landed 20261021T020054-L-2581227 2026-10-21 (merge of deliver/B2/Sheaf.SixFunctors.FlatModel)
