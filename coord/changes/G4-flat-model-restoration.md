# Sheaf.SixFunctors.FlatModel restoration and stratification interface

## Reason

Restore the assigned rework item from
`quarantine/Sheaf/SixFunctors/FlatModel.lean`, preserving its Lean attachment and every
proof dependency. The active source is absent, as recorded in `coord/rework.tsv`.

Compiling the unmodified archive failed with unknown identifiers
`LocallyClosedStratification` (lines 271, 294, 404) and
`WeilConjectures.integralCoefficientAbLocallyBijective` (line 85), followed by
cascading elaboration errors. The retirement record
`coord/changes/retire-sheaf-twins-20261020.md` prescribes migration from the retired
stratification name to `Scheme.Stratification`. The current constructible sheaf and
FlatModelGeneration statements already use that structure.

The restored generator definitions and stratification theorem now use the current
scheme stratification interface. It keeps the actual stratum schemes, immersion maps,
finite partition, and constructible locally closed strata. On the Noetherian schemes
of every theorem here, constructibility follows from local closedness by
`IsLocallyClosed.isConstructible_of_noetherianSpace`; thus the paper's statements are
unchanged. Empty schemes and zero rings remain allowed. In particular, the zero
sheaf/identity-stratification proof in the envelope theorem still compiles.

Use `inferInstance` at the explicitly specified coefficient universe for the local
locally-bijective instance; importing integral coefficients merely to recover its old
name is unnecessary. Remove the public import of the retired empty stratification
module. All five theorem proofs are preserved verbatim, and no source-library file or
target signature changes. No sorry is closed or introduced by this restoration.

## Old

The active module is absent. The changed archive declarations are, verbatim:

```lean
local instance sf_locallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X

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

theorem proEtaleFlatStratification
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) (hl : l.Prime) (hlp : l ≠ D.p)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 0 < n ∧ (l ^ n) • (1 : A) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (hF : IsConstructibleProEtaleModuleSheaf X A F)
    (hflat : SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
      (R := proEtaleConstantRing X A) F) :
    ∃ str : LocallyClosedStratification X, ∀ i : Fin str.n,
      ∃ (I : Type (u + 1)) (U : I → (str.domain i).ProEt)
        (f : ∀ t : I, U t ⟶ ProEt.mk (𝟙 (str.domain i))),
        Presieve.ofArrows U f ∈ (ProEt.precoverage (str.domain i)).coverings _ ∧
        ∀ t : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} A),
          Finite M ∧ Module.Projective (ULift.{u + 1, u} A) M ∧
          Nonempty ((proEtaleConstantModulePullback (str.immersion i) A F).over (U t) ≅
            proEtaleConstantModuleSheafOver (str.domain i) A (U t) M)
```

The archive publicly imported `Sheaf.AlgebraicGeometry.LocallyClosedStratification`.

## New

```lean
local instance sf_locallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  inferInstance

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

theorem proEtaleFlatStratification
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) (hl : l.Prime) (hlp : l ≠ D.p)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 0 < n ∧ (l ^ n) • (1 : A) = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (hF : IsConstructibleProEtaleModuleSheaf X A F)
    (hflat : SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
      (R := proEtaleConstantRing X A) F) :
    ∃ str : Stratification X, ∀ i : Fin str.n,
      ∃ (I : Type (u + 1)) (U : I → (str.domain i).ProEt)
        (f : ∀ t : I, U t ⟶ ProEt.mk (𝟙 (str.domain i))),
        Presieve.ofArrows U f ∈ (ProEt.precoverage (str.domain i)).coverings _ ∧
        ∀ t : I, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} A),
          Finite M ∧ Module.Projective (ULift.{u + 1, u} A) M ∧
          Nonempty ((proEtaleConstantModulePullback (str.immersion i) A F).over (U t) ≅
            proEtaleConstantModuleSheafOver (str.domain i) A (U t) M)
```

The retired empty-module import is removed. The existing public imports of
`WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` and the intrinsic
constructibility module provide the current scheme stratification interface.

## Users

`python3 tools/downstream.py Sheaf.SixFunctors.FlatModel --uses
sfProEtaleClosureGenerators` reports `unknown module(s)` because the active item is
absent. Searching both `lean/` and `quarantine/` finds no live consumers and exactly
two archived direct importers. Neither archive is edited or withdrawn. The item and
all DAG parent obligations are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.FlatModel | G4 | Restore and migrate three stratification references and the local instance proof. |
| Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators | F3 | Archived consumer of etaleThickGeneration; its inferred stratum supports the same projections and immersion instance. No adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | Unclaimed in local records | Archived consumer of sfProEtaleClosureGenerators and proEtaleThickGeneration_eq; applies the same theorem with unchanged hypotheses. No adaptation. |

No current consumer requires compilation or adaptation. The independent reader should
compare the restored module with its quarantine source; this is an API restoration,
not a new proof or a withdrawal. No target-meaning review is reopened: the mathematical
objects used by the targets are unchanged.

## Status

landed 20261021T023310-L-2946003 2026-10-21 (merge of deliver/G4/Sheaf.SixFunctors.FlatModel)
