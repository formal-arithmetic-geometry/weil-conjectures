# AlgebraicGeometry.ProEtale.FiniteReductionOrigin.reductionComparison

## Reason

Restore the quarantined item with its proof. The archived definitions failed elaboration
with a stuck EssentiallySmall universe equation `u+1 = max (u+1) ?u`. Specify the existing
scheme and small-site universes and their canonical EssentiallySmall proof arguments.
The main theorem uses the same explicit arguments at each occurrence. This changes no
mathematical type, binder, coefficient object, functor or comparison map. Proof arguments
are propositionally irrelevant. No target statement or coefficient construction changes. Remove the unused public imports
`Sheaf.Paper.FiniteTorAmplitudeSites` and
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`; import the coefficient
finiteness theorem directly from `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`.
These were proof-plan imports: the retained theorem uses the source categorical Tor
amplitude and the fixed scalar adjoint, with exactly the archived mathematical meaning.

## Old

```lean
def reductionComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X : Scheme.{u}} {Ke : Etale.DerivedCategoryModule A X}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (α : (nu A X).obj Ke ≅ K) :
    (nu B X).obj ((pbcFixedScalarExtension X.smallEtaleTopology φ).obj Ke) ≅
      (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj K :=
  (pbcComparisonReduction X φ).symm.app Ke ≪≫
    (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).mapIso α

def openReductionComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    {Ke : Etale.DerivedCategoryModule A X}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (α : (nu A X).obj Ke ≅ K) :
    (nu B Z).obj ((pbcFixedScalarExtension Z.smallEtaleTopology φ).obj
      ((etaleOpen A j).obj Ke)) ≅
    (proEtaleOpen B j).obj ((pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj K) :=
  (nu B Z).mapIso ((Etale.openScalarExtension φ j).app Ke) ≪≫
    (openComparison B j).app ((pbcFixedScalarExtension X.smallEtaleTopology φ).obj Ke) ≪≫
    (proEtaleOpen B j).mapIso (reductionComparison φ α)

```

## New

```lean
def reductionComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X : Scheme.{u}} {Ke : Etale.DerivedCategoryModule A X}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (α : (nu A X).obj Ke ≅ K) :
    (nu B X).obj ((@pbcFixedScalarExtension.{u} X.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) X.smallEtaleTopology
          _ _ inferInstance inferInstance φ).obj Ke) ≅
      (@pbcFixedScalarExtension.{u} X.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
        A B inferInstance inferInstance φ).obj K :=
  (pbcComparisonReduction.{u} X φ).symm.app Ke ≪≫
    (@pbcFixedScalarExtension.{u} X.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
        A B inferInstance inferInstance φ).mapIso α

def openReductionComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    {Ke : Etale.DerivedCategoryModule A X}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (α : (nu A X).obj Ke ≅ K) :
    (nu B Z).obj ((@pbcFixedScalarExtension.{u} Z.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) Z.smallEtaleTopology
          _ _ inferInstance inferInstance φ).obj
      ((etaleOpen A j).obj Ke)) ≅
    (proEtaleOpen B j).obj ((@pbcFixedScalarExtension.{u} X.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
        A B inferInstance inferInstance φ).obj K) :=
  (nu B Z).mapIso ((Etale.openScalarExtension φ j).app Ke) ≪≫
    (openComparison B j).app ((@pbcFixedScalarExtension.{u} X.Etale inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) X.smallEtaleTopology
          _ _ inferInstance inferInstance φ).obj Ke) ≪≫
    (proEtaleOpen B j).mapIso (reductionComparison φ α)

```

## Users

`python3 tools/downstream.py Sheaf.Paper.ReductionOpenEtaleOrigin --allow-missing
--uses reductionComparison openReductionComparison reduction_open_etale_origin` returned
zero downstream modules and zero users of each declaration. A search of quarantined
Lean modules found only the restored item itself. The DAG parent
lem-fix-compact-support-coefficient-change still needs this item and is preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ReductionOpenEtaleOrigin | A3 | Explicit elaboration arguments; completed proof. |

## Status

landed 20261021T162107-L-270444 2026-10-21 (merge of deliver/A3/Sheaf.Paper.ReductionOpenEtaleOrigin)
