# AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap

## Reason

Restore the lost preferred proof at 438e3d04508 while preserving every upstream
signature, attribute, public import and non-theorem defining term. The 2026-10-20
sync moved five comparison definitions back into upstream SmoothBaseChange. The
old ComparisonCounit and ComparisonSquare proof imports now reach that upstream
module through SmoothBaseChangeComparisons, so restoring those imports creates a
cycle. Reuse their existing proved arguments through lower Core interfaces whose
statements expand the fixed comparison constants to their exact defining expressions.
No new definition of a comparison is introduced: the expansions are lambda terms,
using the same constructors and proof-irrelevant IsIso evidence. All hypotheses
and universes are retained. The original helper modules keep their public interfaces,
imports and proofs unchanged; no consumer loses a public import.

The ordinary path constructions never used the five upstream comparisons. Relocate
those declarations verbatim into ComparisonSquarePathsCore, with their existing
DAG attachment. ComparisonSquarePaths retains both original public imports and
publicly re-exports the core. The lower core therefore does not reach the upstream
module. This is the necessary import-cycle repair, with identical mathematical data.
No target signature or definition changes, and no target semantic review reopens.

Each lower helper module carries its existing mathematical node; no new node or
proof obligation is added. ComparisonCounitCore uses the original counit argument,
with explicit adjunction arguments in its previously unconstrained rewrite.
The two path-normalization cores use the existing arguments with comparison formulas
expanded. ComparisonSquareTransportCore and ComparisonSquareCore combine them exactly
as before. Their namespace is AlgebraicGeometry.ProEtale.ComparisonCore so they do
not collide with any existing declaration. The source imports the counit and square
cores privately, and adds the original proved private comparison_mate_transport.
Please register these private helpers and Sheaf proof imports in the upstream sync
exception table; the worker has not changed that maintainer-owned file.

## Old

ComparisonSquarePaths, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons
public import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence

/-! # The two ordinary comparison paths and their common derived endpoints

Source: blueprint comparison-square transport, expanded proof step 4.
(blueprint: stage3-proetale-comparison-square-paths)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Paths

variable {A B B' C P Q Q' R : Type*}
  [Category A] [Category B] [Category B'] [Category C]
  [Category P] [Category Q] [Category Q'] [Category R]

/-- The comparison path passing through the first square.
Source: blueprint comparison-square transport, expanded proof step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
noncomputable def comparisonSquareEtalePathOfData
    (s : ComparisonSquareData A B B' C P Q Q' R) :
    (s.L₁ ⋙ s.L₂) ⋙ s.K₂ ≅ s.K₀ ⋙ (s.R₁' ⋙ s.R₂') :=
  Functor.isoWhiskerRight s.se s.K₂ ≪≫
    Functor.isoWhiskerLeft s.L₁' s.c₂' ≪≫ Functor.isoWhiskerRight s.c₁' s.R₂'

/-- The comparison path passing through the second square.
Source: blueprint comparison-square transport, expanded proof step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
noncomputable def comparisonSquareProEtalePathOfData
    (s : ComparisonSquareData A B B' C P Q Q' R) :
    (s.L₁ ⋙ s.L₂) ⋙ s.K₂ ≅ s.K₀ ⋙ (s.R₁' ⋙ s.R₂') :=
  Functor.isoWhiskerLeft s.L₁ s.c₂ ≪≫ Functor.isoWhiskerRight s.c₁ s.R₂ ≪≫
    Functor.isoWhiskerLeft s.K₀ s.sp

/-- Component coherence identifies the two specified ordinary paths.
Source: extensionality of natural transformations; blueprint transport step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
theorem comparisonSquarePaths_eq (s : ComparisonSquareData A B B' C P Q Q' R)
    (h : ∀ F, ComparisonSquareComponent s F) :
    comparisonSquareEtalePathOfData s = comparisonSquareProEtalePathOfData s := by
  apply Iso.ext
  apply NatTrans.ext
  funext F
  simpa only [comparisonSquareEtalePathOfData, comparisonSquareProEtalePathOfData,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] using (h F).symm

end Paths

variable (Λ : Type (u + 1)) [CommRing Λ]
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The ordinary path through the etale square, followed by its two comparison maps.
Source: blueprint comparison-square transport, step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
noncomputable def comparisonSquareEtalePath (cs : ChosenCartesianSquare g' f' f g) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙
        Etale.upperStar (ModuleCat.{u + 1} Λ) f') ⋙ ν^*(X')[ModuleCat.{u + 1} Λ] ≅
      ν^*(Y)[ModuleCat.{u + 1} Λ] ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f ⋙ upperStar (ModuleCat.{u + 1} Λ) g') :=
  comparisonSquareEtalePathOfData (comparisonSquareData (ModuleCat.{u + 1} Λ) g' f' f g cs)

/-- The ordinary path through the two comparison maps, followed by the pro-etale square.
Source: blueprint comparison-square transport, step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
noncomputable def comparisonSquareProEtalePath (cs : ChosenCartesianSquare g' f' f g) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙
        Etale.upperStar (ModuleCat.{u + 1} Λ) f') ⋙ ν^*(X')[ModuleCat.{u + 1} Λ] ≅
      ν^*(Y)[ModuleCat.{u + 1} Λ] ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f ⋙ upperStar (ModuleCat.{u + 1} Λ) g') :=
  comparisonSquareProEtalePathOfData (comparisonSquareData (ModuleCat.{u + 1} Λ) g' f' f g cs)

/-- The common source comparison from derivation of the ordinary triple composite.
Source: exact-functor composition comparisons, blueprint transport step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
noncomputable def comparisonSquareSourceIso (g : Y' ⟶ Y) (f' : X' ⟶ Y') :
    D((Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙
        Etale.upperStar (ModuleCat.{u + 1} Λ) f') ⋙ ν^*(X')[ModuleCat.{u + 1} Λ]) ≅
      D(Etale.upperStar (ModuleCat.{u + 1} Λ) g) ⋙
        D(Etale.upperStar (ModuleCat.{u + 1} Λ) f') ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ]) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso _ _) _

/-- The common target comparison to the two total left derived pullbacks.
Source: exact-functor composition comparisons, blueprint transport step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
noncomputable def comparisonSquareTargetIso (g' : X' ⟶ X) (f : X ⟶ Y) :
    D(ν^*(Y)[ModuleCat.{u + 1} Λ] ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f ⋙ upperStar (ModuleCat.{u + 1} Λ) g')) ≅
      D(ν^*(Y)[ModuleCat.{u + 1} Λ]) ⋙
        L(upperStar (ModuleCat.{u + 1} Λ) f) ⋙ L(upperStar (ModuleCat.{u + 1} Λ) g') :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f).symm _ ≪≫
        Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g').symm)

/-- The exact derived image of one ordinary path with the common endpoint factors.
This is a concrete composite; its arguments retain the entire ordinary isomorphism.
Source: exact derivation and blueprint comparison-square transport, step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
noncomputable def comparisonSquareDerivedPath
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (e : (Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙
        Etale.upperStar (ModuleCat.{u + 1} Λ) f') ⋙ ν^*(X')[ModuleCat.{u + 1} Λ] ≅
      ν^*(Y)[ModuleCat.{u + 1} Λ] ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f ⋙ upperStar (ModuleCat.{u + 1} Λ) g'))
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (DerivedCategory.Plus.ι ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ])).obj
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f').obj
          (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M)) ⟶
      L(upperStar (ModuleCat.{u + 1} Λ) g').obj
        (L(upperStar (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ])).obj M)) :=
  (comparisonSquareSourceIso Λ g f').inv.app M.obj ≫
    (Functor.mapDerivedCategoryNatIso e).hom.app M.obj ≫
    (comparisonSquareTargetIso Λ g' f).hom.app M.obj

end AlgebraicGeometry.ProEtale
```

Upstream comparison_derivedBaseChangeMap has its current unchanged statement and the
body `sorry`. The existing five public comparison definitions remain upstream.
The old ComparisonCounit and ComparisonSquare family import the upstream comparisons.

## New

ComparisonSquarePaths, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons
public import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence
public import Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquarePathsCore

/-! # The two ordinary comparison paths and their common derived endpoints

Source: blueprint comparison-square transport, expanded proof step 4.
(blueprint: stage3-proetale-comparison-square-paths)
-/

```

ComparisonSquarePathsCore contains every declaration from the old file verbatim,
from `@[expose] public section` onward. Its imports are the lower upstream etale
smooth-base-change Derived module, ProEtale UpperLowerStar and Comparison modules,
and ComparisonPullbackCoherence. It does not import upstream SmoothBaseChange.

New lower helper modules, each carrying the corresponding existing node:

- ComparisonCounitCore: stage3-proetale-comparison-counit.
- ComparisonSquareEtalePathNormalizationCore:
  stage3-proetale-comparison-square-etale-path-normalization.
- ComparisonSquareProEtalePathNormalizationCore:
  stage3-proetale-comparison-square-proetale-path-normalization.
- ComparisonSquareTransportCore: stage3-proetale-comparison-square-transport.
- ComparisonSquareCore: stage3-proetale-comparison-square.

They prove the same fixed-map equations by the same arguments, with direct lambda
expansions of upstream definitions in the signatures. Existing helper modules are
not edited or withdrawn. Upstream comparison_derivedBaseChangeMap now has the recovered
mate calculation applying the lower counit and square lemmas.

## Users

All direct and transitive consumers of the relocated paths retain identical public
names, types and defining terms through the wrapper. All existing helper consumers
retain their exact original modules. No consumer needs a statement adaptation.
The following list is computed from the current source import graph; local claim
records identify holders. New lower interfaces have no pre-existing consumers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompactSupportProperFactor | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactSupportSiteComparisonOpen | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.ClosedSectionCompactOrigin | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.FiniteCompactSiteCoherence | B4 | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.FiniteSiteTowerPaste | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.LineKummerFieldRealization | J9 | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.ProductExchangeCounitCoordinates | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.ProperOpenCoefficientMate | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.SectionCompactSourceExchange | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartAdmissibility | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.SystemCompatibleCompositorNormalization | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.TowerP1CoefficientCoordinates | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.TowerP1EtaleOriginComparisons | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.TowerP1FixedTotalTensor | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.TowerP1FormulaLevelComparisons | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.TowerP1GeometricCoordinates | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.TowerP1LevelWords | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.TowerP1OrdinaryPushCoordinates | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.TowerP1ProjectionLevelComparisons | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.TowerP1ProjectiveCoordinates | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.TowerP1PushCoordinates | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.TowerP1TensorChainCoordinates | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.TowerP1TensorCoordinates | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.Paper.TowerP1TensorOrdinaryCoordinates | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquare | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareEtalePathNormalization | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareProEtalePathNormalization | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareTransport | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Same public names, signatures and defining terms; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | K2 | Assigned item; theorem proof restored from lower interfaces, public signature unchanged. |

## Status

landed 20261024T204623-L-3807184 2026-10-24 (merge of deliver/K2/WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange)
