# AlgebraicGeometry.Etale.rawModuleAbelianHomMap, scalarSourceFactor and rawModuleScalarSourcePrefix

## Reason

After the assigned pullback-comparison migration, the adopted upstream modules
already provide the same declarations. From the first noncomputable definition
through the end of each module, the old Sheaf source agrees verbatim with its
upstream twin after replacing RawModuleScalarComparison.forget by its definition
moduleAbelianForget. Reexport those existing constructions and retain the public
compatibility API. This avoids checking duplicate large derived data.

The original Kan comparison is identified with the canonical comparison by the
assigned item's universal adjunction regression. Relative to that migration,
these construction reexports change neither the data nor the statements.
All adopted source signatures, attributes, imports and bodies remain untouched.
No target statement or mathematical node changes, and no obligation is added.
The existing definition-node attachments now point to the upstream declarations.

## Old

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison
public import WeilConjectures.AlgebraicGeometry.RestrictedOverAbelianComplexData
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison

/-! # The fixed scalar-forgetting map on raw derived Hom

Source: Stacks Project, Tag 03FD, and the free represented sections adjunction.
(blueprint: def-sbc-raw-module-abelian-hom-map).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Forget the derived class and precompose with the map of free represented sheaves.
The coefficient identification is the unique inverse of the inverse-image mate.
Source: Stacks Project, Tag 03FD, and Tags 03D3 and 03D7.
(blueprint: def-sbc-raw-module-abelian-hom-map). -/
noncomputable def rawModuleAbelianHomMap
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (U : S.Etale) (A : Over W) :
    (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op A) ⟶
      (abelianHigherDirectImageRawPresheaf (A.hom ≫ k) q
        (restrictedOverCoefficient
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)
          A)).obj (op U) := by
  let V := RawModuleScalarComparison.forget Λ A.left
  let F := (upperStar (ModuleCat.{u + 1} Λ) A.hom).obj G
  let L := (upperStar (ModuleCat.{u + 1} Λ) (A.hom ≫ k)).obj ((freeSheaf Λ S).obj U)
  let a := (upperStar AddCommGrpCat.{u + 1} (A.hom ≫ k)).map
      (RawModuleScalarComparison.freeMap Λ S U) ≫
    RawModuleScalarComparison.pullback Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
  let b := (V.mapDerivedCategoryPlus.commShiftIso (q : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (shiftFunctor _ (q : ℤ)).map
      ((V.mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          (inv (RawModuleScalarComparison.pullback Λ A.hom G)))
  let c := (DerivedCategory.Plus.singleFunctor _ 0).map a ≫
    (V.mapDerivedCategoryPlusSingleFunctor 0).inv.app L
  exact AddCommGrpCat.ofHom
    (((Preadditive.leftComp _ c).comp (Preadditive.rightComp _ b)).comp
      (V.mapDerivedCategoryPlus.mapAddHom))

end AlgebraicGeometry.Etale
```

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackExtension

/-! # Degree-zero source factors

Source: Stacks Project, Tags 03D7 and 03Q8, and derived single comparisons.
(blueprint: def-sbc-raw-scalar-source-factors).
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
/-- The source part of the scalar comparison, as a fixed derived morphism.
Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: def-sbc-raw-scalar-source-factors). -/
noncomputable def scalarSourceFactor
    (Λ : Type (u + 1)) [CommRing Λ] {S Y : Scheme.{u}} (h : Y ⟶ S)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (E : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (t : E ⟶ (RawModuleScalarComparison.forget Λ S).obj L) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} h).obj E) ⟶
      (RawModuleScalarComparison.forget Λ Y).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStar AddCommGrpCat.{u + 1} h).map t ≫
        RawModuleScalarComparison.pullback Λ h L) ≫
    ((RawModuleScalarComparison.forget Λ Y).mapDerivedCategoryPlusSingleFunctor 0).inv.app
      ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)

/-- The first two module pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-sbc-raw-scalar-source-factors). -/
noncomputable def moduleSourceFactor
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) h').obj L) ⟶
      (upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)) :=
  rawTriangleSource (upperStar (ModuleCat.{u + 1} Λ) h) (upperStar (ModuleCat.{u + 1} Λ) h')
    (upperStar (ModuleCat.{u + 1} Λ) a)
    (DerivedCategory.Plus.singleFunctor _ 0) (DerivedCategory.Plus.singleFunctor _ 0)
    (upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus
    (upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom
    ((upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlusSingleFunctor 0).inv L

/-- The first two abelian pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-sbc-raw-scalar-source-factors). -/
noncomputable def abelianSourceFactor
    {S Y Y' : Scheme.{u}} (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (E : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} h').obj E) ⟶
      (upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar AddCommGrpCat.{u + 1} h).obj E)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.app E) ≫
    ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusSingleFunctor 0).inv.app
      ((upperStar AddCommGrpCat.{u + 1} h).obj E)

end AlgebraicGeometry.Etale
```

The source-prefix definition is likewise reused verbatim after expanding forget:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors

/-! # A concrete common source prefix

Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: def-sbc-raw-module-scalar-source-prefix).
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The source comparison followed by the forgotten class, with coefficients unprocessed.
Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: def-sbc-raw-module-scalar-source-prefix). -/
noncomputable def rawModuleScalarSourcePrefix
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :=
      (abelianSourceFactor f.left (B.hom ≫ k) (A.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) (RawModuleScalarComparison.freeAbelian S U) ≫
        (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map
          (scalarSourceFactor Λ (B.hom ≫ k) ((freeSheaf Λ S).obj U)
            (RawModuleScalarComparison.freeAbelian S U)
            (RawModuleScalarComparison.freeMap Λ S U) ≫
            (RawModuleScalarComparison.forget Λ B.left).mapDerivedCategoryPlus.map z))

end AlgebraicGeometry.Etale
```

## New

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap
public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso

/-! The canonical upstream construction and the historical scalar-forgetting API.
The definitions are unchanged after unfolding the compatibility abbreviation.
(blueprint: def-sbc-raw-module-abelian-hom-map). -/

@[expose] public section
```

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceFactors
public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso

/-! The canonical upstream construction and the historical scalar-forgetting API.
The definitions are unchanged after unfolding the compatibility abbreviation.
(blueprint: def-sbc-raw-scalar-source-factors). -/

@[expose] public section
```

The public names rawModuleAbelianHomMap, scalarSourceFactor, moduleSourceFactor,
abelianSourceFactor and rawModuleScalarSourcePrefix are supplied unchanged by these upstream modules.

The source-prefix module reexports the same construction:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourcePrefix
public import Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors

/-! The existing canonical source construction and its historical scalar API.
(blueprint: def-sbc-raw-module-scalar-source-prefix). -/

@[expose] public section
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap | unclaimed | Same public declaration and construction after the canonical comparison migration; imports preserved. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unclaimed | Same public declaration and construction after the canonical comparison migration; imports preserved. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomTargetFormula | unclaimed | Same public declaration and construction after the canonical comparison migration; imports preserved. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | unclaimed | Same public declaration and construction after the canonical comparison migration; imports preserved. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation | unclaimed | Same public declaration and construction after the canonical comparison migration; imports preserved. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula | unclaimed | Same public declaration and construction after the canonical comparison migration; imports preserved. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas | unclaimed | Same public declaration and construction after the canonical comparison migration; imports preserved. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula | unclaimed | Same public declaration and construction after the canonical comparison migration; imports preserved. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors | unclaimed | Same public declaration and construction after the canonical comparison migration; imports preserved. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourcePrefix | unclaimed | Same public declaration and construction after the canonical comparison migration; imports preserved. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquare | unclaimed | Same public declaration and construction after the canonical comparison migration; imports preserved. |

The scan lists all nine transitive importers as well as the adapted construction modules.
The compatibility imports preserve the four legacy forget names. Any target
using these constructions is subject to definition review; the equality to the
original route follows from the comparison's unit characterization. Identity
arrows, zero coefficients and empty schemes remain included.

The final 2026-10-23 source reconciliation retains RawModuleScalarPullbackComparison as a compatibility reexport with no duplicate declarations, because its H9 consumer is now quarantined. The quarantined consumer is not restored or edited. The canonical construction and equality proofs in this record are unchanged.

## Status

landed 20261024T015347-L-2367834 2026-10-24 (merge of deliver/P2/Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison)
