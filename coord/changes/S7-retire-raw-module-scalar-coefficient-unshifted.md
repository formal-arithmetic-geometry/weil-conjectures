# AlgebraicGeometry.Etale.RawModuleScalarComparison.derivedPullbackIso

## Reason

Complete the assigned retirement in coord/retire-items.tsv. The unshifted coefficient
and shift-compatibility nodes already attach to complete upstream proofs. The local
module now contains only a historical abbreviation and public reexports. Preserve the
abbreviation in the existing definition module RawModuleScalarDerivedPullbackIso,
move its two current importers to that module and the canonical upstream reexports,
and retire the redundant module. This is an actual retirement repair with zero holes.

The full abbreviation signature and body are copied verbatim. In particular, its explicit
inverse structure and reducible inv projection are retained, addressing the earlier
P2 review of RawModuleAbelianHomSourceFormula. It remains definitionally equal to
(moduleAbelianDerivedUpperStarIso Λ f).symm and to derivedPullbackIsoImpl Λ f.
Zero coefficients, identity arrows, arbitrary schemes and all universes retain exactly
the old behavior. No target statement, adopted source-library file, mathematical node
statement, proof dependency or unit route changes. Targets using the definition retain
the exact previous definition; this delivery requests the ordinary independent review
of its relocation and public import adaptations.

## Old

```lean
module

public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted

/-! The canonical coefficient identity and its historical reverse-comparison name.
(blueprint: lem-sbc-raw-scalar-coefficient-unshifted). -/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale.RawModuleScalarComparison

noncomputable abbrev derivedPullbackIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (forget Λ X).mapDerivedCategoryPlus ≅
      (forget Λ Y).mapDerivedCategoryPlus ⋙
        (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus where
  hom := (moduleAbelianDerivedUpperStarIso Λ f).inv
  inv := (moduleAbelianDerivedUpperStarIso Λ f).hom
  hom_inv_id := (moduleAbelianDerivedUpperStarIso Λ f).inv_hom_id
  inv_hom_id := (moduleAbelianDerivedUpperStarIso Λ f).hom_inv_id

end AlgebraicGeometry.Etale.RawModuleScalarComparison
```

## New

The old item path is withdrawn via deleted.txt. The following declaration is inserted
in the existing Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso module,
under its existing public section and namespace, after derivedPullbackIsoImpl:

```lean
noncomputable abbrev derivedPullbackIso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (forget Λ X).mapDerivedCategoryPlus ≅
      (forget Λ Y).mapDerivedCategoryPlus ⋙
        (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus where
  hom := (moduleAbelianDerivedUpperStarIso Λ f).inv
  inv := (moduleAbelianDerivedUpperStarIso Λ f).hom
  hom_inv_id := (moduleAbelianDerivedUpperStarIso Λ f).inv_hom_id
  inv_hom_id := (moduleAbelianDerivedUpperStarIso Λ f).hom_inv_id
```

RawModuleScalarCoefficientSquare replaces its former public import with:

```lean
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientSquare
public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso
```

RawModuleScalarSourceClassFormula replaces its former public import with:

```lean
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceClassFormula
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted
public import Sheaf.AlgebraicGeometry.RawModuleScalarSourcePrefix
public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso
```

The coefficient-square upstream module already publicly imports the canonical
coefficient-unshifted module. The source-class wrapper adds that import explicitly
because its upstream twin imports it only for its proof. Both former public importers
therefore continue to expose the old abbreviation and both canonical unshifted theorems.
The definition node gains the moved abbreviation in lean.declarations; its existing
module, main declaration, statement and mathematical dependencies stay intact.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted | S7 | Assigned retirement; its alias is preserved verbatim in the existing definition module. |
| Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso | unclaimed | Receives the unchanged public abbreviation; existing definitions, instances and proofs unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare | unclaimed | Replaces the retired public import with the existing definition module. The upstream twin already publicly imports the canonical unshifted theorems. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula | unclaimed | Replaces the retired public import with the definition module and the canonical unshifted upstream module, preserving both parts of the previous public API. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unclaimed | Only external whole-name user of derivedPullbackIso; signature and proof unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomTargetFormula | unclaimed | Downstream of the retired wrapper; unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | unclaimed | Downstream of the retired wrapper; unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation | unclaimed | Downstream of the retired wrapper; unchanged. |
| Sheaf.AlgebraicGeometry.ComparisonForgetScalars | unclaimed | Direct importer of the existing definition module; unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer | unclaimed | Direct importer of the existing definition module; unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap | unclaimed | Direct importer of the existing definition module; unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleFreeSourceAcyclic | unclaimed | Direct importer of the existing definition module; unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleFreeSourceHomBijective | unclaimed | Direct importer of the existing definition module; unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleScalarClassMorphisms | unclaimed | Direct importer of the existing definition module; unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition | unclaimed | Historically direct importer; now an already withdrawn empty module, unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors | unclaimed | Direct importer of the existing definition module; unchanged. |
| Sheaf.Paper.CartierRelativeBoundaryRealization | unclaimed | Direct importer of the existing definition module; unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquare | unclaimed | Historical retirement-row consumer; already an empty withdrawn module, unchanged. |

The six modules found by tools/downstream.py for the retired item are all listed above.
Whole-name declaration search finds only RawModuleAbelianHomSourceFormula outside the
retired file. Direct importers of the receiving definition module are listed as well.
Exact import scans include both live library roots and quarantine/. The historical
source-square and scalar-composition modules remain withdrawn; neither is restored or
removed by this delivery. No other group holds any adapted module in the current
claim records. Only the three necessary active files are delivered.

## Status

landed 20261025T071152-L-122746 2026-10-25 (merge of deliver/S7/Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted)
