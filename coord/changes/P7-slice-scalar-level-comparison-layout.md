# SheafOfModules.SliceScalarLevelComparison

## Reason

The complete proof checked but took 86 seconds in one module. Profiling showed
substantial time in the existing structure's type checking and congruence
generation. Move its unchanged data API to a support module so data generation
and proof checking each meet the 60-second limit. Private proof helpers have
already been made irreducible after proving their API.

## Old

The following declarations were in `Sheaf.CategoryTheory.SliceScalarLevelComparison`:

```lean
/-- Transport a level comparison along the specified object identifications.
Source: Stacks 03EK (blueprint: lem-sf-slice-scalar-level-comparison). -/
def sliceScalarComponentHom
    (e : ∀ G n,
      changeOfRings.{v, c, max c v r} (α.app (op n))
        ((localizedSystemExtension.{c, v, r} O U).obj G) ≅
      (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj
        (changeOfRings.{v, max c v, max c v r}
          ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G)) (G) (n : ℕ) :
    (AX.F.obj ((localizedSystemExtension.{c, v, r} O U).obj G)).level n ⟶
      (extension.F.obj (AV.F.obj G)).level n :=
  eqToHom (AX.obj_eq ((localizedSystemExtension.{c, v, r} O U).obj G) n) ≫
    (e G n).hom ≫
      (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).map
        (eqToHom (AV.obj_eq G n).symm) ≫
          eqToHom (extension.obj_eq (AV.F.obj G) n).symm

/-- Levelwise scalar projection formula and its generator equations, prior to assembling
an isomorphism of strict systems or complexes.
Source: Stacks 0E8I, 03DI, 03CY and 03EK
(blueprint: lem-sf-slice-scalar-level-comparison). -/
structure SliceScalarLevelComparison where
  /-- Its coefficient-linear component on the actual sheafified tensor objects. -/
  component : ∀ G n,
    changeOfRings.{v, c, max c v r} (α.app (op n))
      ((localizedSystemExtension.{c, v, r} O U).obj G) ≅
      (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj
        (changeOfRings.{v, max c v, max c v r}
          ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G)
  /-- The prescribed forward formula after both sheafifications. -/
  generator : ∀ G n (W : Over U) (x : G.val.obj (op W))
    (b : (B.obj (op n)).obj.obj (op W.left)),
    (component G n).hom.val.app (op W.left)
        (sliceScalarPure.{c, v, r} (α.app (op n)) _ (op W.left)
          (ringedSliceExtensionSection.{c, v, r} O U G W x) b) =
      ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U _ W
        (sliceScalarPure.{max c v, v, r}
          ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G (op W) x b)
  /-- Generator normalization uniquely specifies the B_n-linear realization. -/
  unique : ∀ G n (f :
    changeOfRings.{v, c, max c v r} (α.app (op n))
      ((localizedSystemExtension.{c, v, r} O U).obj G) ⟶
      (localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj
        (changeOfRings.{v, max c v, max c v r}
          ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G)),
    (∀ (W : Over U) (x : G.val.obj (op W))
      (b : (B.obj (op n)).obj.obj (op W.left)),
      f.val.app (op W.left)
          (sliceScalarPure.{c, v, r} (α.app (op n)) _ (op W.left)
            (ringedSliceExtensionSection.{c, v, r} O U G W x) b) =
        ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U _ W
          (sliceScalarPure.{max c v, v, r}
            ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)) G (op W) x b)) →
      f = (component G n).hom
  /-- The common underlying O-module identification of the two extensions. -/
  scalarIdentification : ∀ n F,
    (localizedSystemExtension.{c, v, r} O U).obj
      ((restrictScalars ((sheafCompose (J.over U)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map
        ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)))).obj F) ≅
      (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map
        (α.app (op n)))).obj
          ((localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj F)
  /-- This identification preserves each original direct-sum injection. -/
  scalarIdentification_generator : ∀ n F (W : Over U) (x : F.val.obj (op W)),
    (scalarIdentification n F).hom.val.app (op W.left)
        (ringedSliceExtensionSection.{c, v, r} O U _ W x) =
      ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U F W x
  /-- No other identification preserving all original summands is permitted. -/
  scalarIdentification_unique : ∀ n F (f :
    (localizedSystemExtension.{c, v, r} O U).obj
      ((restrictScalars ((sheafCompose (J.over U)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map
        ((sliceScalarAlgebra.{c, v, r} B U O α).app (op n)))).obj F) ⟶
      (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map
        (α.app (op n)))).obj
          ((localizedSystemExtension.{c, v, r} (B.obj (op n)) U).obj F)),
    (∀ (W : Over U) (x : F.val.obj (op W)),
      f.val.app (op W.left) (ringedSliceExtensionSection.{c, v, r} O U _ W x) =
        ringedSliceExtensionSection.{c, v, r} (B.obj (op n)) U F W x) →
      f = (scalarIdentification n F).hom
  /-- The forward level maps commute with every coefficient transition. -/
  transition : ∀ G {m n : ℕ} (h : m ≤ n),
    sliceScalarComponentHom B U O α AX AV extension component G n ≫
        (extension.F.obj (AV.F.obj G)).transition h =
      (AX.F.obj ((localizedSystemExtension.{c, v, r} O U).obj G)).transition h ≫
        (systemRestriction B h).map
          (sliceScalarComponentHom B U O α AX AV extension component G m)
  /-- Naturality of the forward maps at each coefficient level. -/
  naturality : ∀ {G G'} (g : G ⟶ G') n,
    (AX.F.map ((localizedSystemExtension.{c, v, r} O U).map g)).app n ≫
        sliceScalarComponentHom B U O α AX AV extension component G' n =
      sliceScalarComponentHom B U O α AX AV extension component G n ≫
        (extension.F.map (AV.F.map g)).app n

```

## New

The same declarations, with identical signatures, attributes and definition bodies,
are in `Sheaf.CategoryTheory.SliceScalarLevelComparisonBasic`; only documentation
node references change to `def-sf-slice-scalar-level-comparison-data`. The original
module publicly imports the new module and retains its original public import.
There is no mathematical statement or definition change and no target meaning changes.
The existing node `lem-sf-slice-scalar-level-comparison` gains only the relocated
data owner in `stmt_deps`. Its sole citer,
`lem-sf-semilinear-slice-scalar-generators`, still uses exactly the same existence
statement, and its unchanged Lean consumer passed compilation.
Local reducibility attributes in the proof module do not change public attributes.
No source-library module changes.

## Users

`tools/downstream.py` finds the following users; no adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SliceScalarLevelComparison | P7 | Imports the relocated data and proves existence. |
| Sheaf.CategoryTheory.SemilinearSliceScalarGenerators | unclaimed (queue done) | Same names and API remain publicly available; compiled unchanged against this delivery. |

The fully proved generic scalar/slice comparison is separated into the new
`Sheaf.CategoryTheory.SliceScalarLevelAdjunction`, imported privately by the item.
Its two public theorems provide the normalized comparison and Hom extensionality
criterion. No existing public declaration changes and no new hole is added.
The corresponding new node is `lem-sf-slice-scalar-adjunction-comparison`.

## Status

landed 20261027T065859-L-2486306 2026-10-27 (merge of deliver/P7/Sheaf.CategoryTheory.SliceScalarLevelComparison)
