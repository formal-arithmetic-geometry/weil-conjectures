# MapExtendHomology duplicate repair

## Reason

Remove private copies of the existing HomologicalComplex.mapExtendX and
HomologicalComplex.mapExtendIso. No public declaration changes its signature.

## Old

```lean
private def mapExtendTermIso
    {D : Type u} [Category.{v} D] [Abelian D]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (E : D ⥤ B) [E.Additive] (K : CochainComplex D ℕ) (i : Option ℕ) :
    E.obj (HomologicalComplex.extend.X K i) ≅
      HomologicalComplex.extend.X ((E.mapHomologicalComplex (.up ℕ)).obj K) i :=
  match i with
  | some _ => Iso.refl _
  | none => IsZero.iso (E.map_isZero (isZero_zero D)) (isZero_zero B)

private lemma mapExtendTermIso_comm
    {D : Type u} [Category.{v} D] [Abelian D]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (E : D ⥤ B) [E.Additive] (K : CochainComplex D ℕ) (i j : Option ℕ) :
    E.map (HomologicalComplex.extend.d K i j) ≫ (mapExtendTermIso E K j).hom =
      (mapExtendTermIso E K i).hom ≫
        HomologicalComplex.extend.d ((E.mapHomologicalComplex (.up ℕ)).obj K) i j := by
  cases i <;> cases j <;>
    simp [mapExtendTermIso, HomologicalComplex.extend.d]

private def mapExtendComplexIso
    {D : Type u} [Category.{v} D] [Abelian D]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (E : D ⥤ B) [E.Additive] (K : CochainComplex D ℕ) :
    (E.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((E.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ mapExtendTermIso E K (ComplexShape.embeddingUpNat.r i))
    (fun i j _ ↦ (mapExtendTermIso_comm E K
      (ComplexShape.embeddingUpNat.r i) (ComplexShape.embeddingUpNat.r j)).symm)
```

## New

The three private declarations are removed. The unchanged public theorem uses
HomologicalComplex.mapExtendIso K ComplexShape.embeddingUpNat E in place of
mapExtendComplexIso E K. ExtendMap is a proof-only import; all original public
imports are preserved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.MapExtendHomology | N2 | Use the canonical complex isomorphism; identical public theorem signature. |
| Sheaf.Paper.FreeRepresentableHomotopyHomology | unclaimed | Its call to mapExtendHomology_nonempty_iso is unchanged; no adaptation needed. |

The removed declarations were private and had no external users.

## Status

landed 20261013T224517-L-1474380 2026-10-13 (merge of deliver/N2/Sheaf.CategoryTheory.MapExtendHomology)
