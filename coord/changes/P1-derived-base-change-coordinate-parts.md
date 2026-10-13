# Derived base-change coordinate transport parts

## Reason

Expose the two independent restricted coordinate transport laws needed to reduce
the original theorem. Its existing signature and all definitions stay unchanged.
No new data is selected from a mere existence theorem in a definition.

## Old

The two new modules/declarations did not exist. The original coordinate-naturality
theorem had one whole-proof sorry, with its current unchanged signature.

## New

```lean
theorem exists_derivedBaseChange_base_coordinates
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g)
    {A B : Scheme.{u}} (eS : S ≅ A) (eT : S' ≅ B)
    (hA : g' ≫ (f ≫ eS.hom) =
      (f' ≫ eT.hom) ≫ (eT.inv ≫ g ≫ eS.hom)) :
    let fA := f ≫ eS.hom
    let gA := eT.inv ≫ g ≫ eS.hom
    let T := schemeDerivedDirectImage eT.inv
    ∃ b : schemeDerivedDirectImage f' ≅
        schemeDerivedDirectImage (f' ≫ eT.hom) ⋙ T,
    ∃ a : schemeDerivedDirectImage f ⋙ derivedPullback g ≅
        schemeDerivedDirectImage fA ⋙ derivedPullback gA ⋙ T,
      ∀ E : schemeDerivedCategory X,
        schemeDerivedBaseChangeMap f f' g g' h E ≫
            b.hom.app ((derivedPullback g').obj E) =
          a.hom.app E ≫ T.map
            (schemeDerivedBaseChangeMap fA (f' ≫ eT.hom) gA g' hA E)
```

```lean
theorem exists_derivedBaseChange_top_iso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S P S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (p : P ⟶ X) (q : P ⟶ S') (h : p ≫ f = q ≫ g)
    (e : X' ≅ P) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hp : e.hom ≫ p = g') (hq : e.hom ≫ q = f')
    (h' : g' ≫ f = f' ≫ g) :
    ∃ j : derivedPullback g' ⋙ schemeDerivedDirectImage e.hom ≅ derivedPullback p,
    ∃ k : schemeDerivedDirectImage f' ≅
        schemeDerivedDirectImage e.hom ⋙ schemeDerivedDirectImage q,
      ∀ E : schemeDerivedCategory X,
        schemeDerivedBaseChangeMap f f' g g' h' E ≫
            k.hom.app ((derivedPullback g').obj E) ≫
            (schemeDerivedDirectImage q).map (j.hom.app E) =
          schemeDerivedBaseChangeMap f q g p h E
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeCoordinateNaturality | P1 | Private proof imports of both new laws; unchanged signature. |

The new names have no pre-existing users. No existing module is adapted; downstream
users of the item see the same interface. No definition change reopens target review.

## Status

landed 20261013T045547-L-133504 2026-10-13 (merge of deliver/P1/Sheaf.AlgebraicGeometry.DerivedBaseChangeCoordinateNaturality)
