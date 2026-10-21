# AlgebraicGeometry.exists_derivedPushforwardSquareMateUnit

## Reason

The adopted source module already declares exactly the same theorem with the same
complete proof. The restored Sheaf implementation independently redeclares its public
name. Use the adopted declaration through a compatibility import, preserving the
existing Sheaf import path and its existing public affine base-change import.
No source-library file is changed, no mathematical statement is changed, and no target
semantic review is reopened. The theorem signature was compared byte for byte.

## Old

Public imports and proof imports:

```lean
public import Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
import WeilConjectures.AlgebraicGeometry.DirectImageSquareUnitTransport
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate
```

The Sheaf file locally declared the following public theorem:

```lean
theorem exists_derivedPushforwardSquareMateUnit
    {R B : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R) :
    let P₀ := RingedSpace.moduleDirectImage (pullback.fst f g).toLRSHom.toShHom
    let Q₀ := RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let G₀ := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let RF := schemeDerivedDirectImage f
    let RG := schemeDerivedDirectImage g
    let a := fun {A D : Scheme.{u}} (h : A ⟶ D) ↦ canonicalPullbackAdjunction h
    let p : ∀ {X Y Z : Scheme.{u}} (h : X ⟶ Y) (i : Y ⟶ Z),
        derivedPullback i ⋙ derivedPullback h ≅ derivedPullback (h ≫ i) :=
      @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let k := p (pullback.snd f g) g ≪≫
      eqToIso (congrArg (fun h ↦ derivedPullback h)
        (pullback.condition (f := f) (g := g)).symm) ≪≫
      (p (pullback.fst f g) f).symm
    let δ := conjugateEquiv ((a f).comp (a (pullback.fst f g)))
      ((a g).comp (a (pullback.snd f g))) k.hom
    ∃ e : P₀ ⋙ F₀ ≅ Q₀ ⋙ G₀,
      (∀ (M : SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))
        (x : M.val.obj (op ⊤)), ((e.hom.app M).val.app (op ⊤)) x = x) ∧
      ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) (.up ℤ),
        F₀.rightDerivedFunctorUnit.app ((P₀.mapHomotopyCategory (.up ℤ)).obj J) ≫
          RF.map (P₀.rightDerivedFunctorUnit.app J) ≫
          δ.app (DerivedCategory.Qh.obj J) =
        DerivedCategory.Qh.map ((e.hom.mapHomotopyCategory (.up ℤ)).app J) ≫
          G₀.rightDerivedFunctorUnit.app ((Q₀.mapHomotopyCategory (.up ℤ)).obj J) ≫
          RG.map (Q₀.rightDerivedFunctorUnit.app J)
```

## New

```lean
public import Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.DerivedPushforwardSquareMateUnit
```

The identical public theorem is re-exported from the adopted source, whose signature,
proof, attributes and imports are unchanged. The node's Lean attachment now names that
source module. All three proof dependencies are retained, because the source proof
uses them. The private local helper copies and file-local elaboration settings are
removed from the compatibility module.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit
--uses AlgebraicGeometry.exists_derivedPushforwardSquareMateUnit` found zero downstream
modules and only the old local declaration. A direct source search additionally finds
the source consumer below, which already imports the adopted source module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit | J1 | Re-exports the identical source theorem; no local duplicate declaration. |
| WeilConjectures.AlgebraicGeometry.AffineSectionsSquareMatePathUnit | unclaimed | Already imports the adopted source; unchanged. |

## Status

landed 20261021T233728-L-855330 2026-10-21 (merge of deliver/J1/Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit)
