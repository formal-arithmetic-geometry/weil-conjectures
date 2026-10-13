# Homotopy base-change bridge statements

## Reason

Expose the two strictly smaller bridge identities used in the original node's
proof. Existing signatures, visibility and definitions remain unchanged.

## Old

The two new modules and their declarations did not exist. The item theorem
had a whole-proof sorry.

## New


`Sheaf.AlgebraicGeometry.HomotopyPullbackSquareLocalization` adds:

```lean
theorem homotopyPullbackSquare_localization
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback f).Additive]
    [(Scheme.Modules.tensorPullback f').Additive]
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive]
    (M : HomotopyCategory S.Modules (.up ℤ))
    (K : HomotopyCategory X.Modules (.up ℤ))
    (a : ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)).obj M ⟶ K) :
    let ε := @Classical.choose _ _ (Classical.choose_spec
      exists_derivedPullbackComposition.{u, w})
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    (c f' g).hom.app (DerivedCategory.Qh.obj M) ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj (DerivedCategory.Qh.obj M)) h.symm) ≫
      (c p f).inv.app (DerivedCategory.Qh.obj M) ≫
      (derivedPullback p).map ((ε f).app M ≫ DerivedCategory.Qh.map a) ≫
      (ε p).app K =
    (derivedPullback f').map ((ε g).app M) ≫
      (ε f').app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj M) ≫
      DerivedCategory.Qh.map ((moduleHomotopyPullbackSquare f f' g p h).app M ≫
        ((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).map a)
```


`Sheaf.AlgebraicGeometry.HomotopyBaseChangeCounit` adds:

```lean
theorem moduleHomotopyBaseChange_counit
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback f).Additive]
    [(Scheme.Modules.tensorPullback f').Additive]
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive]
    (D : HomotopyCategory X.Modules (.up ℤ)) :
    let af := (Classical.choose
      (Scheme.Modules.exists_tensorPullbackAdjunction f)).mapHomotopyCategory (.up ℤ)
    let af' := (Classical.choose
      (Scheme.Modules.exists_tensorPullbackAdjunction f')).mapHomotopyCategory (.up ℤ)
    let b :=
      (Functor.mapHomotopyCategoryCompIso (Iso.refl
        (Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g))
        (ComplexShape.up ℤ)).hom ≫
      NatTrans.mapHomotopyCategory
        { app := Scheme.Modules.moduleBaseChangeMap f f' g p h
          naturality := fun _ _ a ↦
            Scheme.Modules.moduleBaseChangeMap_naturality f f' g p h a }
        (ComplexShape.up ℤ) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl
        (Scheme.Modules.tensorPullback p ⋙ Scheme.Modules.pushforward f'))
        (ComplexShape.up ℤ)).inv
    (moduleHomotopyPullbackSquare f f' g p h).app
        (((Scheme.Modules.pushforward f).mapHomotopyCategory (.up ℤ)).obj D) ≫
      ((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).map
        (af.counit.app D) = (af'.homEquiv _ _).symm (b.app D)
```


The first module also constructs `AlgebraicGeometry.moduleHomotopyPullbackSquare`
by descending the composite canonical pullback comparison; its definition has no hole.

```lean
def moduleHomotopyPullbackSquare
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback f).Additive]
    [(Scheme.Modules.tensorPullback f').Additive]
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive] :
    (Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ) ⋙
        (Scheme.Modules.tensorPullback f').mapHomotopyCategory (.up ℤ) ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ) ⋙
        (Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ) := by
  let adj := fun {A B : Scheme.{u}} (k : A ⟶ B) ↦
    Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)
  let c := fun {A B C : Scheme.{u}} (k : A ⟶ B) (l : B ⟶ C) ↦
    (conjugateIsoEquiv (adj (k ≫ l)) ((adj l).comp (adj k))).symm
      (Scheme.Modules.pushforwardComp k l).symm
  let t := c f' g ≪≫
    eqToIso (congrArg Scheme.Modules.tensorPullback h.symm) ≪≫ (c p f).symm
  exact (Functor.mapHomotopyCategoryCompIso t (.up ℤ)).hom ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl
      (Scheme.Modules.tensorPullback f ⋙ Scheme.Modules.tensorPullback p)) (.up ℤ)).inv
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility | B4 | Adds a private proof import; its public interface is unchanged. |
| Sheaf.AlgebraicGeometry.HomotopyBaseChangeCounit | B4, new | Uses the real homotopy pullback square from the other new module. |

The new declarations have no pre-existing users. No existing consumer is adapted.

## Status

landed 20261013T142852-L-495894 2026-10-13 (merge of deliver/B4/Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility)
