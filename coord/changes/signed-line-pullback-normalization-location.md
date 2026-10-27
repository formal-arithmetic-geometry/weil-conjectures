# SignedLinePullbackNormalized and SignedLineScalarPullbackSquare

## Reason

Move the two predicates to SignedLinePullbackNormalization so separate construction and naturality statements can use them without importing the theorem that uses those statements. The original module publicly re-exports the new module. No predicate body, declaration signature, target or interpretation changes.

## Old

In Sheaf.Paper.SignedLineScalarPullbackSquare:

```lean
def SignedLinePullbackNormalized
    {R : Sheaf J CommRingCat.{max u v w}} {R' : Sheaf K CommRingCat.{max u v w}}
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (L : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (L' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (p : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj L ≅ L')
    (P : ∀ m : ℤ, (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj
        (signedLinePower.{u, v, w} L m) ≅ signedLinePower.{u, v, w} L' m) : Prop :=
  (∀ (V : C) (r : R.obj.obj (op V)),
    (P 0).hom.val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        (signedLinePower.{u, v, w} L 0) V r) = a.hom.app (op V) r) ∧
  (P 1).hom = p.hom ∧
  (∀ (n : ℕ) (V : C) (x : (scalarTensorPower R L (n + 1)).val.obj (op V))
    (y : L.val.obj (op V)),
    (P (.ofNat (n + 2))).hom.val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        (scalarTensorPower R L (n + 2)) V
          (siteSheafTensorTmul (scalarTensorPower R L (n + 1)) L (op V) x y)) =
      siteSheafTensorTmul (scalarTensorPower R' L' (n + 1)) L' (op (U.obj V))
        ((P (.ofNat (n + 1))).hom.val.app (op (U.obj V))
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
            (scalarTensorPower R L (n + 1)) V x))
        (p.hom.val.app (op (U.obj V))
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
            L V y))) ∧
  (∀ (n : ℕ) (V : C)
    (φ : (signedLinePower.{u, v, w} L (.negSucc n)).val.obj (op V))
    (x : (scalarTensorPower R L (n + 1)).val.obj (op V)),
    (((P (.negSucc n)).hom.val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        (signedLinePower.{u, v, w} L (.negSucc n)) V φ)).app
          (op (Over.mk (𝟙 (U.obj V)))))
      ((P (.ofNat (n + 1))).hom.val.app (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          (scalarTensorPower R L (n + 1)) V x)) =
      a.hom.app (op V) (φ.app (op (Over.mk (𝟙 V))) x))

/-- The actual scalar/pullback square, tested on its canonical local generators.
Source: Stacks 03EL, tensor balancing; blueprint first-line square; node proof steps 2, 8.
(blueprint: lem-pur-signed-line-scalar-pullback-square)
Under Θ, the pulled image of x tensor s is (pulled x tensor 1) tensor b(s).
Thus this equation is exactly q F_S(c) = c' (p tensor 1) Θ. Equality on these
sections determines the two morphisms by scalar-extension and pullback adjunctions.
No surjectivity of the sectionwise sheafification unit is assumed. -/
def SignedLineScalarPullbackSquare
    {R S : Sheaf J CommRingCat.{max u v w}}
    {R' S' : Sheaf K CommRingCat.{max u v w}} (ι : R ⟶ S) (ι' : R' ⟶ S')
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (b : (sheafCompose J (forget₂ CommRingCat RingCat)).obj S ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S'))
    (L : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (L' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (N' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S'))
    (c : changeOfRingsOfUniverses ι L ≅ N)
    (c' : changeOfRingsOfUniverses ι' L' ≅ N')
    (p : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj L ≅ L')
    (q : (ringedSitePullbackFunctor b
      (module_pushforward_isRightAdjoint_of_universes b)).obj N ≅ N') : Prop :=
  ∀ (V : C) (x : L.val.obj (op V)) (s : S.obj.obj (op V)),
    q.hom.val.app (op (U.obj V))
      ((ringedSitePullbackFunctor b (module_pushforward_isRightAdjoint_of_universes b)).map
        c.hom |>.val.app (op (U.obj V))
          (ringedSitePullbackSection b (module_pushforward_isRightAdjoint_of_universes b)
            (changeOfRingsOfUniverses ι L) V (scalarExtensionSection ι L (op V) s x))) =
      c'.hom.val.app (op (U.obj V))
        (scalarExtensionSection ι' L' (op (U.obj V)) (b.hom.app (op V) s)
          (p.hom.val.app (op (U.obj V))
            (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
              L V x)))
```

## New

Exactly the same definitions, verbatim, in Sheaf.Paper.SignedLinePullbackNormalization, publicly imported by the original module.

```lean
def SignedLinePullbackNormalized
    {R : Sheaf J CommRingCat.{max u v w}} {R' : Sheaf K CommRingCat.{max u v w}}
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (L : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (L' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (p : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj L ≅ L')
    (P : ∀ m : ℤ, (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj
        (signedLinePower.{u, v, w} L m) ≅ signedLinePower.{u, v, w} L' m) : Prop :=
  (∀ (V : C) (r : R.obj.obj (op V)),
    (P 0).hom.val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        (signedLinePower.{u, v, w} L 0) V r) = a.hom.app (op V) r) ∧
  (P 1).hom = p.hom ∧
  (∀ (n : ℕ) (V : C) (x : (scalarTensorPower R L (n + 1)).val.obj (op V))
    (y : L.val.obj (op V)),
    (P (.ofNat (n + 2))).hom.val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        (scalarTensorPower R L (n + 2)) V
          (siteSheafTensorTmul (scalarTensorPower R L (n + 1)) L (op V) x y)) =
      siteSheafTensorTmul (scalarTensorPower R' L' (n + 1)) L' (op (U.obj V))
        ((P (.ofNat (n + 1))).hom.val.app (op (U.obj V))
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
            (scalarTensorPower R L (n + 1)) V x))
        (p.hom.val.app (op (U.obj V))
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
            L V y))) ∧
  (∀ (n : ℕ) (V : C)
    (φ : (signedLinePower.{u, v, w} L (.negSucc n)).val.obj (op V))
    (x : (scalarTensorPower R L (n + 1)).val.obj (op V)),
    (((P (.negSucc n)).hom.val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        (signedLinePower.{u, v, w} L (.negSucc n)) V φ)).app
          (op (Over.mk (𝟙 (U.obj V)))))
      ((P (.ofNat (n + 1))).hom.val.app (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          (scalarTensorPower R L (n + 1)) V x)) =
      a.hom.app (op V) (φ.app (op (Over.mk (𝟙 V))) x))

/-- The actual scalar/pullback square, tested on its canonical local generators.
Source: Stacks 03EL, tensor balancing; blueprint first-line square; node proof steps 2, 8.
(blueprint: lem-pur-signed-line-scalar-pullback-square)
Under Θ, the pulled image of x tensor s is (pulled x tensor 1) tensor b(s).
Thus this equation is exactly q F_S(c) = c' (p tensor 1) Θ. Equality on these
sections determines the two morphisms by scalar-extension and pullback adjunctions.
No surjectivity of the sectionwise sheafification unit is assumed. -/
def SignedLineScalarPullbackSquare
    {R S : Sheaf J CommRingCat.{max u v w}}
    {R' S' : Sheaf K CommRingCat.{max u v w}} (ι : R ⟶ S) (ι' : R' ⟶ S')
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (b : (sheafCompose J (forget₂ CommRingCat RingCat)).obj S ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S'))
    (L : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (L' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (N' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S'))
    (c : changeOfRingsOfUniverses ι L ≅ N)
    (c' : changeOfRingsOfUniverses ι' L' ≅ N')
    (p : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj L ≅ L')
    (q : (ringedSitePullbackFunctor b
      (module_pushforward_isRightAdjoint_of_universes b)).obj N ≅ N') : Prop :=
  ∀ (V : C) (x : L.val.obj (op V)) (s : S.obj.obj (op V)),
    q.hom.val.app (op (U.obj V))
      ((ringedSitePullbackFunctor b (module_pushforward_isRightAdjoint_of_universes b)).map
        c.hom |>.val.app (op (U.obj V))
          (ringedSitePullbackSection b (module_pushforward_isRightAdjoint_of_universes b)
            (changeOfRingsOfUniverses ι L) V (scalarExtensionSection ι L (op V) s x))) =
      c'.hom.val.app (op (U.obj V))
        (scalarExtensionSection ι' L' (op (U.obj V)) (b.hom.app (op V) s)
          (p.hom.val.app (op (U.obj V))
            (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
              L V x)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SignedLineScalarPullbackSquare | D6 | Imports and uses unchanged definitions; theorem proof changed. |
| Sheaf.Algebra.Homology.SignedLineDerivedBaseChange | unclaimed in shared snapshot | Same names, signatures and bodies through public re-export; no adaptation. |
| Sheaf.Paper.IntegralTwistSchemeCompatibility | unclaimed in shared snapshot | Same scalar-square predicate through public re-export; no adaptation. |

The downstream.py --uses scans report exactly these existing textual users (plus the item itself). There are 381 transitive importers; their public interface remains the same. No target statement or referenced definition changes mathematically, so no statement review is reopened for semantic change.

## Status

landed 20261024T184859-L-3243522 2026-10-24 (merge of deliver/D6/Sheaf.Paper.SignedLineScalarPullbackSquare)
