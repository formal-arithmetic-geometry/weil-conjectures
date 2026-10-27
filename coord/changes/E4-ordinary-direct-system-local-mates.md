# OrdinaryDirectSystemCore

## Reason

The original `ordinaryDirectSystem_homData_exists` was false for an arbitrary
core. A core specified only vertical components and section identities. On the
one-object site with a constant nonzero coefficient ring, identity pullback and
level adjunctions, let push retain all component modules and maps but replace
every transition between distinct indices by zero. This is a functor and meets
the old core fields. For a constant nonzero identity-transition system M=N,
the requested transpose of the identity must have identity components into
push(N). Its horizontal square would read 0 = id, a contradiction.

Add the missing local mate law for two arbitrary component maps to the core.
This law concerns one horizontal square and does not assert the existence,
assembly, or inverse laws of a global Hom equivalence. The existing geometric
core construction theorem retains its hole and now supplies this local law;
its source proof already described this construction. The repaired Hom-data
theorem is completely proved by explicit assembly on the actual sequence site.
No new hole, module, axiom, or choice of arbitrary unproved data is introduced.

This is an interface repair, not a claim to have proved geometric reassembly.
The main `ordinaryDirectSystem_exists` statement and `OrdinaryDirectSystem`
record are verbatim unchanged. The revised auxiliary core definition does not
occur in any target signature or definition used by a target statement.

## Old

In the unchanged module-variable context of the item:

```lean
structure OrdinaryDirectSystemCore where
  push : Systems.{c, v, max c v r} J' F σ ⥤ Systems.{c, v, max c v r} J B τ
  component : ∀ n,
    push ⋙ evaluation.{c, v, max c v r} J B τ n ≅
      evaluation.{c, v, max c v r} J' F σ n ⋙ V n
  component_sections : ∀ n (M : Systems.{c, v, max c v r} J' F σ) (U : Cᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj (push.obj M)).val.obj U),
    HEq ((((component n).hom.app M).val.app U) x) x

structure OrdinaryDirectSystemHomData (K : OrdinaryDirectSystemCore.{c, v, r} J B τ J' F σ V) where

theorem ordinaryDirectSystem_core_exists [PreservesFiniteLimits uInv]
    (hI : ∀ n,
      uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map (τ n)) ≫
          (I n).ringUnderlying.hom =
        (I (n + 1)).ringUnderlying.hom ≫
          (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map (σ n))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush)
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (ha : ∀ n (M : Mod.{c, v, max c v r} J (B n))
      (N : Mod.{c, v, max c v r} J' (F n)) (f : (I n).modules.obj M ⟶ N),
      (underlying.{c, v, r} J (B n)).map ((a n).homEquiv M N f) ≫ (eV n).hom.app N =
        adjSet.homEquiv _ _ ((I n).moduleUnderlying.inv.app M ≫
          (underlying.{c, v, r} J' (F n)).map f)) :
    Nonempty (OrdinaryDirectSystemCore.{c, v, r} J B τ J' F σ V)

theorem ordinaryDirectSystem_homData_exists
    (K : OrdinaryDirectSystemCore.{c, v, r} J B τ J' F σ V) :
    Nonempty (OrdinaryDirectSystemHomData.{c, v, r} J B τ J' uInv F σ I P V a K)
```

## New

In the same context (P and a are now also parameters of the core):

```lean
structure OrdinaryDirectSystemCore where
  push : Systems.{c, v, max c v r} J' F σ ⥤ Systems.{c, v, max c v r} J B τ
  component : ∀ n,
    push ⋙ evaluation.{c, v, max c v r} J B τ n ≅
      evaluation.{c, v, max c v r} J' F σ n ⋙ V n
  component_sections : ∀ n (M : Systems.{c, v, max c v r} J' F σ) (U : Cᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj (push.obj M)).val.obj U),
    HEq ((((component n).hom.app M).val.app U) x) x

  transition_mate : ∀ (M : Systems.{c, v, max c v r} J B τ)
    (N : Systems.{c, v, max c v r} J' F σ) {m n : ℕ} (h : n ≤ m)
    (fm : (evaluation.{c, v, max c v r} J' F σ m).obj (P.pull.obj M) ⟶
      (evaluation.{c, v, max c v r} J' F σ m).obj N)
    (fn : (evaluation.{c, v, max c v r} J' F σ n).obj (P.pull.obj M) ⟶
      (evaluation.{c, v, max c v r} J' F σ n).obj N),
    let gm := (a m).homEquiv _ _ ((P.component m).inv.app M ≫ fm) ≫
      (component m).inv.app N
    let gn := (a n).homEquiv _ _ ((P.component n).inv.app M ≫ fn) ≫
      (component n).inv.app N
    (fm ≫ (transition.{c, v, max c v r} J' F σ h).app N =
      (transition.{c, v, max c v r} J' F σ h).app (P.pull.obj M) ≫
        (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J' F σ h)).map fn) ↔
      (gm ≫ (transition.{c, v, max c v r} J B τ h).app (push.obj N) =
        (transition.{c, v, max c v r} J B τ h).app M ≫
          (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map gn)

structure OrdinaryDirectSystemHomData
    (K : OrdinaryDirectSystemCore.{c, v, r} J B τ J' uInv F σ I P V a) where

theorem ordinaryDirectSystem_core_exists [PreservesFiniteLimits uInv]
    (hI : ∀ n,
      uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map (τ n)) ≫
          (I n).ringUnderlying.hom =
        (I (n + 1)).ringUnderlying.hom ≫
          (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map (σ n))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush)
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush)
    (ha : ∀ n (M : Mod.{c, v, max c v r} J (B n))
      (N : Mod.{c, v, max c v r} J' (F n)) (f : (I n).modules.obj M ⟶ N),
      (underlying.{c, v, r} J (B n)).map ((a n).homEquiv M N f) ≫ (eV n).hom.app N =
        adjSet.homEquiv _ _ ((I n).moduleUnderlying.inv.app M ≫
          (underlying.{c, v, r} J' (F n)).map f)) :
    Nonempty (OrdinaryDirectSystemCore.{c, v, r} J B τ J' uInv F σ I P V a)

theorem ordinaryDirectSystem_homData_exists
    (K : OrdinaryDirectSystemCore.{c, v, r} J B τ J' uInv F σ I P V a) :
    Nonempty (OrdinaryDirectSystemHomData.{c, v, r} J B τ J' uInv F σ I P V a K)
```

## Users

`tools/downstream.py` found 879 transitive importers, but its declaration-usage
scan and a source-wide rg search found these four names only in this item.
There is one direct importer. No downstream statement needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SemilinearOrdinaryDirectSystem | E4 | Pass P and a to the strengthened core; prove local-to-global Hom data. |
| Sheaf.Paper.GeometricOrdinaryRealization | unclaimed at audit | Uses only unchanged OrdinaryDirectSystem and ordinaryDirectSystem_exists; compile original against this delivery. |

## Status

landed 20261026T114137-L-2268475 2026-10-26 (merge of deliver/E4/Sheaf.Paper.SemilinearOrdinaryDirectSystem)
