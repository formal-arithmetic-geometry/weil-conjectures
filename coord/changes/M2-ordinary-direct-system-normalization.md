# ordinaryDirectSystem_core_data_exists and ordinaryDirectSystem_core_transition_mate_exists

## Reason

STATEMENT-DISPUTED (former assertion): component data alone do not determine horizontal maps. On the one-object site with a constant nonzero ring and identity adjoints, the functor retaining levels and replacing every strict transition between distinct indices by zero has identity component isomorphisms. The two identity component maps of a constant tower satisfy the source square, while their transposes would require zero = identity. Add the actual horizontal normalization of D; its existence is proved in the components node.

The component existence theorem is strengthened to produce exactly this normalization. The core, Hom-data and final ordinary-direct-system statements are unchanged. The mate predicate and theorem move to SemilinearOrdinaryDirectSystemMate, publicly reexported by the item module. The normalized coefficient comparisons are proved in the new SemilinearOrdinaryDirectRestrictions module; the construction and its public auxiliary declarations move to the new CoreData module to keep individual compilation within the required limit; the original module publicly reexports it. No source-library module or target declaration changes.

## Old

```lean
theorem ordinaryDirectSystem_core_data_exists [PreservesFiniteLimits uInv]
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
    Nonempty (OrdinaryDirectSystemCoreData.{c, v, r} (J := J) (B := B) (τ := τ)
      (J' := J') (F := F) (σ := σ) (V := V))
```

```lean
theorem ordinaryDirectSystem_core_transition_mate_exists [PreservesFiniteLimits uInv]
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
          (underlying.{c, v, r} J' (F n)).map f))
    (D : OrdinaryDirectSystemCoreData.{c, v, r} (J := J) (B := B) (τ := τ)
      (J' := J') (F := F) (σ := σ) (V := V)) :
    OrdinaryDirectSystemCoreTransitionMate.{c, v, r} (J := J) (B := B) (τ := τ)
      (J' := J') (F := F) (σ := σ) (I := I) (P := P) (V := V) (a := a) (D := D)
```

## New

```lean
theorem ordinaryDirectSystem_core_data_exists [PreservesFiniteLimits uInv]
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
    ∃ D : OrdinaryDirectSystemCoreData.{c, v, r} (J := J) (B := B) (τ := τ)
        (J' := J') (F := F) (σ := σ) (V := V),
      OrdinaryDirectSystemCoreNormalized.{c, v, r} J B τ J' F σ V D uPush eV
```

```lean
theorem ordinaryDirectSystem_core_transition_mate_exists [PreservesFiniteLimits uInv]
    (_hI : ∀ n,
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
          (underlying.{c, v, r} J' (F n)).map f))
    (D : OrdinaryDirectSystemCoreData.{c, v, r} (J := J) (B := B) (τ := τ)
      (J' := J') (F := F) (σ := σ) (V := V))
    (hD : OrdinaryDirectSystemCoreNormalized.{c, v, r} J B τ J' F σ V D uPush eV) :
    OrdinaryDirectSystemCoreTransitionMate.{c, v, r} (J := J) (B := B) (τ := τ)
      (J' := J') (F := F) (σ := σ) (I := I) (P := P) (V := V) (a := a) (D := D)
```

The new predicate `OrdinaryDirectSystemCoreNormalized` says that the underlying horizontal maps conjugated by the component and `eV` isomorphisms are `uPush` of the original transition maps. Its full definition is in `lean/Sheaf/Paper/SemilinearOrdinaryDirectSystemCoreData.lean`.

```lean
def OrdinaryDirectSystemCoreNormalized
    (D : OrdinaryDirectSystemCoreData.{c, v, r} (J := J) (B := B) (τ := τ)
      (J' := J') (F := F) (σ := σ) (V := V))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (eV : ∀ n, V n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (F n) ⋙ uPush) : Prop :=
  ∀ (N : Systems.{c, v, max c v r} J' F σ) {m n : ℕ} (h : n ≤ m),
    (underlying.{c, v, r} J (B m)).map
        ((transition.{c, v, max c v r} J B τ h).app (D.push.obj N)) ≫
      (underlying.{c, v, r} J (B n)).map ((D.component n).hom.app N) ≫
      (eV n).hom.app ((evaluation.{c, v, max c v r} J' F σ n).obj N) =
    (underlying.{c, v, r} J (B m)).map ((D.component m).hom.app N) ≫
      (eV m).hom.app ((evaluation.{c, v, max c v r} J' F σ m).obj N) ≫
      uPush.map ((underlying.{c, v, r} J' (F m)).map
        ((transition.{c, v, max c v r} J' F σ h).app N))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SemilinearOrdinaryDirectSystem | M2 | Pass the constructed normalization to the repaired mate lemma; all final public structures and theorem signatures remain the same. |
| Sheaf.Paper.GeometricOrdinaryRealization | unclaimed | Direct importer; uses only the unchanged OrdinaryDirectSystem and ordinaryDirectSystem_exists interfaces. Compile the unchanged source against the delivery. |

The auxiliary theorem names occur in no other Lean module. DAG citers are the core node and (for components) the mate node; the corrected component existence satisfies each use. The unit route is unchanged.

## Status

landed 20261026T152657-L-1147431 2026-10-26 (merge of deliver/M2/Sheaf.Paper.SemilinearOrdinaryDirectSystem)
