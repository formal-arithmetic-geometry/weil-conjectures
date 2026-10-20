# canonicalSingleBaseChangeComparison

## Reason

Restore the item from the quarantine named by coord/rework.tsv. Its archived
source does not elaborate after the upstream sync: the unqualified derivedPullback
inside AlgebraicGeometry.Scheme.Modules now resolves to the newer functor on
DerivedCategory S.Modules, whose morphisms are in universe u. The other maps in
the equation use the pinned AlgebraicGeometry.derivedPullback on the shared
schemeDerivedCategory, with morphisms in arbitrary universe w. The compiler
reports a Type w morphism where a Type u morphism is expected.

Qualify the intended functor and pin the universe arguments to the existing u,w
parameters. Retain the arbitrary module, arbitrary commutative square, all shared
derived-category instances, and the exact canonical comparison maps. This is a
name-resolution repair, not a change of the mathematical statement. Preserve the
existing complete naturality and isomorphism-cancellation proof and its declared
proof dependencies. Explicitly type the right-derived unit, respect the functors'
transparency, and remove the old initial dsimp of scheme aliases. That dsimp
exposes semireducible topological-space expressions that the current simplifier
cannot recheck at implicit transparency. Perform the reassociation needed to
combine the two identities in a proved private lemma for an arbitrary category,
so that no simplifier must rewrite a concrete scheme-derived functor expression.
The final canonical-map identification is definitional, using exact hf instead
of the old dsimp/convert sequence. The restored module compiles in 50.0 seconds
without errors or warnings. No definition, target statement, unit route, or adopted source
file is changed. There are no holes in the archived module or the restored module.

## Old

The source is preserved at
quarantine/Sheaf/AlgebraicGeometry/CanonicalSingleBaseChangeComparison.lean;
its lean/ path is absent before this restoration.

```lean
theorem canonicalSingleBaseChangeComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) (M : X.Modules) :
    (derivedPullback g).map (canonicalSingleDirectImageMap f M) ≫
      schemeDerivedBaseChangeMap f f' g p h
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) ≫
      (schemeDerivedDirectImage f').map (canonicalSinglePullbackMap p M) =
    canonicalSinglePullbackMap g ((pushforward f).obj M) ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map
        (((Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
          (pullbackPushforwardAdjunction g)).inv.app ((pushforward f).obj M) ≫
          moduleBaseChangeMap f f' g p h M ≫
          (pushforward f').map
            (((Classical.choose (exists_tensorPullbackAdjunction p)).leftAdjointUniq
              (pullbackPushforwardAdjunction p)).hom.app M)) ≫
      canonicalSingleDirectImageMap f' ((pullback p).obj M)
```

## New

```lean
theorem canonicalSingleBaseChangeComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) (M : X.Modules) :
    (AlgebraicGeometry.derivedPullback.{u, w} g).map (canonicalSingleDirectImageMap.{u, w} f M) ≫
      schemeDerivedBaseChangeMap f f' g p h
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) ≫
      (schemeDerivedDirectImage.{u, w, w} f').map (canonicalSinglePullbackMap.{u, w} p M) =
    canonicalSinglePullbackMap g ((pushforward f).obj M) ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map
        (((Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
          (pullbackPushforwardAdjunction g)).inv.app ((pushforward f).obj M) ≫
          moduleBaseChangeMap f f' g p h M ≫
          (pushforward f').map
            (((Classical.choose (exists_tensorPullbackAdjunction p)).leftAdjointUniq
              (pullbackPushforwardAdjunction p)).hom.app M)) ≫
      canonicalSingleDirectImageMap f' ((pullback p).obj M)
```

## Users

The downstream.py query reports unknown module because the item's lean/ file is
quarantined. A scan of both lean/ and quarantine/ for imports and the declaration
name finds the following two direct users; the DAG also names exactly these two
parents. Their obligations and import/dependency edges are preserved. Both
already intend the pinned comparison occurring in the repaired signature. They
remain quarantined for their own restoration; no adaptation is forced by this
name qualification. There are no current lean/ users of this declaration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CanonicalSingleBaseChangeComparison | T2 | Restore the complete proof with the intended qualified functor. |
| Sheaf.AlgebraicGeometry.CanonicalStructureMapBaseChange | unclaimed | Quarantined parent; the same pinned exchange identity remains available. |
| Sheaf.AlgebraicGeometry.Picard.TensorSingleBaseChangeSquare | unclaimed | Quarantined parent; the same universe-polymorphic comparison remains available. |

## Status

landed 20261020T235628-L-1197941 2026-10-20 (merge of deliver/T2/Sheaf.AlgebraicGeometry.CanonicalSingleBaseChangeComparison)
