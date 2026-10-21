# SheafOfModules.ringedSlicePullbackMateNormalization

## Reason

Server preflight flags the added local attributes and universe commands as possible
changes to the environment visible to importers. This record documents their local
scope. The retained candidate and even an unchanged-source diagnostic exceeded the
fixed 60-second compile limit. Profiling identified repeated sheaf-composition and
derived-category instance searches, and expansion of the ordinary adjunction.

The proof now uses fully proved private categorical helpers and a degreewise ordinary
transpose API. Locally prioritizing Mathlib's all-limits sheaf-composition instance
avoids its more general multicospan-limit instance search. Local irreducibility keeps
the concrete restriction, pullback, pushforward and adjunction constructions behind
those APIs. The entire file compiled without warnings in 44.8 seconds. The server
wall-clock limit remains 60 seconds.

No existing public signature, definition body, public import, structure field, or
exported attribute changes. No source-library module is edited. No axiom or new hole
is introduced. The change in local elaboration environment is recorded conservatively;
it does not require an adaptation or a target-statement review.

## Old

The original header environment is verbatim:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules
```

The existing theorem signature is verbatim:

```lean
theorem ringedSlicePullbackMateNormalization
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)] (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (u.obj V)))]
    (e : RingedSliceDerivedImage.{u, w} u a)
    (l : RingedSliceDerivedImage.{u, w} (Over.post (X := V) u)
      (localizedRingedSiteMap u a V))
    (d : RingedSliceAdjunctionSquare e.adjunction l.adjunction
      (ringedSliceRestriction.{u, w} R V) (ringedSliceRestriction.{u, w} S (u.obj V)))
    (hnormal : ∀ (I : CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ),
      (ringedSliceRestriction.{u, w} R V).map
          (X := DerivedCategory.Q.{w}.obj
            (((ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ)).obj I))
          (Y := e.right.obj (DerivedCategory.Q.{w}.obj I)) (e.eta.app I) ≫
        d.beta.hom.app (DerivedCategory.Q.{w}.obj I) ≫
        l.right.map
          (X := (ringedSliceRestriction.{u, w} S (u.obj V)).obj (DerivedCategory.Q.{w}.obj I))
          (Y := DerivedCategory.Q.{w}.obj
            ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj I))
          ((ringedSliceRestrictionFactors.{u, w} S (u.obj V)).hom.app I) =
      (ringedSliceRestrictionFactors.{u, w} R V).hom.app
          (((ringedSliceModulePushforward u a).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.{w}.map (ringedSlicePushforwardComplexIso u a V I).hom ≫
        l.eta.app ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u}
          J S (u.obj V)).obj I)) :
    (∀ (P : CochainComplex (SheafOfModules.{u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ℤ),
      P.IsKFlatIndependentCoefficients → (∀ n : ℤ, (P.X n).IsFlat) →
      CochainComplex.IsKFlatIndependentCoefficients
          ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P) ∧
        (∀ n : ℤ, IsFlat (R := R.over V)
          (((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P).X n)) ∧
        IsIso (e.epsilon.app P) ∧
        IsIso (l.epsilon.app
          ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P)) ∧
        d.lambda.hom.app (DerivedCategory.Q.{w}.obj P) ≫
            (ringedSliceRestriction.{u, w} S (u.obj V)).map (e.epsilon.app P) ≫
            (ringedSliceRestrictionFactors.{u, w} S (u.obj V)).hom.app
              (((ringedSliceModulePullback u a).mapHomologicalComplex (.up ℤ)).obj P) =
          l.left.map ((ringedSliceRestrictionFactors.{u, w} R V).hom.app P) ≫
            l.epsilon.app
              ((CategoryTheory.ringedSliceComplexRestriction.{u, u, u} K R V).obj P) ≫
            DerivedCategory.Q.{w}.map (ringedSlicePullbackComplexMap u a V P)) ∧
      (mateEquiv e.adjunction l.adjunction
        (TwoSquare.mk _ _ _ _ d.lambda.hom)).natTrans = d.beta.hom ∧
      ∀ M : ringedSiteDerived.{u, w} S,
        l.adjunction.homEquiv _ _
          (d.lambda.hom.app (e.right.obj M) ≫
            (ringedSliceRestriction.{u, w} S (u.obj V)).map (e.adjunction.counit.app M)) =
          d.beta.hom.app M
```

Its old proof is `:= by sorry`. The preceding public definition
`SheafOfModules.ringedSlicePullbackComplexMap`, including its statement and full
chain-map body, is preserved verbatim.

## New

The theorem signature remains exactly the one above; its proof is complete.
The new header environment is verbatim:

```lean
set_option autoImplicit false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 256

universe u w v x

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

attribute [local implicit_reducible] DerivedCategory HomotopyCategory
  SheafOfModules.instCategory SheafOfModules.instAbelian

attribute [local instance 20000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
  CategoryTheory.siteAbelianHasSheafify
  CategoryTheory.siteAbelianWEqualsLocallyBijective
```

The added universes `v` and `x` parameterize only the private categorical helper.
They are not extra parameters of either existing public declaration. The private
helpers are `normalizeRepresentative`, `unitOfNormalized`,
`slicePushforward_hom_eq_id`, `ordinaryTranspose`, and `epsilon_isIso`.
Their binder variables are declaration-local and all five helpers are proved.

The later attributes are also local:

```lean
attribute [local irreducible] ringedSliceRestriction ringedSliceRestrictionFactors
  HomologicalComplex.quasiIso ringedSliceModulePullback ringedSliceModulePushforward
  ringedSliceModuleAdjunction
```

The final theorem uses this declaration-scoped heartbeat budget:

```lean
set_option maxHeartbeats 400000 in
-- The comparison uses both complex and derived adjunction presentations.
```

This does not raise the server compile time limit. The declaration needs to elaborate
both ordinary and derived adjunction interfaces. Profiling options and diagnostic
heartbeat settings are removed. The original public imports remain unchanged;
proof-only imports and the node's proof dependencies follow the completed argument.
The public theorem's proof docstring is updated to match the actual argument.

## Users

`python3 tools/downstream.py Sheaf.Paper.RingedSlicePullbackMateNormalization
--uses ringedSlicePullbackComplexMap ringedSlicePullbackMateNormalization` reports
zero downstream modules and only the item itself as a textual user of either public
name. The DAG's prospective parent dependencies are retained: zero current importers
is not being used to withdraw any statement or module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingedSlicePullbackMateNormalization | M4 | One hole proved; public statement and comparison data unchanged; local proof elaboration optimized. |

There are no adaptations to other groups' files. Importers retain the same public
statements, definition data, imports, and exported attributes. Their statements do
not become stronger, weaker, or different.

## Status

landed 20261021T111338-L-77375 2026-10-21 (merge of deliver/M4/Sheaf.Paper.RingedSlicePullbackMateNormalization)
