# exists_relativeTensorPullback_balanced_natural

## Reason

The conservative interface checker records added open, variable, notation and option
commands as interface changes. This delivery adds local notation and variables for
private proof helpers, opens TopologicalSpace and ChangeOfRings for the tensor syntax,
and enables backward defeq attributes for elaboration. It also scopes heartbeat
options to individual proofs. None of these commands changes an exported declaration
or a mathematical definition. No original public import is removed. The three new
proof imports are private. The new public invertibility criterion has its own node.

## Old

The public theorem has this signature:

```lean
theorem exists_relativeTensorPullback_balanced_natural
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hG : ∀ M, G.obj M = Modules.tensorPullbackObj f M)
    (hGmap : ∀ {M N} (a : M ⟶ N),
      G.map a = eqToHom (hG M) ≫ Modules.tensorPullbackMap f a ≫ eqToHom (hG N).symm) :
    let R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (TopCat.Sheaf.inverseImageRing f.base S.sheaf))
    let U := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
    let V := SheafOfModules.toSheaf R
    let H := SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map (Modules.tensorPullbackRingMap f))
    let I := TopCat.Sheaf.inverseImageModuleFunctor f.base S.sheaf
    let T := @curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)
    let T' := @curriedTensor _ _ (SheafOfModules.monoidalCategory
      (TopCat.Sheaf.inverseImageRing f.base S.sheaf))
    ∃ e : ∀ M N, U.obj ((T.obj M).obj (G.obj N)) ≅
        V.obj ((T'.obj (H.obj M)).obj (I.obj N)),
      (∀ M M' (a : M ⟶ M') N,
        U.map ((T.map a).app (G.obj N)) ≫ (e M' N).hom =
          (e M N).hom ≫ V.map ((T'.map (H.map a)).app (I.obj N))) ∧
      (∀ M N N' (b : N ⟶ N'),
        U.map ((T.obj M).map (G.map b)) ≫ (e M N').hom =
          (e M N).hom ≫ V.map ((T'.obj (H.obj M)).map (I.map b)))
```

Proof commands before the change:

```lean
open CategoryTheory MonoidalCategory
```

## New

The public theorem has exactly the same signature as in Old; its proof now constructs
the balanced map, proves naturality and applies the separately stated invertibility
criterion. All new helpers in the existing module are private. Added proof commands:

```lean
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory TopologicalSpace
open scoped ChangeOfRings
```

Inside the SheafOfModules namespace, a noncomputable section contains variables for
Z, R and B and local notation for forgetting the commutative structure of ring sheaves.
These variables and notations are section-local. The namespace is closed before the
original public theorem. The private balancedMap has an irreducibility attribute to
prevent costly unfolding of its unique-map construction in subsequent proofs.

## Users

The downstream scan lists 422 transitive importers and two textual users of the
existing theorem, including its own declaration. Every transitive user sees the same
public theorem statement and the same definitions. None needs an adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RelativeTensorPullbackBalancedNaturality | N4 | Same statement and objects; no adaptation required. |
| Sheaf.AlgebraicGeometry.RelativeTensorPullbackComplexComparison | unclaimed | Same statement and objects; no adaptation required. |

## Status

landed 20261013T152018-L-953911 2026-10-13 (merge of deliver/N4/Sheaf.AlgebraicGeometry.RelativeTensorPullbackBalancedNaturality)
