# AlgebraicGeometry.sheafHom_restrictScalars_counit

## Reason

The proof needs private constructions over arbitrary sheaves of commutative rings.
They use section-scoped variables and local notation. The static interface detector
records these commands as an interface change even though the section ends before
the original public theorem. This record documents their precise scope. No public
signature, public definition, import or target meaning changes.

A private instance supplies the commutative-ring structure inherited from the
larger commutative-ring sheaf; `attribute [local instance] coinductionCommRing`
registers it only inside `section Construction`. There is no new global instance.

## Old

The original public theorem signature is:

```lean
theorem sheafHom_restrictScalars_counit
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    let A := ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj Y.ringCatSheaf
    let T := SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom
    let M := T.obj (SheafOfModules.unit A)
    let K := (SheafOfModules.homFunctor X.sheaf).obj (op M)
    ∀ (H : SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} A)
      (i : H ⋙ T ≅ K),
      (∀ (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
        (a : A.obj.obj (op U)) (φ : (H.obj F).val.obj (op U))
        (W : Over U) (b : A.obj.obj (op W.left)),
        (((i.hom.app F).val.app (op U)).hom (a • φ)).app (op W) b =
          (((i.hom.app F).val.app (op U)).hom φ).app (op W)
            (A.obj.map W.hom.op a * b)) →
      ∃ e : Adjunction.CoreHomEquiv T H,
        ∀ (G : SheafOfModules.{u} A) (F : SheafOfModules.{u} X.ringCatSheaf)
          (ψ : G ⟶ H.obj F) (U : X.Opens) (m : G.val.obj (op U)),
          (((e.homEquiv G F).symm ψ).val.app (op U)).hom m =
            ((((i.hom.app F).val.app (op U)).hom
              (((ψ.val.app (op U)).hom) m)).app
              (op (Over.mk (𝟙 U)))) (1 : A.obj.obj (op U))
```

The file had no private construction section.

## New

The public theorem has exactly the Old signature and is now proved. Before it,
`section Construction` introduces site and ring-sheaf variables and the following
local notation:

```lean
local notation "A" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj S
local notation "T" => SheafOfModules.restrictScalars α
local notation "AM" => (T).obj (SheafOfModules.unit A)
```

The same section contains private definitions and proved private lemmas and ends
before the public theorem. Its commutativity helper is a `private instance` and is
registered by `attribute [local instance] coinductionCommRing`. The scoped
`set_option quotPrecheck false` lets the local notation contain projections.
Section scoping removes the variables, local notation, option and local instance
registration afterwards. No previously exported declaration is changed.

## Users

`tools/downstream.py --uses AlgebraicGeometry.sheafHom_restrictScalars_counit`
finds the following uses. No module is adapted; all signatures and target meanings
are unchanged because the only exported change is the proof of the same theorem.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SheafCoinductionCounit | U2 | Sole hole proved; signature unchanged |
| Sheaf.AlgebraicGeometry.SheafCoinductionAdjunction | unclaimed | Existing application unchanged |

All other transitive importers have the same exported interface. No change to a
definition used by a target is made, so no target statement review is reopened.

## Status

landed 20261012T150957-L-2232416 2026-10-12 (merge of deliver/U2/Sheaf.AlgebraicGeometry.SheafCoinductionCounit)
