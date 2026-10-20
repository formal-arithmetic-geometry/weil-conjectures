# AlgebraicGeometry.ModuleExtensionByZeroStalkTransitions

## Reason

Retire the duplicate Sheaf module as requested by coord/retire-items.tsv and the human's
2026-10-20 retirement hand-off. The upstream theorem has the exact same signature after
renaming the declaration. The retirement table's API difference is only that rename.
The DAG attachment already used the upstream declaration name but pointed to the copy,
which instead declared the capitalized name; this delivery corrects the attachment.

## Old

In `Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkTransitions`:

```lean
theorem ModuleExtensionByZeroStalkTransitions (X : RingedSpace.{u}) :
    (∀ F : SheafOfModules.{u} (moduleRings X),
      IsIso ((Classical.choice (open_restriction_adjunction_exact X ⊤).the project server).counit.app F) ∧
      ∃ iota : (∀ (W W' : Opens X), W ≤ W' →
        ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
              ((SheafOfModules.overFunctor.{u} (moduleRings X) W).obj F) ⟶
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W' ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
              ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F))),
        (∀ (W W' : Opens X) (h : W ≤ W'),
          (Classical.choice (open_restriction_adjunction_exact X W).the project server).homEquiv _ _
              (iota W W' h) =
            (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).inv.app F ≫
              (SheafOfModules.overMap (moduleRings X) (homOfLE h)).map
                ((Classical.choice (open_restriction_adjunction_exact X W').the project server).unit.app
                  ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F)) ≫
              (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).hom.app
                ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W' ⋙
                  PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                    ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F))) ∧
        (∀ W : Opens X, iota W W le_rfl = 𝟙 _) ∧
        (∀ (W W' W'' : Opens X) (h : W ≤ W') (h' : W' ≤ W''),
          iota W W' h ≫ iota W' W'' h' = iota W W'' (h.trans h')) ∧
        (∀ W : Opens X,
          iota W ⊤ le_top ≫
              (Classical.choice (open_restriction_adjunction_exact X ⊤).the project server).counit.app F =
            (Classical.choice (open_restriction_adjunction_exact X W).the project server).counit.app F) ∧
        ∃ e : (∀ (W : Opens X) (x : X), x ∈ W →
            ((RingedSpace.moduleStalkFunctor X x).obj F ≅
              (RingedSpace.moduleStalkFunctor X x).obj
                ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
                  PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                    ((SheafOfModules.overFunctor.{u} (moduleRings X) W).obj F)))),
          (∀ (W : Opens X) (x : X) (hx : x ∈ W),
            (e W x hx).inv =
              (RingedSpace.moduleStalkFunctor X x).map
                ((Classical.choice (open_restriction_adjunction_exact X W).the project server).counit.app
                  F)) ∧
          (∀ (W W' : Opens X) (h : W ≤ W') (x : X) (hx : x ∈ W),
            (e W x hx).hom ≫ (RingedSpace.moduleStalkFunctor X x).map (iota W W' h) =
              (e W' x (h hx)).hom))
```

## New

The old module is withdrawn. The node points to the already proved theorem in
`WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkTransitions`:

```lean
theorem moduleExtensionByZero_stalk_transitions (X : RingedSpace.{u}) :
    (∀ F : SheafOfModules.{u} (moduleRings X),
      IsIso ((Classical.choice (open_restriction_adjunction_exact X ⊤).the project server).counit.app F) ∧
      ∃ iota : (∀ (W W' : Opens X), W ≤ W' →
        ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
              ((SheafOfModules.overFunctor.{u} (moduleRings X) W).obj F) ⟶
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W' ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
              ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F))),
        (∀ (W W' : Opens X) (h : W ≤ W'),
          (Classical.choice (open_restriction_adjunction_exact X W).the project server).homEquiv _ _
              (iota W W' h) =
            (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).inv.app F ≫
              (SheafOfModules.overMap (moduleRings X) (homOfLE h)).map
                ((Classical.choice (open_restriction_adjunction_exact X W').the project server).unit.app
                  ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F)) ≫
              (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).hom.app
                ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W' ⋙
                  PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                    ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F))) ∧
        (∀ W : Opens X, iota W W le_rfl = 𝟙 _) ∧
        (∀ (W W' W'' : Opens X) (h : W ≤ W') (h' : W' ≤ W''),
          iota W W' h ≫ iota W' W'' h' = iota W W'' (h.trans h')) ∧
        (∀ W : Opens X,
          iota W ⊤ le_top ≫
              (Classical.choice (open_restriction_adjunction_exact X ⊤).the project server).counit.app F =
            (Classical.choice (open_restriction_adjunction_exact X W).the project server).counit.app F) ∧
        ∃ e : (∀ (W : Opens X) (x : X), x ∈ W →
            ((RingedSpace.moduleStalkFunctor X x).obj F ≅
              (RingedSpace.moduleStalkFunctor X x).obj
                ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
                  PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                    ((SheafOfModules.overFunctor.{u} (moduleRings X) W).obj F)))),
          (∀ (W : Opens X) (x : X) (hx : x ∈ W),
            (e W x hx).inv =
              (RingedSpace.moduleStalkFunctor X x).map
                ((Classical.choice (open_restriction_adjunction_exact X W).the project server).counit.app
                  F)) ∧
          (∀ (W W' : Opens X) (h : W ≤ W') (x : X) (hx : x ∈ W),
            (e W x hx).hom ≫ (RingedSpace.moduleStalkFunctor X x).map (iota W W' h) =
              (e W' x (h hx)).hom))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkTransitions | C3 | Withdraw the unused duplicate. |

`tools/downstream.py --direct --uses ModuleExtensionByZeroStalkTransitions` reports zero
external direct importers and only the declaration itself as a name occurrence. An
independent whole-library source search agrees: no module imports the copy or calls
its capitalized declaration. The retirement inventory's former consumer,
`Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkMaps`, is already absent from the
current tree. Its upstream replacement imports the upstream transitions module and
calls `moduleExtensionByZero_stalk_transitions`; it compiles unchanged in this session.
No consumer adaptation is required. No upstream source or target statement is edited.
The node's statement, proof route, dependencies, unit and chapter are preserved.

Validation: the copy's exact statement was proved by applying
`moduleExtensionByZero_stalk_transitions X` in a sandbox verification file, compiling in
2.7 seconds. The unchanged upstream ModuleExtensionByZeroStalkMaps source compiled in
4.1 seconds. Both axiom checks list only propext, Classical.choice and Quot.sound.

## Status

landed 20261020T131943-L-1394547 2026-10-20 (merge of deliver/C3/Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkTransitions)
