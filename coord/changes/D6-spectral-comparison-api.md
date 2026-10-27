# TopCat.Sheaf.compUnit and compMap comparison API

## Reason

Repair the landing refusal of D6 head d48e72436bf: the intersection proof duplicated
three private comparison lemmas from SpectralLimitPullbackSections. Expose the existing
comparison definitions and the unit, composition and transport equations in their original
module; remove the local copies and use this API. The uniqueness helper stays private.
The spectral module is unclaimed in the current claim snapshot. This is an additive visibility
change in Sheaf, with no mathematical statement or definition body change. Public imports,
attributes, theorem proofs and existing public signatures are preserved. Neither targets nor
public definitions of intersection sections change.

## Old

```lean
@[irreducible] private noncomputable def compUnit {A B C : TopCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (G : C.Sheaf (Type u)) :
    (pullback (Type u) g).obj G ⟶
      (pushforward (Type u) f).obj ((pullback (Type u) (f ≫ g)).obj G)

private theorem compUnit_unit {A B C : TopCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (G : C.Sheaf (Type u)) :
    (pullbackPushforwardAdjunction (Type u) g).unit.app G ≫
      (pushforward (Type u) g).map (compUnit f g G) =
    (pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app G

private theorem compUnit_comp {A B C D : TopCat.{u}}
    (h : A ⟶ B) (f : B ⟶ C) (g : C ⟶ D) (G : D.Sheaf (Type u)) :
    compUnit f g G ≫ (pushforward (Type u) f).map (compUnit h (f ≫ g) G) =
      compUnit (h ≫ f) g G

@[irreducible] private noncomputable def compMap {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (G : C.Sheaf (Type u)) :
    (pullback (Type u) g).obj G ⟶
      (pushforward (Type u) f).obj ((pullback (Type u) k).obj G)

private theorem compMap_heq {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (G : C.Sheaf (Type u)) (W : Opens B) (t : ((pullback (Type u) g).obj G).obj.obj (op W)) :
    HEq ((compMap f g k h G).hom.app (op W) t)
      ((compUnit f g G).hom.app (op W) t)
```

## New

```lean
@[irreducible] noncomputable def compUnit {A B C : TopCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (G : C.Sheaf (Type u)) :
    (pullback (Type u) g).obj G ⟶
      (pushforward (Type u) f).obj ((pullback (Type u) (f ≫ g)).obj G)

theorem compUnit_unit {A B C : TopCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (G : C.Sheaf (Type u)) :
    (pullbackPushforwardAdjunction (Type u) g).unit.app G ≫
      (pushforward (Type u) g).map (compUnit f g G) =
    (pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app G

theorem compUnit_comp {A B C D : TopCat.{u}}
    (h : A ⟶ B) (f : B ⟶ C) (g : C ⟶ D) (G : D.Sheaf (Type u)) :
    compUnit f g G ≫ (pushforward (Type u) f).map (compUnit h (f ≫ g) G) =
      compUnit (h ≫ f) g G

@[irreducible] noncomputable def compMap {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (G : C.Sheaf (Type u)) :
    (pullback (Type u) g).obj G ⟶
      (pushforward (Type u) f).obj ((pullback (Type u) k).obj G)

theorem compMap_heq {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (G : C.Sheaf (Type u)) (W : Opens B) (t : ((pullback (Type u) g).obj G).obj.obj (op W)) :
    HEq ((compMap f g k h G).hom.app (op W) t)
      ((compUnit f g G).hom.app (op W) t)
```

## Users

`tools/downstream.py Sheaf.Topology.SpectralLimitPullbackSections --uses compUnit`
finds only the defining module. The same is true of compMap; the old declarations were private.
The only direct importers are IntersectionStructureSections and SpectralFiniteCoequalizer.
No consumer requires an adaptation: the shared library has no external source uses of the
old private helpers, and no existing public signature mentions them. The 50 transitive
module importers receive an additive API only. The intersection proof uses it through its
existing private import and exports none of the added machinery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Topology.SpectralLimitPullbackSections | unclaimed | Expose five existing helpers; proofs and bodies unchanged. |
| Sheaf.AlgebraicGeometry.IntersectionStructureSections | D6 | Remove duplicate private maps and lemmas; use the shared API. |
| Sheaf.Topology.SpectralFiniteCoequalizer | unclaimed | Unchanged direct consumer; checked against exposed API. |

## Status

landed 20261023T230633-L-3454233 2026-10-23 (merge of deliver/D6/Sheaf.AlgebraicGeometry.IntersectionStructureSections)
