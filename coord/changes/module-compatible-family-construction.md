# OpenModuleFamily, OpenModuleFamilyCoherent, openModuleFamilyEval

## Reason

The explicit presheaf construction and its two proved properties need the shared family
notions without importing the main existence theorem and creating an import cycle.
Move the three original definitions verbatim to ModuleCompatibleFamilyPresheaf and
publicly import that module from ModuleCompatibleFamilySheaf. Names, signatures, bodies,
universes and public visibility are identical. No target statement or definition meaning changes.
The additional instances supply pointwise operations on the existing family type.

## Old

In Sheaf.Topology.ModuleCompatibleFamilySheaf:

```lean
/-- Local sections on every subopen of a cover member inside `V`.
Source: Stacks, Tag 00AL, first proof, with intersection sections expanded by restriction.
(blueprint: lem-weil-pbc-module-compatible-family-sheaf) -/
abbrev OpenModuleFamily (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
    (V : Opens X) :=
  ∀ (i : I) (W : Opens X) (hi : W ≤ U i) (_ : W ≤ V),
    (Fi i).val.obj (op (Over.mk (homOfLE hi)))

/-- A local family respects restrictions and the given overlap maps.
Source: Stacks, Tags 00AL and 00AM, compatible-family equalizer.
(blueprint: lem-weil-pbc-module-compatible-family-sheaf) -/
def OpenModuleFamilyCoherent (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
    (φij : ∀ i j : I,
      (SheafOfModules.overMap (moduleRings X)
        (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Fi i) ≅
      (SheafOfModules.overMap (moduleRings X)
        (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Fi j))
    (V : Opens X) (a : OpenModuleFamily X I U Fi V) : Prop :=
  (∀ (i : I) (W Z : Opens X) (hi : W ≤ U i) (hWV : W ≤ V) (hZW : Z ≤ W),
    (Fi i).val.map (Over.homMk (homOfLE hZW)).op (a i W hi hWV) =
      a i Z (hZW.trans hi) (hZW.trans hWV)) ∧
  (∀ (i j : I) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hWV : W ≤ V),
    (φij i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) (a i W hi hWV) =
      a j W hj hWV)

/-- Evaluate a global section through a local projection after restricting it.
Source: Stacks, Tag 00AL, projection of the compatible-family equalizer.
(blueprint: lem-weil-pbc-module-compatible-family-sheaf) -/
noncomputable abbrev openModuleFamilyEval
    (X : RingedSpace.{u}) (I : Type w) (U : I → Opens X)
    (Fi : ∀ i : I, SheafOfModules.{max u v} ((moduleRings X).over (U i)))
    (H : SheafOfModules.{max u v} (moduleRings X))
    (π : ∀ i : I, H.over (U i) ⟶ Fi i) (V : Opens X)
    (s : H.val.obj (op V)) : OpenModuleFamily X I U Fi V :=
  fun i _W hi hWV => (π i).val.app (op (Over.mk (homOfLE hi)))
    (H.val.map (homOfLE hWV).op s)
```

## New

The identical three declarations, verbatim as above, now live in
Sheaf.Topology.ModuleCompatibleFamilyPresheaf. The original module reexports them with:

```lean
public import Sheaf.Topology.ModuleCompatibleFamilyPresheaf
```

The original public import Sheaf.Paper.DerivedHomMayerVietoris remains.
The main theorem has exactly its original signature and a complete proof.
No existing module requires adaptation. All new presheaf data are explicit constructions;
Small instances are proved, and gluing data come only from the proved unique sheaf axiom.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Topology.ModuleCompatibleFamilySheaf | G2 | Reexports the identical definitions and proves the original theorem. |
| Sheaf.Topology.ModuleObjectOpenDescentAux | unclaimed in local claim snapshot | Same names, definitions and signatures through the same import; no edit required. |

The downstream scan lists 394 transitive importers but finds only these two modules using
any of the relocated names. The reexport preserves their elaborated interfaces.

## Status

landed 20261012T194113-L-455707 2026-10-12 (merge of deliver/G2/Sheaf.Topology.ModuleCompatibleFamilySheaf)
