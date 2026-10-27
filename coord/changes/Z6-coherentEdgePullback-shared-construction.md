# AlgebraicGeometry.coherentEdgePullback

## Reason

The coefficient h-map now has a shared explicit constructor,
`topDegreeCohomologyPullback`, in `Sheaf.AlgebraicGeometry.TopDegreeLeraySquare`.
It is precisely the existing `moduleCohomologyFMap` of the ordinary adjunct of
the specified tensor coefficient morphism. The old map remains an abbreviation
of this same construction. The square statement uses this constructor too, so
its application at the chosen fiber products keeps the cohomology-map data folded.
No map, coefficient identification, hypothesis or conclusion changes. The
constructor takes its data explicitly; it chooses no new arbitrary witness.

## Old

```lean
def coherentEdgePullback {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) (h : T' ⟶ T) :=
  Scheme.Modules.moduleCohomologyFMap (coherentEdgeXMap f g h)
    ((Scheme.Modules.tensorPullbackSectionAdjunction (coherentEdgeXMap f g h)).homEquiv _ _
      (coherentEdgeCoefficientIso f G g h).hom) 1
```

## New

```lean
abbrev coherentEdgePullback {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) (h : T' ⟶ T) :=
  topDegreeCohomologyPullback (pullback.snd f g) (pullback.snd f (h ≫ g))
    (coherentEdgeXMap f g h)
    (coherentEdgeCoefficient f G g) (coherentEdgeCoefficient f G (h ≫ g))
    (coherentEdgeCoefficientIso f G g h).hom

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false

attribute [local irreducible] Functor.rightDerived

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
local instance coherentEdge_cohomologyModule (T : Scheme.{u}) (n : ℕ)
    (M : SheafOfModules.{u} (moduleRings T.toRingedSpace)) :
    Module Γ(T, ⊤) ((RingedSpace.moduleCohomology T.toRingedSpace n).obj M) :=
  inferInstanceAs (Module ((moduleRings T.toRingedSpace).obj.obj (op ⊤))
    ((RingedSpace.moduleCohomology T.toRingedSpace n).obj M))

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
local instance coherentEdge_sectionsModule (T : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings T.toRingedSpace)) :
    Module Γ(T, ⊤) ((RingedSpace.globalSectionsFunctor T.toRingedSpace).obj M) :=
  inferInstanceAs (Module ((moduleRings T.toRingedSpace).obj.obj (op ⊤))
    ((RingedSpace.globalSectionsFunctor T.toRingedSpace).obj M))

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coherentEdge_classicalEdge_smul
    {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules)
    (r : Γ(S, ⊤)) (x : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj G) :
    let V : ModuleCat.{u} Γ(S, ⊤) :=
      (RingedSpace.globalSectionsFunctor S.toRingedSpace).obj
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived 1).obj G)
    let ε := Classical.choose (exists_lerayEdge_isIso_of_vanishing f)
    (ε 1).app G
        ((show (moduleRings X.toRingedSpace).obj.obj (op ⊤) from f.appTop r) • x) =
      r • (show V from (ε 1).app G x) := by
  classical
  have : IsGrothendieckAbelian.{u} X.Modules := Scheme.Modules.isGrothendieckAbelian X
  let ε := Classical.choose (exists_lerayEdge_isIso_of_vanishing f)
  let a := Scheme.Modules.smulHom G (f.appTop r)
  have hs := Scheme.Modules.moduleCohomology_map_smulHom G (injectiveResolution G) 1
    (f.appTop r) x
  have hn := CategoryTheory.congr_fun ((ε 1).naturality a) x
  have hd := Scheme.Modules.higherDirectImage_map_smulHom f 1 G r
  calc
    (ε 1).app G ((show (moduleRings X.toRingedSpace).obj.obj (op ⊤) from f.appTop r) • x) =
        (ε 1).app G (((RingedSpace.moduleCohomology X.toRingedSpace 1).map a) x) :=
      congrArg (fun y ↦ (ε 1).app G y) hs.symm
    _ = (RingedSpace.globalSectionsFunctor S.toRingedSpace).map
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived 1).map a)
          ((ε 1).app G x) := hn
    _ = (RingedSpace.globalSectionsFunctor S.toRingedSpace).map
        (((Scheme.Modules.higherDirectImage f 1).obj G).smulHom r)
          ((ε 1).app G x) := by
      exact congrArg (fun k ↦ (RingedSpace.globalSectionsFunctor S.toRingedSpace).map k
        ((ε 1).app G x)) hd
    _ = r • (show (RingedSpace.globalSectionsFunctor S.toRingedSpace).obj
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived 1).obj G)
          from (ε 1).app G x) :=
      Scheme.Modules.smulHom_app_top_apply _ r _

attribute [local instance_reducible] TopCat.Sheaf
set_option allowUnsafeReducibility true in
attribute [local reducible] Scheme.Modules Scheme.Modules.Hom Scheme.Modules.instCategory
  Scheme.Modules.instAbelian

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
```

The shared edge and cohomology-map interfaces use the underlying additive groups
of `topDegreeCohomologyOnBase` at their two bases. These are definitionally the
old additive cohomology groups. The source and target scalar restrictions are
explicit real constructions; no map or module action changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge | Z6 | Same coefficient h-map, with the shared constructor used by the Leray square. |

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge
--uses coherentEdgePullback` reports zero downstream importers and this module as
the only user (two occurrences in the current source). No consumer adaptation is
needed outside this item. The shared constructor is included in the square node's
Lean declarations. Its explicit body is the old defining formula with general
schemes and coefficients. The public square import already supports the shared
image, edge and section constructors. No source-library file or target declaration
is changed. The independent reader should compare the constructor body with the
old definition and check any target using this unchanged mathematical map.

## Status

landed 20261022T114331-L-608771 2026-10-22 (merge of deliver/Z6/Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge)
