# AlgebraicGeometry.Scheme.exists_affine_perfect_stalk_hom_lift

## Reason

The explicit retirement row in coord/retire-items.tsv assigns this zero-hole DIFFERENT
module. The source library now proves the same local lifting assertion in a stronger
form. The duplicate would redeclare the same public name if both were imported.
Retire only the Sheaf duplicate; preserve the mathematical node and its dependencies.

## Old

In Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift:

```lean
theorem exists_affine_perfect_stalk_hom_lift
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (x : X) [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (G H : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (U : X.Opens) (hxU : x ∈ U) (hU : IsAffineOpen U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) (hQ : IsStrictlyPerfect X U Q)
    (iG : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj G) ≅ DerivedCategory.Q.obj P)
    (iH : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj H) ≅ DerivedCategory.Q.obj Q)
    (t : DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G) ⟶
      DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj H)) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (hVU : V ≤ U),
      let T := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V) ⥤
          ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X V ⟨x, hxV⟩
      letI : S.PreservesZeroMorphisms :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X V ⟨x, hxV⟩
      ∃ (cG : DerivedCategory.Q.obj
          ((S.mapHomologicalComplex (.up ℤ)).obj
            (T.obj P)) ≅ DerivedCategory.Q.obj
              (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
                (.up ℤ)).obj G))
        (cH : DerivedCategory.Q.obj
          ((S.mapHomologicalComplex (.up ℤ)).obj
            (T.obj Q)) ≅ DerivedCategory.Q.obj
              (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
                (.up ℤ)).obj H))
        (f : T.obj P ⟶ T.obj Q),
        DerivedCategory.Q.map
          ((S.mapHomologicalComplex (.up ℤ)).map f) =
            cG.hom ≫ t ≫ cH.inv
```

## New

Existing declaration in WeilConjectures.AlgebraicGeometry.PerfectStalkDerivedHomLift,
unchanged by this delivery:

```lean
theorem exists_affine_perfect_stalk_hom_lift
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (x : X) [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (G H : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (U : X.Opens) (hxU : x ∈ U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) (hQ : IsStrictlyPerfect X U Q)
    (iG : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj G) ≅ DerivedCategory.Q.obj P)
    (iH : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj H) ≅ DerivedCategory.Q.obj Q)
    (t : DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G) ⟶
      DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj H)) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (hVU : V ≤ U),
      let T := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V) ⥤
          ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X V ⟨x, hxV⟩
      letI : S.PreservesZeroMorphisms :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X V ⟨x, hxV⟩
      let c : T ⋙ S.mapHomologicalComplex (.up ℤ) ≅
          (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ) :=
        Functor.mapHomologicalComplexCompIso
          (openModuleStalkRestrictionComparison X U V hVU x hxU hxV) (.up ℤ)
      let cG := DerivedCategory.Q.mapIso (c.app P) ≪≫
        perfectLocalModelStalkComparison X x U hxU G P iG
      let cH := DerivedCategory.Q.mapIso (c.app Q) ≪≫
        perfectLocalModelStalkComparison X x U hxU H Q iH
      ∃ f : T.obj P ⟶ T.obj Q,
        DerivedCategory.Q.map
          ((S.mapHomologicalComplex (.up ℤ)).map f) =
            cG.hom ≫ t ≫ cH.inv
```

The source theorem omits hU and chooses cG and cH canonically. It is stronger: use
its V, hxV, hV, hVU and f, and choose its two canonical comparison isomorphisms as
the original existential witnesses. A scratch theorem with the entire original
signature proves precisely this implication and compiles. Its axiom list, the
source theorem's axiom list and perfectLocalModelStalkComparison's axiom list all
contain only propext, Classical.choice and Quot.sound. Universes u, v and w remain
independent. Empty U is excluded by hxU; zero complexes and free rank zero are
allowed. No added hypothesis or weaker conclusion is used.

The node's Lean attachment is moved to the exact source signature with existing:true.
Its prose assertion, stmt_deps, proof_deps, unit and all parent dependencies stay.
The proof description now identifies the source's canonical comparison construction.
The duplicate is listed in deleted.txt and will land as a withdrawn module.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift | Q2 | Retire the duplicate and its two private helpers. |
| WeilConjectures.AlgebraicGeometry.PerfectStalkDerivedIsoSpread | unclaimed | Already imports and applies the source theorem; no adaptation. |

tools/downstream.py --uses reports zero downstream modules and only the duplicate's
own declaration reference.

The retirement inventory's old consumer Sheaf.AlgebraicGeometry.PerfectStalkDerivedIsoSpread
is absent in the current library. Its node already points to the source module.
The source parent imports WeilConjectures.AlgebraicGeometry.PerfectStalkDerivedHomLift
at line 11 and applies the source theorem at line 143, unpacking the canonical form.
Thus no parent proof or import migration is pending. Searches of both library roots
and quarantine find no import of the withdrawn Sheaf module. The sole DAG parent is
lem-sc-perfect-stalk-derived-iso-spread; its proof still cites this same node, now
reattached to the source theorem, and none of its edges is removed. The unit
sk-prop-av-cube has no realized statement or step here and is unchanged.
No source declaration, signature, attribute, public import, definition or proof changes.

## Status

landed 20261021T004838-L-1794227 2026-10-21 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift)
