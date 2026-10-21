# AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackSquare

## Reason

Restore the quarantined zero-hole item from its preserved implementation.
The adopted source publicly imports a newer Scheme.Modules.derivedPullback.
Within this namespace that name shadows AlgebraicGeometry.derivedPullback,
which canonicalSinglePullbackMap and exists_derivedPullbackComposition use.
The unmodified archive fails with a Type u morphism where Type w is required.
Qualify the intended functor throughout the statement and private proofs.
This preserves the original mathematical statement and pre-sync elaborated type:
all binders, universes, hypotheses and the specified comparison maps remain.
No target or definition changes. The archived proof and both imports are retained.

## Old

The preserved quarantined signature, whose unqualified references were intended
to denote AlgebraicGeometry.derivedPullback:

```lean
theorem canonicalSinglePullbackSquare
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (h : g' ≫ f = f' ≫ g) (N : S.Modules) (M : X.Modules)
    (a : (pullback f).obj N ⟶ M) :
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj N
    let c := (pullbackComp g' f).app N ≪≫ (pullbackCongr h).app N ≪≫
      ((pullbackComp f' g).app N).symm
    let d := ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) f' g).hom.app E ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj E) h.symm) ≫
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) g' f).inv.app E
    d ≫ (derivedPullback g').map
        (canonicalSinglePullbackMap f N ≫ (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map a) ≫
        canonicalSinglePullbackMap g' M =
      (derivedPullback f').map (canonicalSinglePullbackMap g N) ≫
        canonicalSinglePullbackMap f' ((pullback g).obj N) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map
            (c.inv ≫ (pullback g').map a)
```

## New

```lean
theorem canonicalSinglePullbackSquare
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (h : g' ≫ f = f' ≫ g) (N : S.Modules) (M : X.Modules)
    (a : (pullback f).obj N ⟶ M) :
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj N
    let c := (pullbackComp g' f).app N ≪≫ (pullbackCongr h).app N ≪≫
      ((pullbackComp f' g).app N).symm
    let d := ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) f' g).hom.app E ≫
      eqToHom (congrArg (fun k ↦ (AlgebraicGeometry.derivedPullback k).obj E) h.symm) ≫
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) g' f).inv.app E
    d ≫ (AlgebraicGeometry.derivedPullback g').map
        (canonicalSinglePullbackMap f N ≫ (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map a) ≫
        canonicalSinglePullbackMap g' M =
      (AlgebraicGeometry.derivedPullback f').map (canonicalSinglePullbackMap g N) ≫
        canonicalSinglePullbackMap f' ((pullback g).obj N) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map
            (c.inv ≫ (pullback g').map a)
```

## Users

The live item is absent, so tools/downstream.py reports an unknown module.
A search through lean/ and quarantine/ finds the direct importers below.
Both remain quarantined and have their own rework assignments. The qualified
name restores the same shared derived-category functor their arguments require;
no consumer adaptation follows from this restoration. Their dependencies and
DAG attachments remain intact. Additional mentions in PicardCoefficientTransposePasting
and PicardDirectImageDerivedTransposePasting are explanatory docstrings.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackSquare | E4 | Restore theorem and qualify the intended functor. |
| Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare | unclaimed | Quarantined direct importer and theorem user; unchanged intended interface. |
| Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismPullback | unclaimed | Quarantined direct importer and theorem user; unchanged intended interface. |

No adopted-source file or other group's module is edited. No exported instance,
attribute or public import changes. Only the assigned item and its Lean record
are restored. Quarantined consumers are not included as unrelated repairs.

## Status

landed 20261021T012356-L-2181906 2026-10-21 (merge of deliver/E4/Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackSquare)
