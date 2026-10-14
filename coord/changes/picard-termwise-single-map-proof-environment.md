# AlgebraicGeometry.Scheme.picardTermwiseSingleMap_composition

## Reason

The preflight classifies changed `attribute` commands as an interface change even
when the attributes are local. The new proof uses local transparency attributes
for the existing large categorical definitions, preventing unnecessary unfolding
during elaboration. These attributes have module-local scope. Two private real
definitions simply name the already selected counit and composition comparison;
all other new helpers are private proved theorems.

No existing declaration's signature, visibility, or definition body changes.
`picardTermwiseSingleMap` retains its original canonical-single-map composite.
No target meaning changes, and no downstream adaptation is required or delivered.
This record documents the source-command change required by preflight, rather
than a change to the mathematical interface.

## Old

The theorem's original signature, verbatim:

```lean
theorem picardTermwiseSingleMap_composition
    {W T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
    (ht : i ≫ t = t') (M : W.Modules) :
    let : (Modules.tensorPullback i).Additive :=
      (Classical.choose (Modules.exists_tensorPullbackAdjunction i)).left_adjoint_additive
    let u := (CochainComplex.singleFunctor
      (SheafOfModules.{v} (moduleRings T'.toRingedSpace)) 0).mapIso
        ((Modules.tensorPullbackCompositionIso i t t' ht).app M) ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (Modules.tensorPullback i) (.up ℤ) 0).app ((Modules.tensorPullback t).obj M)).symm
    let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
        eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)
    c.hom.app ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj M) ≫
        picardTermwiseSingleMap t' M ≫ DerivedCategory.Q.map u.hom =
      (derivedPullback i).map (picardTermwiseSingleMap t M) ≫
        (picardTermwiseCounit i).app ((CochainComplex.singleFunctor
          (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
            ((Modules.tensorPullback t).obj M))
```

The original module has no local reducibility attributes for this proof and
uses the default heartbeat budget.

## New

The theorem's signature is identical, verbatim:

```lean
theorem picardTermwiseSingleMap_composition
    {W T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
    (ht : i ≫ t = t') (M : W.Modules) :
    let : (Modules.tensorPullback i).Additive :=
      (Classical.choose (Modules.exists_tensorPullbackAdjunction i)).left_adjoint_additive
    let u := (CochainComplex.singleFunctor
      (SheafOfModules.{v} (moduleRings T'.toRingedSpace)) 0).mapIso
        ((Modules.tensorPullbackCompositionIso i t t' ht).app M) ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (Modules.tensorPullback i) (.up ℤ) 0).app ((Modules.tensorPullback t).obj M)).symm
    let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
        eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)
    c.hom.app ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj M) ≫
        picardTermwiseSingleMap t' M ≫ DerivedCategory.Q.map u.hom =
      (derivedPullback i).map (picardTermwiseSingleMap t M) ≫
        (picardTermwiseCounit i).app ((CochainComplex.singleFunctor
          (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
            ((Modules.tensorPullback t).obj M))
```

The proof environment adds the following local attributes:

```lean
attribute [local implicit_reducible] CochainComplex.singleFunctors

attribute [local irreducible] derivedPullback
  Modules.tensorPullbackCompositionIso Modules.tensorPullback Modules.tensorPullbackObj
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] Modules.Hom DerivedCategory
  Functor.mapHomologicalComplex HomotopyCategory Functor.mapHomotopyCategory
  HomotopyCategory.quotient DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh

attribute [local irreducible] picardTermwiseCounit picardTermwiseSingleMap
  Modules.canonicalSinglePullbackMap
```

The theorem additionally uses a scoped `set_option maxHeartbeats 800000 in`,
with an explanatory comment, for the large dependent types of the pinned choices.
The single-file wall-clock limit remains 60 seconds. The original section variable
and its derived-category universe are unchanged; private generic lemmas precede it
so they do not acquire an unused derived-category instance.

## Users

Textual declaration users were checked with `tools/downstream.py --uses` for
both `picardTermwiseSingleMap` and `picardTermwiseSingleMap_composition`. The latter
has only the first two users below. Holder values are those in this checkout.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardTermwiseSingleMapComposition | J4 | Sole sorry proved; public interface unchanged. |
| Sheaf.AlgebraicGeometry.PicardTermwiseSourceCoherence | unclaimed | Uses both public declarations; unchanged signatures and definition. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeMono | unclaimed | Unfolds the unchanged single-map definition; unaffected. |
| Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap | unclaimed | Uses the unchanged single-map definition; unaffected. |

All transitive importers likewise see the same public declarations, public imports,
and definitions. Local reducibility attributes and private helpers are unavailable
to them. No modules beyond the item are edited.

## Status

landed 20261014T001723-L-2551257 2026-10-14 (merge of deliver/J4/Sheaf.AlgebraicGeometry.PicardTermwiseSingleMapComposition)
