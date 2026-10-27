# AlgebraicGeometry.ProEtale.CondensedRing.DirectImageRestrictionNormalized

## Reason

The native module preadditive instance and the projection of `Mod.instAbelian` are
extensionally and definitionally the same structure, but their implicit dictionaries
have different spellings. Specializing the generic derived-mate equation to the native
spelling exhausts the kernel budget (the isolated conversion took 75.6 seconds before
its deterministic timeout). Pin the four module preadditive instances to the explicit
projections of `Mod.instAbelian` inside this predicate. The canonical representative
proof then checked in 8.9 seconds including profiling and diagnostic output.

Only `Sheaf.Paper.DerivedDirectImageOpenCoherenceData` is adapted; it is unclaimed.
The predicate is now a proposition structure with four proof fields corresponding,
in order, to the original conjunction: derived invertibility, underived invertibility,
sectionwise normalization, and the representative equation. Its constructor packages
those proofs; its four projections recover precisely the old four conditions. Thus the
new predicate is logically equivalent to the old one. The predicate name, binders,
universes, rings, canonical maps, and quantification over all unbounded K-injective
complexes stay the same. Pinning the preadditive projections in the fourth field avoids
the instance conversion, while the record avoids unfolding the entire large conjunction
when checking its proof. This changes the logical packaging as well as the instance
spelling; it is not a claim that the structure and the old conjunction are definitionally
equal.

The inserted local instances use the already constructed abelian structures, without
choosing data from an existence theorem. All other definitions and instances in this
module, and all source-library declarations, are untouched.

This predicate is used in the targets' closure, so this definition repair reopens the
meaning check for the affected targets. The four field types give exactly the same
conditions as before, with no additional hypothesis or weakened conclusion. This record
and the consumer checks support the independent reader's review of that equivalence.

## Old

```lean
def DirectImageRestrictionNormalized
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion i]
    (sq : CommSq i f' f j) : Prop :=
  IsIso (derivedDirectImageOpenRestriction Λ sq) ∧
  IsIso (directImageOpenRestriction Λ sq) ∧ OpenCoherenceSectionwise Λ sq ∧
  ∀ (I : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    [I.IsKInjective],
    (derivedDirectImageOpenRestriction Λ sq).app (DerivedCategory.Q.obj I) ≫
        (lowerStar Λ f').rightDerivedFunctor.map
          ((upperStar Λ i).mapDerivedCategoryFactors.hom.app I) =
      (upperStar Λ j).mapDerivedCategory.map
          ((lowerStar Λ f).rightDerivedFunctorObjQIso I).hom ≫
        (upperStar Λ j).mapDerivedCategoryFactors.hom.app
          (((lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (directImageOpenRestriction Λ sq) (.up ℤ)).app I) ≫
        ((lowerStar Λ f').rightDerivedFunctorObjQIso
          (((upperStar Λ i).mapHomologicalComplex (.up ℤ)).obj I)).inv

```

## New

```lean
structure DirectImageRestrictionNormalized
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion i]
    (sq : CommSq i f' f j) : Prop where
  /-- The derived comparison is invertible. -/
  derived_isIso : IsIso (derivedDirectImageOpenRestriction Λ sq)
  /-- The specified underived mate is invertible. -/
  underived_isIso : IsIso (directImageOpenRestriction Λ sq)
  /-- The open-slice coprojections and section formula have the specified normalization. -/
  sectionwise : OpenCoherenceSectionwise Λ sq
  /-- The derived mate has the specified value on every K-injective representative. -/
  representative :
    letI : Preadditive
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
      (Mod.instAbelian (condensedRingObj Λ X)).toPreadditive
    letI : Preadditive
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :=
      (Mod.instAbelian (condensedRingObj Λ Y)).toPreadditive
    letI : Preadditive
      (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1}) (condensedRingObj Λ X')) :=
      (Mod.instAbelian (condensedRingObj Λ X')).toPreadditive
    letI : Preadditive
      (Mod (Sheaf (Scheme.ProEt.topology Y') Ab.{u + 1}) (condensedRingObj Λ Y')) :=
      (Mod.instAbelian (condensedRingObj Λ Y')).toPreadditive
    ∀ (I : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
      [I.IsKInjective],
      (derivedDirectImageOpenRestriction Λ sq).app (DerivedCategory.Q.obj I) ≫
          (lowerStar Λ f').rightDerivedFunctor.map
            ((upperStar Λ i).mapDerivedCategoryFactors.hom.app I) =
        (upperStar Λ j).mapDerivedCategory.map
            ((lowerStar Λ f).rightDerivedFunctorObjQIso I).hom ≫
          (upperStar Λ j).mapDerivedCategoryFactors.hom.app
            (((lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (directImageOpenRestriction Λ sq) (.up ℤ)).app I) ≫
          ((lowerStar Λ f').rightDerivedFunctorObjQIso
            (((upperStar Λ i).mapHomologicalComplex (.up ℤ)).obj I)).inv
```

## Users

The direct-importer and declaration-consumer search was
`tools/downstream.py Sheaf.Paper.DerivedDirectImageOpenCoherenceData --direct
--uses DirectImageRestrictionNormalized`. Its five direct importers and the definition's
self-use are listed below. The transitive import closure has 277 modules; only the item
and this data module use the predicate in Lean code, with a further docstring mention
in the assembly module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DerivedDirectImageOpenCoherenceData | unclaimed | four-field Prop structure; explicit local projections in the representative field |
| Sheaf.Paper.DerivedOpenRestrictionNormalization | V4 | proof specializes with the same explicit local projections |
| Sheaf.Paper.DerivedDirectImageAssociativity | unclaimed | source unchanged; direct-importer compile passed |
| Sheaf.Paper.DerivedOpenRestrictionSuccessive | unclaimed | source unchanged; direct-importer compile passed |
| Sheaf.Paper.DerivedOpenRestrictionMixed | unclaimed | source unchanged; direct-importer compile passed |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | source unchanged; direct-importer compile passed |

All five direct importers compiled against the final structure with `lcompile.py`, as
did the data module itself. No consumer adaptations were required. The unchanged consumer
copies used for these checks were removed from the delivery sandbox.

## Status

landed 20261027T112439-L-1584557 2026-10-27 (merge of deliver/V4/Sheaf.Paper.DerivedOpenRestrictionNormalization)
