# CategoryTheory.exists_perfect_constant_derived_map_local

## Reason

The proof adds module-level variables for private restriction helpers, and a
declaration-scoped instance attribute. The static preflight classifies these commands
as an interface change. The attribute suppresses the imported high-priority
`GrothendieckTopology.hasSheafify_of_essentiallySmall` only while elaborating this
one theorem, since its successor-universe restriction obstructs the arbitrary
`max u v` coefficient universe. The ordinary concrete sheafification instance applies.
Existing declarations keep exactly their signatures and visibility. All new helpers
in the item module are private. There is no mathematical definition change, no
exported instance change, and no target statement needs a new mathematical review.

## Old

```lean
theorem exists_perfect_constant_derived_map_local
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    (X : C) (_hX : IsTerminal X)
    (R : Type (max u v)) [CommRing R]
    [HasDerivedCategory.{wR, max u v, (max u v) + 1} (ModuleCat.{max u v} R)]
    [siteModuleHasDerivedCategory.{u, v, wS}
      ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))]
    [∀ U : C, siteModuleHasDerivedCategory.{max u v, v, wU}
      (((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)).over U)]
    (P L : DerivedCategory.{wR, max u v, (max u v) + 1} (ModuleCat.{max u v} R))
    (_hP : DerivedCategory.IsPerfectRingComplex.{max u v, wR} P)
    (φ : (siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R).obj P ⟶
      (siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R).obj L) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i : I, U i ⟶ X),
      Presieve.ofArrows U f ∈ J X ∧
      ∀ i : I, ∃ α : P ⟶ L,
        (ringedDerivedRestrictionSized.{u, v, wS, wU}
          ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))
          (U i)).map φ =
        (ringedDerivedRestrictionSized.{u, v, wS, wU}
          ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))
          (U i)).map
          ((siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R).map α)
```

There was no declaration-scoped instance attribute or module-level helper variable command.

## New

```lean
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
theorem exists_perfect_constant_derived_map_local
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    (X : C) (_hX : IsTerminal X)
    (R : Type (max u v)) [CommRing R]
    [HasDerivedCategory.{wR, max u v, (max u v) + 1} (ModuleCat.{max u v} R)]
    [siteModuleHasDerivedCategory.{u, v, wS}
      ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))]
    [∀ U : C, siteModuleHasDerivedCategory.{max u v, v, wU}
      (((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)).over U)]
    (P L : DerivedCategory.{wR, max u v, (max u v) + 1} (ModuleCat.{max u v} R))
    (_hP : DerivedCategory.IsPerfectRingComplex.{max u v, wR} P)
    (φ : (siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R).obj P ⟶
      (siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R).obj L) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i : I, U i ⟶ X),
      Presieve.ofArrows U f ∈ J X ∧
      ∀ i : I, ∃ α : P ⟶ L,
        (ringedDerivedRestrictionSized.{u, v, wS, wU}
          ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))
          (U i)).map φ =
        (ringedDerivedRestrictionSized.{u, v, wS, wU}
          ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))
          (U i)).map
          ((siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R).map α)
```

The private helpers share the local parameters:

```lean
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (S : Sheaf J RingCat.{max u v}) {U V : C} (f : V ⟶ U)
```

The theorem's hypotheses and conclusion, including all universes, are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.PerfectConstantDerivedMapLocal | F6 | Private helper context and a declaration-scoped elaboration attribute; theorem signature unchanged. |

A textual search finds no other module mentioning the theorem. No consumer is adapted.
The change adds no public instance or notation and changes no existing definition.

## Status

landed 20261019T093359-L-2303218 2026-10-19 (merge of deliver/F6/Sheaf.CategoryTheory.PerfectConstantDerivedMapLocal)
