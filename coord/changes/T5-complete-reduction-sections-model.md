# AlgebraicGeometry.ProEtale.CompleteReductionSections.sections, rgamma, sectionTower, limitToRoos

## Reason

The independent normalized-resolution and Roos-triangle statement modules need the
original ordinary section constructions. Keeping those constructions in the item
would create an import cycle. Move them to a shared module, preserving names,
signatures and bodies verbatim; only their blueprint annotations change. The item
publicly imports the shared module and retains its original five public imports.
No target statement, mathematical definition or chosen data changes. This relocation
preserves the meaning of all targets; it does not reopen their mathematical review.

## Old

In `Sheaf.Paper.CompleteReductionRgammaUpperBound`:

```lean
abbrev sections : AdicCompletion.Modules l E U ⥤ Ab.{u + 1} :=
  Mod.forget (AdicCompletion.ring l E U) ⋙
    sheafToPresheaf (Scheme.ProEt.topology U) Ab.{u + 1} ⋙
      (evaluation U.ProEtᵒᵖ Ab.{u + 1}).obj (op (Scheme.ProEt.mk (𝟙 U)))

/-- The total right derived functor of ordinary module sections, computed in the
internal-module category on K-injective resolutions.
Source: Stacks 0D6K (blueprint: lem-sfb-complete-reduction-rgamma-upper-bound). -/
abbrev rgamma : DerivedCategory (AdicCompletion.Modules l E U) ⥤
    DerivedCategory Ab.{u + 1} := (sections l E U).rightDerivedFunctor

/-- Termwise ordinary sections on a complex of strict integral-module towers.
Source: Stacks 0A07 (blueprint: lem-sfb-complete-reduction-rgamma-upper-bound). -/
abbrev sectionTower (I : CochainComplex (ℕᵒᵖ ⥤ AdicCompletion.Modules l E U) ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ Ab.{u + 1}) ℤ :=
  (((Functor.whiskeringRight ℕᵒᵖ (AdicCompletion.Modules l E U) Ab.{u + 1}).obj
    (sections l E U)).mapHomologicalComplex (.up ℤ)).obj I

/-- The chain comparison from sections of the ordinary tower limit to the strict Roos
fibre. It is the product of the actual limit projections, with zero nullhomotopy.
Source: Stacks 0D6K and 0941
(blueprint: lem-sfb-complete-reduction-rgamma-upper-bound). -/
def limitToRoos (I : CochainComplex (ℕᵒᵖ ⥤ AdicCompletion.Modules l E U) ℤ) :
    ((sections l E U).mapHomologicalComplex (.up ℤ)).obj (limit I.asFunctor) ⟶
      roosF.obj (sectionTower l E U I) :=
  roosAugment
    (fun n ↦ ((sections l E U).mapHomologicalComplex (.up ℤ)).map
      (limit.π I.asFunctor (op n)))
    (by
      intro n
      change _ ≫ ((sections l E U).mapHomologicalComplex (.up ℤ)).map
        (I.asFunctor.map (homOfLE (Nat.le_succ n)).op) = _
      rw [← Functor.map_comp, limit.w])
```

## New

In `Sheaf.Paper.CompleteReductionSectionsModel`, publicly imported by the item:

```lean
abbrev sections : AdicCompletion.Modules l E U ⥤ Ab.{u + 1} :=
  Mod.forget (AdicCompletion.ring l E U) ⋙
    sheafToPresheaf (Scheme.ProEt.topology U) Ab.{u + 1} ⋙
      (evaluation U.ProEtᵒᵖ Ab.{u + 1}).obj (op (Scheme.ProEt.mk (𝟙 U)))

/-- The total right derived functor of ordinary module sections, computed in the
internal-module category on K-injective resolutions.
Source: Stacks 0D6K (blueprint: def-sfb-complete-reduction-sections-model). -/
abbrev rgamma : DerivedCategory (AdicCompletion.Modules l E U) ⥤
    DerivedCategory Ab.{u + 1} := (sections l E U).rightDerivedFunctor

/-- Termwise ordinary sections on a complex of strict integral-module towers.
Source: Stacks 0A07 (blueprint: def-sfb-complete-reduction-sections-model). -/
abbrev sectionTower (I : CochainComplex (ℕᵒᵖ ⥤ AdicCompletion.Modules l E U) ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ Ab.{u + 1}) ℤ :=
  (((Functor.whiskeringRight ℕᵒᵖ (AdicCompletion.Modules l E U) Ab.{u + 1}).obj
    (sections l E U)).mapHomologicalComplex (.up ℤ)).obj I

/-- The chain comparison from sections of the ordinary tower limit to the strict Roos
fibre. It is the product of the actual limit projections, with zero nullhomotopy.
Source: Stacks 0D6K and 0941
(blueprint: def-sfb-complete-reduction-sections-model). -/
def limitToRoos (I : CochainComplex (ℕᵒᵖ ⥤ AdicCompletion.Modules l E U) ℤ) :
    ((sections l E U).mapHomologicalComplex (.up ℤ)).obj (limit I.asFunctor) ⟶
      roosF.obj (sectionTower l E U I) :=
  roosAugment
    (fun n ↦ ((sections l E U).mapHomologicalComplex (.up ℤ)).map
      (limit.π I.asFunctor (op n)))
    (by
      intro n
      change _ ≫ ((sections l E U).mapHomologicalComplex (.up ℤ)).map
        (I.asFunctor.map (homOfLE (Nat.le_succ n)).op) = _
      rw [← Functor.map_comp, limit.w])
```

## Users

`tools/downstream.py` was run for the original module and separately with `--uses`
for each of the four declarations. It reports zero downstream modules and only the
item using the names. No module held by another group is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompleteReductionRgammaUpperBound | T5 | Publicly imports the shared model; uses the unchanged constructions. |
| Sheaf.Paper.ReductionSectionsNormalizedResolution | T5 (new) | Uses the shared constructions in its statement. |
| Sheaf.Paper.ReductionSectionsRoosTriangle | T5 (new) | Uses the shared constructions in its statement. |
| Sheaf.Paper.ReductionSectionsMilnor | T5 (new) | Uses the shared constructions in its statement and proof. |

The original DAG node now attaches only the unchanged main theorem. A new definition
node attaches the four constructions. This changes organization below the unit level;
the unit route stays in place.

## Status

landed 20261025T144105-L-1177264 2026-10-25 (merge of deliver/T5/Sheaf.Paper.CompleteReductionRgammaUpperBound)
