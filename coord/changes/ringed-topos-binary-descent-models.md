# CategoryTheory binary descent helper definitions

## Reason

The proof and its independent geometric lemmas need the same six definitions. They
previously lived in the theorem module, so importing them from a dependency would
create an import cycle. Move their declarations, names, instances, universes and
bodies unchanged to `Sheaf.CategoryTheory.RingedToposBinaryDescentDefs`. The old module
publicly reexports it, including all nine original public imports. Only the blueprint
tags of the moved docstrings change. No mathematical definition or target statement
changes. The original theorem signature is unchanged (checked after whitespace normalization).

## Old

In `lean/Sheaf/CategoryTheory/RingedToposBinaryDescent.lean`:

```lean
/-- Expose Mathlib's small-model abelian sheafification at the chosen site universe.
Source: Stacks 03CV (blueprint: lem-sp-ringed-topos-binary-descent). -/
noncomputable instance binaryDescent_hasSheafify {C : Type u} [Category.{v} C]
    [EssentiallySmall.{s} C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{s} :=
  hasSheafifyEssentiallySmallSite J AddCommGrpCat.{s}

/-- Expose Mathlib's transport of the local criterion for abelian sheafification.
Source: Stacks 03CV (blueprint: lem-sp-ringed-topos-binary-descent). -/
noncomputable instance binaryDescent_wEqualsLocallyBijective
    {C : Type u} [Category.{v} C] [EssentiallySmall.{s} C]
    (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{s} :=
  letI : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{s} C).inverse.op) AddCommGrpCat.{s} :=
    fun _ ↦ HasLimitsOfShape.of_small.{s, s} AddCommGrpCat.{s} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J (A := AddCommGrpCat.{s})

/-- Termwise restriction to the localized site, using the recorded restriction functor.
Source: Stacks 03DH and 03DJ (blueprint: lem-sp-ringed-topos-binary-descent). -/
noncomputable def moduleOverComplex {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) (U : C) :=
  letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R U
  (SheafOfModules.overFunctor.{max u v r} R U).mapHomologicalComplex (.up ℤ)

/-- Termwise relocalization along a map of objects of the site.
Source: Stacks 03DH (blueprint: lem-sp-ringed-topos-binary-descent). -/
noncomputable def moduleOverMapComplex {C : Type u} [Category.{v} C] [HasPullbacks C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V) :=
  (SheafOfModules.overMap.{max u v r} R f).mapHomologicalComplex (.up ℤ)

/-- The sectionwise identity comparing restriction with iterated restriction on complexes.
Source: Stacks 03DH (blueprint: lem-sp-ringed-topos-binary-descent). -/
noncomputable def moduleOverComplexComp {C : Type u} [Category.{v} C] [HasPullbacks C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V) :
    moduleOverComplex R U ≅ moduleOverComplex R V ⋙ moduleOverMapComplex R f :=
  letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R U
  letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R V
  NatIso.mapHomologicalComplex (SheafOfModules.overFunctorMap R f).symm (.up ℤ)

/-- The direct-image restriction map is the adjoint of restriction of the counit.
Source: Stacks 08DG, cone construction (blueprint: lem-sp-ringed-topos-binary-descent). -/
noncomputable def restrictionAdjunctionMap
    {D DU DW : Type*} [Category D] [Category DU] [Category DW]
    {rU : D ⥤ DU} {rW : D ⥤ DW} {rUW : DU ⥤ DW}
    {RU : DU ⥤ D} {RW : DW ⥤ D}
    (adjU : rU ⊣ RU) (adjW : rW ⊣ RW) (comp : rW ≅ rU ⋙ rUW) (A : DU) :
    RU.obj A ⟶ RW.obj (rUW.obj A) :=
  (adjW.homEquiv _ _) (comp.hom.app (RU.obj A) ≫ rUW.map (adjU.counit.app A))
```

## New

In `lean/Sheaf/CategoryTheory/RingedToposBinaryDescentDefs.lean`, publicly reexported by
the original module:

```lean
/-- Expose Mathlib's small-model abelian sheafification at the chosen site universe.
Source: Stacks 03CV (blueprint: def-sp-ringed-topos-binary-descent-models). -/
noncomputable instance binaryDescent_hasSheafify {C : Type u} [Category.{v} C]
    [EssentiallySmall.{s} C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{s} :=
  hasSheafifyEssentiallySmallSite J AddCommGrpCat.{s}

/-- Expose Mathlib's transport of the local criterion for abelian sheafification.
Source: Stacks 03CV (blueprint: def-sp-ringed-topos-binary-descent-models). -/
noncomputable instance binaryDescent_wEqualsLocallyBijective
    {C : Type u} [Category.{v} C] [EssentiallySmall.{s} C]
    (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{s} :=
  letI : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{s} C).inverse.op) AddCommGrpCat.{s} :=
    fun _ ↦ HasLimitsOfShape.of_small.{s, s} AddCommGrpCat.{s} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J (A := AddCommGrpCat.{s})

/-- Termwise restriction to the localized site, using the recorded restriction functor.
Source: Stacks 03DH and 03DJ (blueprint: def-sp-ringed-topos-binary-descent-models). -/
noncomputable def moduleOverComplex {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) (U : C) :=
  letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R U
  (SheafOfModules.overFunctor.{max u v r} R U).mapHomologicalComplex (.up ℤ)

/-- Termwise relocalization along a map of objects of the site.
Source: Stacks 03DH (blueprint: def-sp-ringed-topos-binary-descent-models). -/
noncomputable def moduleOverMapComplex {C : Type u} [Category.{v} C] [HasPullbacks C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V) :=
  (SheafOfModules.overMap.{max u v r} R f).mapHomologicalComplex (.up ℤ)

/-- The sectionwise identity comparing restriction with iterated restriction on complexes.
Source: Stacks 03DH (blueprint: def-sp-ringed-topos-binary-descent-models). -/
noncomputable def moduleOverComplexComp {C : Type u} [Category.{v} C] [HasPullbacks C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V) :
    moduleOverComplex R U ≅ moduleOverComplex R V ⋙ moduleOverMapComplex R f :=
  letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R U
  letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R V
  NatIso.mapHomologicalComplex (SheafOfModules.overFunctorMap R f).symm (.up ℤ)

/-- The direct-image restriction map is the adjoint of restriction of the counit.
Source: Stacks 08DG, cone construction (blueprint: def-sp-ringed-topos-binary-descent-models). -/
noncomputable def restrictionAdjunctionMap
    {D DU DW : Type*} [Category D] [Category DU] [Category DW]
    {rU : D ⥤ DU} {rW : D ⥤ DW} {rUW : DU ⥤ DW}
    {RU : DU ⥤ D} {RW : DW ⥤ D}
    (adjU : rU ⊣ RU) (adjW : rW ⊣ RW) (comp : rW ≅ rU ⋙ rUW) (A : DU) :
    RU.obj A ⟶ RW.obj (rUW.obj A) :=
  (adjW.homEquiv _ _) (comp.hom.app (RU.obj A) ≫ rUW.map (adjU.counit.app A))
```

## Users

Ran `tools/downstream.py Sheaf.CategoryTheory.RingedToposBinaryDescent --uses
CategoryTheory.<name>` separately for all six names. Each lists only the item itself;
there are zero downstream importers of the old module in the current repository.
New consumers are included below. No existing consumer other than the item is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RingedToposBinaryDescent | E9 | Same exported interface; imports the extracted definitions. |
| Sheaf.CategoryTheory.RingedToposBinaryDescentDefs | E9, new | Holds the six unchanged definitions and their original public imports. |
| Sheaf.CategoryTheory.RingedToposDirectImageRestriction | E9, new | Uses the same restriction models. |
| Sheaf.CategoryTheory.RingedToposFibreRestriction | E9, new | Uses the same canonical overlap maps. |
| Sheaf.CategoryTheory.RingedToposCrossDirectImageRestriction | E9, new | States cross-restriction for these models. |
| Sheaf.CategoryTheory.RingedToposBinaryDescentTriangle | E9, new | States the independent natural lower-shriek triangle. |

All six definition bodies are identical after removing docstrings and whitespace.
There is no target-meaning change, so this relocation does not reopen target review.
No module under `lean/WeilConjectures/` is changed, withdrawn, or given a new signature.

## Status

landed 20261021T120351-L-3846158 2026-10-21 (merge of deliver/E9/Sheaf.CategoryTheory.RingedToposBinaryDescent)
