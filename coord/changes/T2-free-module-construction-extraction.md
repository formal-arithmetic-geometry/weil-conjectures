# CategoryTheory.SheafFreeModule free-sheaf constructions

## Reason

The parent theorem node was re-split into three stated dependencies. Each dependency
imported the parent theorem module to obtain its seven data constructions. Importing
those dependencies back into the parent would create an import cycle. Extract the
seven constructions unchanged into FreeModuleSheafConstruction; retain their names
and make the original module publicly re-export them. The three support modules now
publicly import the construction module. No theorem signature or object construction
changes. The canonical free object, generators and coefficient-change maps are identical.
No target meaning changes or target statement review is required.

The final claim read on 2026-10-23 shows W4 holds FreeModuleUniversalProperty,
X2 holds GeometricFreeModuleHomEquivalence, and X3 holds NormalizedFreeModuleComparison.
The original reverse imports would close the cycle through the proved parent module;
the import replacements are forced by the construction relocation.
The comparison-calculus module also caches the existing sheaf-composition instances
locally for its three sites. A low-heartbeat diagnostic identified repeated searches
for HasSheafCompose as expensive. Local caching avoids repeating those searches in
every declaration; no global instance or reducibility attribute changes.

## Old

Location: lean/Sheaf/CategoryTheory/Sites/InverseImageFreeModule.lean.
The moved declarations, verbatim:

```lean
/-- Forget commutativity of the coefficient sheaf, using Mathlib's sheaf composition.
Source: Stacks 04BL (blueprint: lem-trf-geometric-inverse-image-free-module). -/
abbrev ring (B : Sheaf J CommRingCat.{w}) : Sheaf J RingCat.{w} :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B

/-- Underlying set sheaves of modules, with the lift used by algebraic inverse image.
Source: Stacks 03D2 (blueprint: lem-trf-geometric-inverse-image-free-module). -/
noncomputable abbrev moduleSets (B : Sheaf J CommRingCat.{w}) :
    ringedSiteModules.{w, w, vC, uC} (ring B) ⥤ Sheaf J (Type w) :=
  SheafOfModules.toSheaf (ring B) ⋙
    sheafCompose J (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})

/-- Module sheafification of `U ↦ B(U)[E(U)]`. Mathlib's presheaf free functor sends
restrictions to the semilinear extension of `[s] ↦ [s|V]`, and its map on generator
sheaves is the sectionwise linear extension. Source: Stacks 04BL and 03CY
(blueprint: lem-trf-geometric-inverse-image-free-module). -/
noncomputable def free (B : Sheaf J CommRingCat.{w}) :
    Sheaf J (Type w) ⥤ ringedSiteModules.{w, w, vC, uC} (ring B) :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  sheafToPresheaf J (Type w) ⋙ PresheafOfModules.free (ring B).obj ⋙
    PresheafOfModules.sheafification (𝟙 (ring B).obj)

/-- The presheaf generator map followed by the abelian sheafification unit, before
lifting the underlying sets. Source: Stacks 04BL
(blueprint: lem-trf-geometric-inverse-image-free-module). -/
noncomputable def generatorRaw (B : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)) :
    E ⟶ (SheafOfModules.toSheaf (ring B) ⋙
      sheafCompose J (forget AddCommGrpCat.{w})).obj ((free B).obj E) :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  { hom := PresheafOfModules.freeAdjunctionUnit (ring B).obj E.obj ≫
      Functor.whiskerRight
        (toSheafify J (PresheafOfModules.freeObj (R := (ring B).obj) E.obj).presheaf)
        (forget AddCommGrpCat.{w}) }

/-- The map `s ↦ [s]` into the underlying sheaf of the free module, with the harmless
`ULift` identification required by the recorded algebraic inverse-image interface.
Source: Stacks 04BL (blueprint: lem-trf-geometric-inverse-image-free-module). -/
noncomputable def generator (B : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)) :
    E ⟶ (moduleSets B).obj ((free B).obj E) where
  hom := (generatorRaw B E).hom ≫ Functor.whiskerLeft
    (((free B).obj E).val.presheaf ⋙ forget AddCommGrpCat.{w}) uliftFunctorTrivial.inv

/-- Simultaneous coefficient and generator change: the sheafified linear extension of
`[s] ↦ [e(s)]`, semilinear along `b`. It is constructed by the two recorded adjunctions,
with target scalars restricted along `b`. Source: Stacks 04BL and 03CY
(blueprint: lem-trf-geometric-inverse-image-free-module). -/
noncomputable def change {B B' : Sheaf J CommRingCat.{w}} (b : B ⟶ B')
    {E E' : Sheaf J (Type w)} (e : E ⟶ E') :
    (free B).obj E ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map b)).obj
        ((free B').obj E') :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ring B).obj)).homEquiv _ _).symm
    (PresheafOfModules.freeObjDesc (e.hom ≫ (generatorRaw B' E').hom))

/-- The simultaneous change map on underlying lifted set sheaves.
Source: Stacks 04BL (blueprint: lem-trf-geometric-inverse-image-free-module). -/
noncomputable def changeSets {B B' : Sheaf J CommRingCat.{w}} (b : B ⟶ B')
    {E E' : Sheaf J (Type w)} (e : E ⟶ E') :
    (moduleSets B).obj ((free B).obj E) ⟶ (moduleSets B').obj ((free B').obj E') :=
  (moduleSets B).map (change b e)

```

The three support modules publicly imported
`Sheaf.CategoryTheory.Sites.InverseImageFreeModule`.

## New

Location: lean/Sheaf/CategoryTheory/Sites/FreeModuleSheafConstruction.lean.
The declarations have the same signatures and bodies; only their blueprint tags now
name the new definition node `def-trf-free-module-sheaf-construction`:

```lean
/-- Forget commutativity of the coefficient sheaf, using Mathlib's sheaf composition.
Source: Stacks 04BL (blueprint: def-trf-free-module-sheaf-construction). -/
abbrev ring (B : Sheaf J CommRingCat.{w}) : Sheaf J RingCat.{w} :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B

/-- Underlying set sheaves of modules, with the lift used by algebraic inverse image.
Source: Stacks 03D2 (blueprint: def-trf-free-module-sheaf-construction). -/
noncomputable abbrev moduleSets (B : Sheaf J CommRingCat.{w}) :
    ringedSiteModules.{w, w, vC, uC} (ring B) ⥤ Sheaf J (Type w) :=
  SheafOfModules.toSheaf (ring B) ⋙
    sheafCompose J (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})

/-- Module sheafification of `U ↦ B(U)[E(U)]`. Mathlib's presheaf free functor sends
restrictions to the semilinear extension of `[s] ↦ [s|V]`, and its map on generator
sheaves is the sectionwise linear extension. Source: Stacks 04BL and 03CY
(blueprint: def-trf-free-module-sheaf-construction). -/
noncomputable def free (B : Sheaf J CommRingCat.{w}) :
    Sheaf J (Type w) ⥤ ringedSiteModules.{w, w, vC, uC} (ring B) :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  sheafToPresheaf J (Type w) ⋙ PresheafOfModules.free (ring B).obj ⋙
    PresheafOfModules.sheafification (𝟙 (ring B).obj)

/-- The presheaf generator map followed by the abelian sheafification unit, before
lifting the underlying sets. Source: Stacks 04BL
(blueprint: def-trf-free-module-sheaf-construction). -/
noncomputable def generatorRaw (B : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)) :
    E ⟶ (SheafOfModules.toSheaf (ring B) ⋙
      sheafCompose J (forget AddCommGrpCat.{w})).obj ((free B).obj E) :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  { hom := PresheafOfModules.freeAdjunctionUnit (ring B).obj E.obj ≫
      Functor.whiskerRight
        (toSheafify J (PresheafOfModules.freeObj (R := (ring B).obj) E.obj).presheaf)
        (forget AddCommGrpCat.{w}) }

/-- The map `s ↦ [s]` into the underlying sheaf of the free module, with the harmless
`ULift` identification required by the recorded algebraic inverse-image interface.
Source: Stacks 04BL (blueprint: def-trf-free-module-sheaf-construction). -/
noncomputable def generator (B : Sheaf J CommRingCat.{w}) (E : Sheaf J (Type w)) :
    E ⟶ (moduleSets B).obj ((free B).obj E) where
  hom := (generatorRaw B E).hom ≫ Functor.whiskerLeft
    (((free B).obj E).val.presheaf ⋙ forget AddCommGrpCat.{w}) uliftFunctorTrivial.inv

/-- Simultaneous coefficient and generator change: the sheafified linear extension of
`[s] ↦ [e(s)]`, semilinear along `b`. It is constructed by the two recorded adjunctions,
with target scalars restricted along `b`. Source: Stacks 04BL and 03CY
(blueprint: def-trf-free-module-sheaf-construction). -/
noncomputable def change {B B' : Sheaf J CommRingCat.{w}} (b : B ⟶ B')
    {E E' : Sheaf J (Type w)} (e : E ⟶ E') :
    (free B).obj E ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map b)).obj
        ((free B').obj E') :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ring B).obj)).homEquiv _ _).symm
    (PresheafOfModules.freeObjDesc (e.hom ≫ (generatorRaw B' E').hom))

/-- The simultaneous change map on underlying lifted set sheaves.
Source: Stacks 04BL (blueprint: def-trf-free-module-sheaf-construction). -/
noncomputable def changeSets {B B' : Sheaf J CommRingCat.{w}} (b : B ⟶ B')
    {E E' : Sheaf J (Type w)} (e : E ⟶ E') :
    (moduleSets B).obj ((free B).obj E) ⟶ (moduleSets B').obj ((free B').obj E') :=
  (moduleSets B).map (change b e)

```

The original module publicly imports the construction module and privately imports
the three proof-dependency modules. Each of those publicly imports the construction
module in place of the original theorem module. The original module keeps comparison,
IsComparison, and all five theorem signatures unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Sites.InverseImageFreeModule | T2 | Re-export moved definitions; prove five theorems from the stated dependencies |
| Sheaf.CategoryTheory.Sites.FreeModuleSheafConstruction | new | Own the unchanged seven constructions |
| Sheaf.CategoryTheory.Sites.FreeModuleUniversalProperty | W4 | Replace parent import by construction import; all signatures and proofs unchanged |
| Sheaf.CategoryTheory.Sites.GeometricFreeModuleHomEquivalence | X2 | Replace parent import by construction import; all signatures and proofs unchanged |
| Sheaf.CategoryTheory.Sites.NormalizedFreeModuleComparison | X3 | Replace parent import by construction import; cache existing sheaf-composition instances locally during elaboration |
| Sheaf.CategoryTheory.Sites.InverseImageDifferentials | unclaimed | No source adaptation; original module continues to expose all seven names |

| Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion | unclaimed | No adaptation; same public names and local witnesses have no consumer effect |
| Sheaf.Algebra.Homology.RingedSitePointFinitePresentationRetract | unclaimed | No adaptation; same public free-sheaf constructions |
| Sheaf.Algebra.Homology.RingedSitePointUniversalTensor | unclaimed | No adaptation; same public change maps |
| Sheaf.Topology.SheafCotangentComparison | unclaimed | No adaptation; same public generators |

The table contains every downstream module returned by tools/downstream.py, including
the unchanged differential consumer. No source-library module is edited.

## Status

landed 20261023T131812-L-2153781 2026-10-23 (merge of deliver/T2/Sheaf.CategoryTheory.Sites.InverseImageFreeModule)
