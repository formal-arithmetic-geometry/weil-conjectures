# CategoryTheory.CechPushforward.columnFunctor

## Reason

The nested map/flip/evaluation presentation repeatedly expands bicomplex data when
checking column naturality and localized comparison laws. Evaluate the Cech degree
before mapping the resolution complex. Both presentations have definitionally equal
objects, differentials, and maps; the refinement components are unchanged.

## Old

```lean
def columnFunctor (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    (V : Sheaf J (Type u)) (n : SimplexCategory) :
    CochainComplex (ringedSiteModules.{u} R) ℕ ⥤
      CochainComplex (ringedSiteModules.{u} S) ℕ :=
  (D.cochains V ⋙ G.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ) ⋙
      HomologicalComplex.eval _ (.up ℕ) n.len

/-- The actual covering-refinement arrow on a column, before localization.
Source: Stacks 04J4 (blueprint: lem-sfb-cech-pushforward-augmented-model). -/
def columnRefinement (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    {V W : Sheaf J (Type u)} (r : W ⟶ V) (n : SimplexCategory)
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ) :
    (columnFunctor D G V n).obj I ⟶ (columnFunctor D G W n).obj I :=
  ((HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ)) ⋙
    HomologicalComplex.eval _ (.up ℕ) n.len).map
      ((NatTrans.mapHomologicalComplex
        (Functor.whiskerRight (D.refinement r) (G.mapHomologicalComplex (.up ℕ)))
          (.up ℕ)).app I)
```

## New

```lean
def columnFunctor (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    (V : Sheaf J (Type u)) (n : SimplexCategory) :
    CochainComplex (ringedSiteModules.{u} R) ℕ ⥤
      CochainComplex (ringedSiteModules.{u} S) ℕ :=
  (D.cochains V ⋙ HomologicalComplex.eval _ (.up ℕ) n.len ⋙ G).mapHomologicalComplex
    (.up ℕ)

/-- The actual covering-refinement arrow on a column, before localization.
Source: Stacks 04J4 (blueprint: lem-sfb-cech-pushforward-augmented-model). -/
def columnRefinement (D : CoherentCechImageModel R)
    (G : ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} S) [G.Additive]
    {V W : Sheaf J (Type u)} (r : W ⟶ V) (n : SimplexCategory)
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ) :
    (columnFunctor D G V n).obj I ⟶ (columnFunctor D G W n).obj I :=
  (NatTrans.mapHomologicalComplex
    (Functor.whiskerRight (D.refinement r)
      (HomologicalComplex.eval _ (.up ℕ) n.len ⋙ G)) (.up ℕ)).app I
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CechPushforwardAugmentedModel | V4 | Same column maps; the complete proof is checked against the simpler presentation. |

There are no current Lean importers of this module. The unfinished DAG parents
`lem-sfb-cech-localization-unit-totalization`,
`lem-sfb-supported-hull-proetale-descent`, and
`lem-sfb-norm-local-model-finite-field-derived-generation` still require its
unchanged statement. No module or DAG attachment is withdrawn. Target statements
and their mathematical meanings are unchanged.

The public column signatures also carry the sheafification and local-bijection
instances used by their module-category structures. On the small sites in this
file these are supplied by the direct Mathlib instances; they impose no new
mathematical hypothesis. The assigned existence theorem retains its original
signature. The proof's private instance caches and private `import all` imports
leave the existing column-model and normalized-naturality modules unchanged.

This record is part of the delivery at
`coord/changes/cech-pushforward-column-representation.md`. For a reviewer correction
passed through `--apply-fixes`, the landing tool expects the correction filename
`cech-pushforward-column-representation.change.md` (the delivery filename itself
remains unchanged). The previous approved delivery, `724afe8f731`, was returned
because its reviewer correction used the delivery basename without `.change`.
This is a delivery-metadata repair; it does not change the proved Lean statement.

## Added instance binders (recorded by the reviewer, 2026-10-25)

The module now erases `CategoryTheory.siteAbelianHasSheafify` and
`CategoryTheory.siteAbelianWEqualsLocallyBijective` and works under section variables
`[HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
[HasSheafify L AddCommGrpCat.{u}] [L.WEqualsLocallyBijective AddCommGrpCat.{u}]`.
Four existing public definitions therefore gain instance-implicit binders (as printed by
`#check @…` on the delivered module, compared with the published module):

| declaration | binders added |
| --- | --- |
| `CategoryTheory.CechPushforward.totalTransition` | `[HasSheafify L AddCommGrpCat]`, `[L.WEqualsLocallyBijective AddCommGrpCat]` |
| `CategoryTheory.CechPushforward.AugmentedModel` | `[HasSheafify J AddCommGrpCat]`, `[J.WEqualsLocallyBijective AddCommGrpCat]`, `[HasSheafify L AddCommGrpCat]`, `[L.WEqualsLocallyBijective AddCommGrpCat]` |
| `CategoryTheory.CechPushforward.ModelNaturality` | the same four |
| `CategoryTheory.CechPushforward.ComparisonLaws` | the same four |

All four classes are `Prop`-valued and are synthesized by Mathlib's direct instances on
every small site (`C X : Type u`, `[SmallCategory C]`), which is the only setting of this
module; the predicates are therefore the same propositions as before (any two instance
proofs are equal by proof irrelevance). The statement of
`cech_pushforward_augmented_model` is unchanged and has no added binders. Elaborating the
public predicates with the global instances instead (so that they keep their old binder
lists) makes the proofs exceed the 60 s compile limit, so the binders are recorded here.

Users: no Lean module imports `Sheaf.CategoryTheory.CechPushforwardAugmentedModel`; the
unfinished DAG parents listed above see the same propositions, and any caller obtains the
four instances by instance search.

## Status

landed 20261025T164550-L-1034685 2026-10-25 (merge of deliver/V4/Sheaf.CategoryTheory.CechPushforwardAugmentedModel)
