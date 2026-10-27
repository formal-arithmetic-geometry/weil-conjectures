# Roos cone compositor proof helpers

## Reason

Complete the one proof hole in `Sheaf.CategoryTheory.RoosConeCompositorDescent` and
repair the duplicate private proofs reported for returned head `4624e3fe2`.
The static interface detector also flags the command-level sections, options and
attributes used by private proof helpers. No existing public signature, definition
body, attribute or public import changes.

## Old

The public theorem is:

```lean
theorem roosConeCompositorDescent
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (_hcomm : ∀ (V : Cᵒᵖ) (x y : R.obj.obj V), x * y = y * x)
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wA} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    {S : Type uS} [Category.{vS} S] [Abelian S] [HasDerivedCategory.{wS} S]
    (U : S ⥤ ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (F : Fin 3 → ringedSiteModules.{max uC vC r} R ⥤ ringedSiteModules.{max uC vC r} R)
    [∀ i, (F i).Additive] [∀ i, PreservesFiniteLimits (F i)]
    [∀ i, PreservesFiniteColimits (F i)]
    [∀ i, PreservesLimitsOfShape (Discrete ℕ) (F i)]
    (G : Fin 3 → S ⥤ S) [∀ i, (G i).Additive]
    [∀ i, PreservesFiniteLimits (G i)] [∀ i, PreservesFiniteColimits (G i)]
    (b : ∀ i : Fin 3, U ⋙ RoosCompositor.tower (F i) ≅ G i ⋙ U)
    (d : F 0 ⋙ F 1 ≅ F 2) (t : G 0 ⋙ G 1 ≅ G 2)
    (_hb : ∀ M : S,
      (Functor.whiskerLeft (U.obj M) d.hom) ≫ (b 2).hom.app M =
        (RoosCompositor.tower (F 1)).map ((b 0).hom.app M) ≫
          (b 1).hom.app ((G 0).obj M) ≫ U.map (t.hom.app M))
    (RL : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{max uC vC r} R))
    (eta : roosLimitFunctor ⋙ DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ RL)
    (_hRL : RL.IsRightDerivedFunctor eta
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) (.up ℤ))) :
    ∃ N : RoosCompositor.Comparisons U F G RL,
      RoosCompositor.HasSignedCoordinates (A := ringedSiteModules.{max uC vC r} R) ∧
      RoosCompositor.HasNormalization U F G RL N eta ∧
      RoosCompositor.HasProducts U F G RL N b ∧
      RoosCompositor.HasDiagonal U F G RL N ∧
      RoosCompositor.HasDerivedModel U F G RL N ∧
      RoosCompositor.HasCompositors U F G RL N d t := by
  sorry
```

All public comparison definitions are already present.
The retained returned packet additionally reproved private `limit_unit_iso` and
`roos_tower_grothendieck`, duplicating existing library statements.

## New

The theorem has the identical signature and a complete proof. All existing public
comparison definitions and public imports remain verbatim. Private helpers verify
the signed coordinate formulas, product and cone compositors and localization descent.
The private `productIso` and `transportIso` are irreducible and have proved equations.
A `reassoc` attribute on the private product projection lemma generates its private
reassociated equation. Local elaborator transparency options prevent repeated
unfolding of the cone and localization constructions. Synchronous elaboration and
explicit composition of equalities keep the cone compositor calculation within
the single-file compile limit. After their equations are proved, `coordinates` and
`coordIso`, `roosF` and `roosConeFunctor` are locally irreducible except around
the concrete chain-comparison application; the exported definitions and attributes stay unchanged.

The returned duplicate `limit_unit_iso` and `roos_tower_grothendieck` and their unused
`ordinaryLimitIso` and `normalized_inclusion` helpers are removed. Private
`import all Sheaf.CategoryTheory.StrictRoosDerivation` makes its already proved
`CategoryTheory.roos_inclusion_quasiIso` available. This stronger theorem proves the
needed result on every K-injective tower directly, so neither duplicate argument is
needed. No dependency file is edited and no helper is newly exported.

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.RoosConeCompositorDescent --uses
roosConeCompositorDescent complex tower coordinates total Comparisons toRoos
HasProducts HasDiagonal HasSignedCoordinates HasNormalization HasDerivedModel
HasCompositors` reports zero downstream modules on 2026-10-24. Unfinished DAG parents
retain the same statement and Lean attachment. No module is withdrawn and no consumer
adaptation is required.

| Module | Holder | Effect |
|---|---|---|
| Sheaf.CategoryTheory.RoosConeCompositorDescent | F4 | One proof completed; duplicate private proofs removed |

## Validation

The full repaired module compiled through `lcompile.py` in 54.6 seconds with no
warnings or errors; `tools/import_prune_check.py` passes. Static comparison confirms
all original public definitions, public imports and the theorem signature remain
verbatim. The Lean file contains zero `sorry` occurrences and all lines fit within
100 characters. The node records the actual eight-step proof and dependencies.
No source-library module or target statement changes.

## Status
landed 20261024T014820-L-2273599 2026-10-24 (merge of deliver/F4/Sheaf.CategoryTheory.RoosConeCompositorDescent)
