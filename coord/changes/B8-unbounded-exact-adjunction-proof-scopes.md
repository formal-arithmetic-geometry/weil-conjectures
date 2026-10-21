# CategoryTheory.UnboundedExactTower.unboundedExactAdjunctionSquare

## Reason

Preflight (d) classifies the new section-variable commands used by proved private helpers
as a visibility change. These commands introduce local proof contexts only. Every original
public declaration signature, universe, instance body and definition body is preserved.
All added declarations are private. Public imports are preserved; proof imports are private.
The fully compiled delivery passes the declaration/axiom probe.

## Old

The existing theorem signature, verbatim:

```lean
theorem unboundedExactAdjunctionSquare
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J RingCat.{u}) (S : Sheaf K RingCat.{u})
    [HasDerivedCategory.{wA} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{wB} (ringedSiteModules.{u} S)]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R)]
    [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ ringedSiteModules.{u} S)]
    (f : ExactMorphism R S) :
    TowerProperties (ringedSiteModules.{u} R) ∧
      TowerProperties (ringedSiteModules.{u} S) ∧ ComparisonsCompatible f.adjunction
```

The original file had no `ComparisonProofs` or `EvaluationCube` helper sections.

## New

The same theorem signature, verbatim:

```lean
theorem unboundedExactAdjunctionSquare
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J RingCat.{u}) (S : Sheaf K RingCat.{u})
    [HasDerivedCategory.{wA} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{wB} (ringedSiteModules.{u} S)]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R)]
    [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ ringedSiteModules.{u} S)]
    (f : ExactMorphism R S) :
    TowerProperties (ringedSiteModules.{u} R) ∧
      TowerProperties (ringedSiteModules.{u} S) ∧ ComparisonsCompatible f.adjunction
```

Its proof is complete. The other original theorem signature is also unchanged.
The added evaluation helper context is, verbatim:

```lean
section EvaluationCube

universe uA' vA' uB' vB'

variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wB'} B']
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory.{wTA'} (ℕᵒᵖ ⥤ A')] [HasDerivedCategory.{wTB'} (ℕᵒᵖ ⥤ B')]
  (F : B ⥤ A) (F' : B' ⥤ A') (g : B ⥤ B') (h : A ⥤ A')
  [F.Additive] [F'.Additive] [g.Additive] [h.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]
  [PreservesFiniteLimits h] [PreservesFiniteColimits h]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

The additional `ComparisonProofs` section similarly repeats the existing two-category
comparison context to prove private normalization and invertibility lemmas. Local `omit`
commands remove unused tower instances from helper signatures; scoped transparency options
control elaboration of existing localization functors. These commands end with their
sections/declarations and do not alter the existing public interface. No target meaning,
definition, mathematical assertion, or consumer statement changes.

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare`
reports exactly one downstream module. The live claim search has no row for it.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.TowerLimitTransposeNormalization | unclaimed | Existing imported declarations, including `cochainUnit`, keep identical signatures and bodies; no adaptation required. |

## Status

landed 20261021T110938-L-3832600 2026-10-21 (merge of deliver/B8/Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare)
