# Sheaf.Paper.DerivedLocalClassEdgeComparison proof sections

## Reason

The proof adds private proved helpers in local sections. The static interface comparison
records section, variable, option, open and local-attribute commands, even though no
existing public declaration, definition body, public import or attribute is changed.
The local exact-composition instances are confined to their helper section. The added
`open CategoryTheory.Functor` and elaboration options are likewise inside that section.
No helper is used in any public definition body.

## Old

The previous nondeclaration commands, verbatim as token-normalized by leanindex:

```lean
@[expose] public section
set_option autoImplicit false
universe u vC vD uC uD wC wD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C) (Λ : Type (u + 1)) [CommRing Λ]
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C) (Λ : Type (u + 1)) [CommRing Λ] [HasTerminal C]
```

## New

The new nondeclaration commands, verbatim as token-normalized by leanindex:

```lean
@[expose] public section
set_option autoImplicit false
universe u vC vD uC uD wC wD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] [L.PreservesHomology] [R.PreservesHomology]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D] {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D] [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] in
omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] in
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D E : Type*} [Category.{vC} C] [Category.{vC} D] [Category.{vC} E] [Abelian C] [Abelian D] [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasKInjectiveResolutions C] [HasKInjectiveResolutions D] {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes] {L₁ : D ⥤ C} {L₂ : E ⥤ D} {L : E ⥤ C} [L₁.Additive] [L₂.Additive] [L.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂] [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj₁ : L₁ ⊣ F) (adj₂ : L₂ ⊣ G) (adj : L ⊣ H)
omit [Abelian C] [Abelian D] [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasKInjectiveResolutions C] [HasKInjectiveResolutions D] [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes] [L₁.Additive] [L₂.Additive] [L.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂] [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D] [HasKInjectiveResolutions D] {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C) (Λ : Type (u + 1)) [CommRing Λ]
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C) (Λ : Type (u + 1)) [CommRing Λ] [HasTerminal C]
omit [HasTerminal C] in
```

All existing public declaration signatures and non-theorem bodies remain verbatim.
The one public theorem replaces its sorry with a proof using the private helpers.

## Users

`python3 tools/downstream.py Sheaf.Paper.DerivedLocalClassEdgeComparison` reports
zero current Lean importers. This does not withdraw the item: its DAG parents and
unit route remain attached. No consumer adaptation is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DerivedLocalClassEdgeComparison | R9 | Private proof sections only; public statements and definitions unchanged. |

## Status

landed 20261021T140910-L-2771092 2026-10-21 (merge of deliver/R9/Sheaf.Paper.DerivedLocalClassEdgeComparison)
