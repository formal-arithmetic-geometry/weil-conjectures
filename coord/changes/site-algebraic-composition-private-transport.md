# CategoryTheory.siteAlgebraicCompositionUnit

## Reason

The proof needs private generalized-section transport helpers. Four named
`noncomputable section` blocks delimit their variables and end before the existing
theorem. These scoped variable commands trigger preflight's command-change gate;
this record makes the additions available for independent review. No existing
public statement, definition, attribute or public import changes. The only import
change removes the redundant private `Mathlib.CategoryTheory.Adjunction.Mates`;
`Mathlib.CategoryTheory.Adjunction.Unique` already imports it publicly.

## Old

The theorem signature, verbatim (body was `sorry`):

```lean
theorem siteAlgebraicCompositionUnit
    {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (v : C ⥤ D) (u : D ⥤ E)
    [v.IsContinuous J K] [u.IsContinuous K L]
    [PreservesFiniteLimits (sheafPullback v
      (Type (max uC vC uD vD uE vE w)) J K)]
    [PreservesFiniteLimits (sheafPullback u
      (Type (max uC vC uD vD uE vE w)) K L)]
    [PreservesFiniteLimits
      (siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u)] :
    (∀ H : Sheaf J (Type (max uC vC uD vD uE vE w)),
      (siteAlgebraicCompositeAdjunction.{uC, vC, uD, vD, uE, vE, w} J K L v u).unit.app H ≫
          (v.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) J K).map
            ((u.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) K L).map
              ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app H)) =
        (sheafAdjunctionContinuous v (Type (max uC vC uD vD uE vE w)) J K).unit.app H ≫
          (v.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) J K).map
            ((sheafAdjunctionContinuous u (Type (max uC vC uD vD uE vE w)) K L).unit.app
              ((sheafPullback v (Type (max uC vC uD vD uE vE w)) J K).obj H))) ∧
    (∀ (H : Sheaf J (Type (max uC vC uD vD uE vE w))) (W : C) (x : H.obj.obj (op W)),
      ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app H).hom.app
          (op (u.obj (v.obj W)))
          (((siteAlgebraicCompositeAdjunction.{uC, vC, uD, vD, uE, vE, w} J K L v u).unit.app
              H).hom.app (op W) x) =
        ((sheafAdjunctionContinuous u (Type (max uC vC uD vD uE vE w)) K L).unit.app
            ((sheafPullback v (Type (max uC vC uD vD uE vE w)) J K).obj H)).hom.app
          (op (v.obj W))
          (((sheafAdjunctionContinuous v (Type (max uC vC uD vD uE vE w)) J K).unit.app
            H).hom.app (op W) x)) ∧
    (∀ δ : siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u ≅
        sheafPullback v (Type (max uC vC uD vD uE vE w)) J K ⋙
          sheafPullback u (Type (max uC vC uD vD uE vE w)) K L,
      (∀ (H : Sheaf J (Type (max uC vC uD vD uE vE w))) (W : C)
          (x : H.obj.obj (op W)),
        (δ.hom.app H).hom.app (op (u.obj (v.obj W)))
            (((siteAlgebraicCompositeAdjunction.{uC, vC, uD, vD, uE, vE, w} J K L v u).unit.app
              H).hom.app (op W) x) =
          ((sheafAdjunctionContinuous u (Type (max uC vC uD vD uE vE w)) K L).unit.app
              ((sheafPullback v (Type (max uC vC uD vD uE vE w)) J K).obj H)).hom.app
            (op (v.obj W))
            (((sheafAdjunctionContinuous v (Type (max uC vC uD vD uE vE w)) J K).unit.app
              H).hom.app (op W) x)) →
        δ = siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u) ∧
    (∀ A B : Sheaf J (Type (max uC vC uD vD uE vE w)),
      (siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app (A ⨯ B) ≫
          prodComparison (sheafPullback v (Type (max uC vC uD vD uE vE w)) J K ⋙
            sheafPullback u (Type (max uC vC uD vD uE vE w)) K L) A B =
        prodComparison (siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u) A B ≫
          prod.map ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app A)
            ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app B)) ∧
    ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app (⊤_ _) ≫
        terminalComparison (sheafPullback v (Type (max uC vC uD vD uE vE w)) J K ⋙
          sheafPullback u (Type (max uC vC uD vD uE vE w)) K L) =
      terminalComparison (siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u)) ∧
    SiteAlgebraicComparison
      (siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom ∧
    (∀ H : Sheaf J (Type (max uC vC uD vD uE vE w)),
      IsIso ((sheafAdjunctionContinuous (𝟭 C)
        (Type (max uC vC uD vD uE vE w)) J J).unit.app H)) ∧
    SiteAlgebraicIdentityUnit
      (sheafAdjunctionContinuous (𝟭 C) (Type (max uC vC uD vD uE vE w)) J J).unit :=
```

## New

The signature is identical, verbatim (body is now proved):

```lean
theorem siteAlgebraicCompositionUnit
    {C : Type uC} {D : Type uD} {E : Type uE}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (v : C ⥤ D) (u : D ⥤ E)
    [v.IsContinuous J K] [u.IsContinuous K L]
    [PreservesFiniteLimits (sheafPullback v
      (Type (max uC vC uD vD uE vE w)) J K)]
    [PreservesFiniteLimits (sheafPullback u
      (Type (max uC vC uD vD uE vE w)) K L)]
    [PreservesFiniteLimits
      (siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u)] :
    (∀ H : Sheaf J (Type (max uC vC uD vD uE vE w)),
      (siteAlgebraicCompositeAdjunction.{uC, vC, uD, vD, uE, vE, w} J K L v u).unit.app H ≫
          (v.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) J K).map
            ((u.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) K L).map
              ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app H)) =
        (sheafAdjunctionContinuous v (Type (max uC vC uD vD uE vE w)) J K).unit.app H ≫
          (v.sheafPushforwardContinuous (Type (max uC vC uD vD uE vE w)) J K).map
            ((sheafAdjunctionContinuous u (Type (max uC vC uD vD uE vE w)) K L).unit.app
              ((sheafPullback v (Type (max uC vC uD vD uE vE w)) J K).obj H))) ∧
    (∀ (H : Sheaf J (Type (max uC vC uD vD uE vE w))) (W : C) (x : H.obj.obj (op W)),
      ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app H).hom.app
          (op (u.obj (v.obj W)))
          (((siteAlgebraicCompositeAdjunction.{uC, vC, uD, vD, uE, vE, w} J K L v u).unit.app
              H).hom.app (op W) x) =
        ((sheafAdjunctionContinuous u (Type (max uC vC uD vD uE vE w)) K L).unit.app
            ((sheafPullback v (Type (max uC vC uD vD uE vE w)) J K).obj H)).hom.app
          (op (v.obj W))
          (((sheafAdjunctionContinuous v (Type (max uC vC uD vD uE vE w)) J K).unit.app
            H).hom.app (op W) x)) ∧
    (∀ δ : siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u ≅
        sheafPullback v (Type (max uC vC uD vD uE vE w)) J K ⋙
          sheafPullback u (Type (max uC vC uD vD uE vE w)) K L,
      (∀ (H : Sheaf J (Type (max uC vC uD vD uE vE w))) (W : C)
          (x : H.obj.obj (op W)),
        (δ.hom.app H).hom.app (op (u.obj (v.obj W)))
            (((siteAlgebraicCompositeAdjunction.{uC, vC, uD, vD, uE, vE, w} J K L v u).unit.app
              H).hom.app (op W) x) =
          ((sheafAdjunctionContinuous u (Type (max uC vC uD vD uE vE w)) K L).unit.app
              ((sheafPullback v (Type (max uC vC uD vD uE vE w)) J K).obj H)).hom.app
            (op (v.obj W))
            (((sheafAdjunctionContinuous v (Type (max uC vC uD vD uE vE w)) J K).unit.app
              H).hom.app (op W) x)) →
        δ = siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u) ∧
    (∀ A B : Sheaf J (Type (max uC vC uD vD uE vE w)),
      (siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app (A ⨯ B) ≫
          prodComparison (sheafPullback v (Type (max uC vC uD vD uE vE w)) J K ⋙
            sheafPullback u (Type (max uC vC uD vD uE vE w)) K L) A B =
        prodComparison (siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u) A B ≫
          prod.map ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app A)
            ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app B)) ∧
    ((siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom.app (⊤_ _) ≫
        terminalComparison (sheafPullback v (Type (max uC vC uD vD uE vE w)) J K ⋙
          sheafPullback u (Type (max uC vC uD vD uE vE w)) K L) =
      terminalComparison (siteAlgebraicCompositePullback.{uC, vC, uD, vD, uE, vE, w} J K L v u)) ∧
    SiteAlgebraicComparison
      (siteAlgebraicCompositionIso.{uC, vC, uD, vD, uE, vE, w} J K L v u).hom ∧
    (∀ H : Sheaf J (Type (max uC vC uD vD uE vE w)),
      IsIso ((sheafAdjunctionContinuous (𝟭 C)
        (Type (max uC vC uD vD uE vE w)) J J).unit.app H)) ∧
    SiteAlgebraicIdentityUnit
      (sheafAdjunctionContinuous (𝟭 C) (Type (max uC vC uD vD uE vE w)) J J).unit :=
```

The added sections are `Transport`, `AlgebraicTransport`, `Lift` and
`FinishTransport`. Each ends before the existing theorem. All 26 added helper
declarations are private and fully proved or concretely constructed. The
section variables do not escape their blocks. There are no new attributes,
instances, notations, options or public declarations. Existing definitions are
unchanged. The proof follows the existing DAG dependency route.

## Users

`tools/downstream.py Sheaf.CategoryTheory.SiteAlgebraicCompositionUnit --uses
siteAlgebraicCompositionUnit` found zero downstream modules and only the item's
own declaration occurrence. A source search also found no external users of
this module's comparison definitions. Unfinished DAG parents remain attached;
no node or module is withdrawn.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.SiteAlgebraicCompositionUnit | C3 | One proof hole closed; existing interface unchanged |

## Status

landed 20261021T111012-L-3882271 2026-10-21 (merge of deliver/C3/Sheaf.CategoryTheory.SiteAlgebraicCompositionUnit)
