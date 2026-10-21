# CategoryTheory.DerivedTowerPullback.exists_unique_normalized_evaluation

## Reason

The delivery adds proved private helpers for the existing normalization theorem.
The static interface check flags the new elaboration option and declaration-scoped
`omit ... in` / `include ... in` commands and a local Mathlib-instance priority, so this
record documents their scope.
These commands control elaboration, section-variable inclusion for private helpers,
and the priority of an existing proof-valued Mathlib instance.
No existing declaration signature, definition body, visibility, attribute, or public
import changes. The public theorem receives its complete proof.

The source-only interface comparison using `tools/leanindex.py` confirms that every
public declaration entry and the public-import entry agree exactly; only the generic
command-list entry differs. Both original `set_option autoImplicit false` and original
`include adj hL hLt` remain in place.

## Old

The original public signature, verbatim:

```lean
theorem exists_unique_normalized_evaluation :
    ∃ v : ∀ n : ℕ, Comparison (A := (Modules R))
        (B := (Modules S)) L Lt n,
      (∀ n : ℕ, IsNormalizedOn F L Lt ε τ (IsGoodTower R) n (v n)) ∧
      (∀ (n : ℕ) (v' : Comparison (A := (Modules R))
        (B := (Modules S)) L Lt n),
        IsNormalizedOn F L Lt ε τ (IsGoodTower R) n v' → v' = v n) ∧
      ∀ (a b : ℕ) (h : a ≤ b)
        (M : DerivedCategory (ℕᵒᵖ ⥤ (Modules R))),
        (v b).hom.app M ≫ L.map ((derivedTransition (A := (Modules R)) a b h).app M) =
          (derivedTransition (A := (Modules S)) a b h).app (Lt.obj M) ≫
            (v a).hom.app M
```

There were no private-helper scoping commands or `backward.isDefEq.respectTransparency`
option in this module.

## New

The public signature remains verbatim:

```lean
theorem exists_unique_normalized_evaluation :
    ∃ v : ∀ n : ℕ, Comparison (A := (Modules R))
        (B := (Modules S)) L Lt n,
      (∀ n : ℕ, IsNormalizedOn F L Lt ε τ (IsGoodTower R) n (v n)) ∧
      (∀ (n : ℕ) (v' : Comparison (A := (Modules R))
        (B := (Modules S)) L Lt n),
        IsNormalizedOn F L Lt ε τ (IsGoodTower R) n v' → v' = v n) ∧
      ∀ (a b : ℕ) (h : a ≤ b)
        (M : DerivedCategory (ℕᵒᵖ ⥤ (Modules R))),
        (v b).hom.app M ≫ L.map ((derivedTransition (A := (Modules R)) a b h).app M) =
          (derivedTransition (A := (Modules S)) a b h).app (Lt.obj M) ≫
            (v a).hom.app M
```

The new module-local elaboration setting is:

```lean
set_option backward.isDefEq.respectTransparency false
```

Declaration-scoped commands omit unused derived-category instances from the private
`complexTransition`, `levelCounit_transition`, `complex_transition`,
`towerCounit_transition`, `single_preserves`, and `tower_preserves` helpers.
The last two private helpers also have `include adj in`, retaining the specified
pullback adjunction. Every such command has `in` and applies only to its following
private declaration. The original public section variables remain unchanged.

The existing Mathlib proof-valued instance is prioritized locally:

```lean
attribute [local instance 100000] hasSheafCompose_of_preservesLimitsOfSize
```

This selects the direct limit-preservation proof of sheaf composition before the more
expensive multicospan route. Both prove the same proposition; no category data changes.
The attribute is local to this module and exports no instance. It refers to an existing
public Mathlib declaration, so no private helper enters any public signature or definition.

The final comparison calculation is a proved private categorical lemma,
`normalized_evaluation_of_resolutions`, instantiated by the main theorem. This avoids
repeating expensive concrete sheaf-module instance elaboration throughout that calculation.

The complete module compiled without warnings in 16.7 seconds. The main theorem's
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Users

`tools/downstream.py Sheaf.Paper.DerivedTowerEvaluationNormalization --uses
CategoryTheory.DerivedTowerPullback.exists_unique_normalized_evaluation` reports zero
importing downstream modules and only the item itself as a textual declaration use.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.DerivedTowerEvaluationNormalization | U6 | Complete proof; public interface unchanged. |

The DAG parents `lem-cbc-adic-pullback-presentation-transport` and
`lem-cbc-derived-finite-quotient-coherence` retain the same dependency and can use the
unchanged public signature. No consumer adaptation, target statement change, or target
definition change is necessary.

## Status

landed 20261021T120753-L-3944826 2026-10-21 (merge of deliver/U6/Sheaf.Paper.DerivedTowerEvaluationNormalization)
