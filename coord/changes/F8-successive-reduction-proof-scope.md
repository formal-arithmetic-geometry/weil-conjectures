# AlgebraicGeometry.ProEtale.successiveReduction_constructible_interval

## Reason

The new proof opens additional namespaces and marks exactness/finite-ring helpers as local
instances. The static interface check records these scope commands, so this record documents
that they do not change an importing module's declarations or instance search. The one new
finite-ring helper is a private theorem with a local instance attribute. All existing public
imports and the theorem signature stay verbatim. No global instance is added or disabled.

## Old

```lean
theorem successiveReduction_constructible_interval (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X))
    (n : ℕ) (a b : ℤ)
    (hfirst : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
      ((AdicCompletion.derivedReduction l E X 0).obj K))
    (hprev : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) X
      ((AdicCompletion.derivedReduction l E X n).obj K))
    (hfirstBounds : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((AdicCompletion.derivedReduction l E X 0).obj K)))
    (hprevBounds : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((AdicCompletion.derivedReduction l E X n).obj K))) :
    constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1 + 1)) X
        ((AdicCompletion.derivedReduction l E X (n + 1)).obj K) ∧
      ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((AdicCompletion.derivedReduction l E X (n + 1)).obj K))
```

The original proof body is `by sorry`.

## New

```lean
theorem successiveReduction_constructible_interval (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X))
    (n : ℕ) (a b : ℤ)
    (hfirst : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
      ((AdicCompletion.derivedReduction l E X 0).obj K))
    (hprev : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) X
      ((AdicCompletion.derivedReduction l E X n).obj K))
    (hfirstBounds : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((AdicCompletion.derivedReduction l E X 0).obj K)))
    (hprevBounds : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((AdicCompletion.derivedReduction l E X n).obj K))) :
    constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1 + 1)) X
        ((AdicCompletion.derivedReduction l E X (n + 1)).obj K) ∧
      ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((AdicCompletion.derivedReduction l E X (n + 1)).obj K))
```

The proof body is complete. Added scope commands are `open Opposite WeilConjectures`,
`open CategoryTheory.Pretriangulated`, local instance attributes for exact restriction and
`finite_quotient`, and a proof elaboration transparency option. No definition or statement
changes, and no target meaning changes.

## Users

`python3 tools/downstream.py Sheaf.Paper.SuccessiveReductionConstructibility
--allow-missing --uses successiveReduction_constructible_interval` reports zero
current downstream modules and zero uses. A text search of both `lean/` and
`quarantine/` also finds no current importer or use. No consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralCriterionReductions | unclaimed | Earlier intended parent; current reverted version has no import or use. Its signature and proof are untouched. |

This repairs the return by restoring the nonempty module and its attached node
from the retained packet. The current base has neither the module nor its node,
and no `coord/rework.tsv` row or quarantine archive exists for it. F8 still holds
the original item claim. The theorem signature above remains identical to the
retained original node attachment. Nothing is withdrawn; the current absence of
users is not treated as permission to prune it. No target meaning changes.

The repair of return `1173900dfaa` removes the duplicate private theorem
`arbitrary_encoding_comparison` and imports the existing private
`finiteEncoding_constructible` using `import all Sheaf.Paper.IntegralCriterionReductions`.
The three comparison sites use that theorem directly. The private import exports
no additional interface. `tools/import_direction.py may` confirms no import cycle;
the parent module currently contains no reverse import or DAG dependency on this item.
The repaired file compiles with exit code 0. No existing public signature, instance,
consumer, or definition is changed by this duplicate-removal repair.

## Status

landed 20261024T185307-L-3500913 2026-10-24 (merge of deliver/F8/Sheaf.Paper.SuccessiveReductionConstructibility)
