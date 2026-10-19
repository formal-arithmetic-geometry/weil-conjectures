# SheafOfModules.locallyConstantFiniteTypeModules_reduction_succ

## Reason

The delivery fills the theorem's proof with private coefficient, complex and homology
helpers. The preflight scope-command check requires this record for the added `section`,
`variable`, `open`, local notation and local attribute commands. Every existing signature,
definition and visibility, and every public import, is unchanged. The additive helper is a
private proved theorem, registered as an instance only locally in its helper section and
introduced explicitly inside the main proof. No global instance is exported.

## Old

The original public declaration was:

```lean
theorem locallyConstantFiniteTypeModules_reduction_succ
    {C : Type u} [Category.{u} C] (T : Precoverage C)
    [T.HasIsos] [T.IsStableUnderComposition] [T.IsStableUnderBaseChange] [T.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B))]
    [∀ I : Ideal B, HasDerivedCategory.{w}
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck (B ⧸ I)))]
    (K : DerivedCategory
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B)))
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K))
    (hmod : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck (Ideal.Quotient.mk J)).obj K)))
    (n : ℕ) (hn : 1 ≤ n)
    (hprevious : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J ^ n)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck
          (Ideal.Quotient.mk (J ^ n))).obj K))) :
    ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J ^ (n + 1))
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck
          (Ideal.Quotient.mk (J ^ (n + 1)))).obj K)) := by
  sorry
```

The original top-level scopes were:

```lean
universe u w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules
```

## New

The public signature remains verbatim:

```lean
theorem locallyConstantFiniteTypeModules_reduction_succ
    {C : Type u} [Category.{u} C] (T : Precoverage C)
    [T.HasIsos] [T.IsStableUnderComposition] [T.IsStableUnderBaseChange] [T.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B))]
    [∀ I : Ideal B, HasDerivedCategory.{w}
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck (B ⧸ I)))]
    (K : DerivedCategory
      (SheafOfModules.{u} (constantCoefficientRing T.toGrothendieck B)))
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K))
    (hmod : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck (Ideal.Quotient.mk J)).obj K)))
    (n : ℕ) (hn : 1 ≤ n)
    (hprevious : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J ^ n)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck
          (Ideal.Quotient.mk (J ^ n))).obj K))) :
    ∀ i : ℤ, IsLocallyConstantFiniteTypeModules T.toGrothendieck (B ⧸ J ^ (n + 1))
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T.toGrothendieck
          (Ideal.Quotient.mk (J ^ (n + 1)))).obj K))
```

Its body is the complete quotient-triangle proof in the delivered module. The added proof
scopes are:

```lean
open scoped ZeroObject
section CoefficientTensor
open MonoidalCategory
variable {C : Type u} [Category.{u} C] {T : GrothendieckTopology C}
  {R S A : Sheaf T CommRingCat.{u}}
end CoefficientTensor
section TensorSequence
open MonoidalCategory
variable {V : Type*} [Category V] [Abelian V] [MonoidalCategory V]
  [MonoidalPreadditive V]
attribute [local instance] tensorComplex_additive
end TensorSequence
attribute [local irreducible] leftDerived_model
```

The coefficient section also has local `𝓡(...)` and `𝓻(...)` notation abbreviating the
underlying ring-sheaf functor on objects and morphisms. These scopes support only private
helpers; no private helper occurs in a public signature or public definition.
The local irreducibility attribute prevents elaboration from repeatedly unfolding the
composite comparison into the chosen derived-functor data. It does not alter any definition.

## Users

`tools/downstream.py Sheaf.Paper.NilpotentReductionStep --uses
SheafOfModules.locallyConstantFiniteTypeModules_reduction_succ` finds the following direct
textual users (the total import closure has many further modules). The only direct importer
is `Sheaf.Paper.NilpotentReductionLissity`. Both use the identical theorem statement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NilpotentReductionStep | G6 | Assigned module; proof filled, signature unchanged. |
| Sheaf.Paper.NilpotentReductionLissity | unclaimed | Existing application remains valid; no adaptation. |

All transitive importers receive the same public declarations and imports. No target's
meaning changes and no target statement is edited. No downstream file is adapted.

## Status

landed 20261019T192742-L-1862821 2026-10-19 (merge of deliver/G6/Sheaf.Paper.NilpotentReductionStep)
