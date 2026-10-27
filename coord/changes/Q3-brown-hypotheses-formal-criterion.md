# CategoryTheory.brownHypothesesFor_iff

## Reason

The public arbitrary-field Brown theorem is already disputed. Its proved formal
assembly should identify the remaining geometric inputs in both directions without
claiming the unavailable compactness theorem. Add a proved criterion for arbitrary
schemes and commutative condensed coefficients, and use its reverse implication
in the existing six-case geometric finite-field specialization.

The nontrivial forward implication chooses a small equivalent category using the
bundle's essential-smallness clause, applies the any-presentation compactness clause,
and transports compactness to each constructible finite-Tor object along the
unit of that equivalence. The reverse implication uses the structural theorem and
the existing orthogonal/minimality generation proof.

## Old

There was no public `brownHypothesesFor_iff` declaration. The one-way private
`brownHypothesesFor_of_compact` was applied directly by the finite-field specialization:

```lean
  apply brownHypothesesFor_of_compact Λ X hS
  intro K hK
```

## New

```lean
theorem brownHypothesesFor_iff
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    BrownHypothesesFor Λ X ↔
      let S := constantModelBoundedConstructible Λ X ⊓
        fun K ↦ DerivedCategory.finiteTorAmplitude _ K
      S.IsTriangulated ∧ S.IsClosedUnderIsomorphisms ∧ S.IsStableUnderRetracts ∧
        ObjectProperty.EssentiallySmall.{u + 1} S ∧
        ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
          letI := hSums
          ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
            S K.obj → IsCompactObject K
```

The finite-field specialization now uses the public criterion, dropping its separate
structural-theorem application because the criterion supplies those structures:

```lean
  apply (brownHypothesesFor_iff Λ X).mpr
  refine ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2, hcop, ?_⟩
  intro K hK
```

Every pre-existing declaration signature, definition body, visibility and public
import is unchanged. The sole existing sorry remains in brownHypotheses; no hole
is moved, added or disguised as a hypothesis. No source-library file is edited.

## Users

`python3 tools/downstream.py Sheaf.SixFunctorsBasics.BrownHypotheses --uses
brownHypothesesFor_iff BrownHypothesesFor brownHypotheses` reports zero live downstream
modules. The four DAG parents are also preserved in quarantine. Their old theorem
calls and every part of the original bundle remain identical, so no adaptation is
forced and no parent dependency is removed. No target meaning changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctorsBasics.BrownHypotheses | Q3 | New proved criterion used in private finite-field assembly. |
| Sheaf.Paper.BrownExceptionalAdjoint | quarantined; not adapted | Existing public interface unchanged. |
| Sheaf.Paper.ExceptionalInverseImageExistence | quarantined; not adapted | Existing public theorem calls unchanged. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | quarantined; not adapted | Existing public theorem calls unchanged. |
| Sheaf.Paper.MateOpenRestriction | quarantined; not adapted | Existing public interface unchanged. |

## Status

landed 20261024T190642-L-4180066 2026-10-24 (merge of deliver/Q3/Sheaf.SixFunctorsBasics.BrownHypotheses)
