# CategoryTheory.brownHypotheses_admissible_small

## Reason

Use the actual admissibility predicate in this private proof helper. Previously its
signature repeated and reordered the six alternatives, and its caller repeated the
conversion. The helper now matches those alternatives directly. Every public statement,
definition, instance and public import is unchanged.

The finite-field proof now chooses one skeleton and feeds its compactness directly to
the representative Brown criterion. The integral criterion uses the existing integral
compactness theorem and rewrites its entire witness along the closure equality. These
proofs remove the need to import BrownHypothesesArbitraryFieldCompactness.

## Old

```lean
private theorem brownHypotheses_admissible_small
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ r : ℕ, ∀ a : A, (ℓ ^ r) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X] :
    let S := constantModelBoundedConstructible Λ X ⊓
      fun K ↦ DerivedCategory.finiteTorAmplitude _ K
    S.IsTriangulated ∧ S.IsClosedUnderIsomorphisms ∧ S.IsStableUnderRetracts ∧
      ObjectProperty.EssentiallySmall.{u + 1} S
```

## New

```lean
private theorem brownHypotheses_admissible_small
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X] :
    let S := constantModelBoundedConstructible Λ X ⊓
      fun K ↦ DerivedCategory.finiteTorAmplitude _ K
    S.IsTriangulated ∧ S.IsClosedUnderIsomorphisms ∧ S.IsStableUnderRetracts ∧
      ObjectProperty.EssentiallySmall.{u + 1} S
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctorsBasics.BrownHypotheses | G4 | Private smallness helper uses the actual predicate; valid compactness proofs simplified. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not adapted | Direct importer; identical public interface and all existing proofs remain available. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not adapted | Direct importer; identical public interface and all existing proofs remain available. |

The private helper has no external source references. No consumer needs adaptation;
no global attribute or instance has changed.

## Status

landed 20261027T094410-L-222683 2026-10-27 (merge of deliver/G4/Sheaf.SixFunctorsBasics.BrownHypotheses)
