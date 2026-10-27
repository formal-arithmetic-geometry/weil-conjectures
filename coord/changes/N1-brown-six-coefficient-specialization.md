# CategoryTheory.brownHypotheses_finiteIntermediateField

## Reason

Extend the already-proved private finite-rational-coefficient specialization to the
entire six-case coefficient range of the existing finite-field compactness theorem.
This is a genuine strengthening of the private helper: it now proves the full Brown
bundle for finite discrete rings, Z_l, O_E, Q_l, finite E and finite-subextension-valued
Qbar_l. The original public arbitrary-field theorem and BrownHypothesesFor definition
remain verbatim. No target signature or definition changes.

The new finiteCoefficientLiftIso is a proved private helper. It constructs the ring-sheaf
isomorphism explicitly by continuous postcomposition with the ULift ring equivalence,
then maps to condensed abelian groups and verifies the monoid-object structure.
It resolves the universe mismatch between the Type 0 finite-ring alternative in the
compactness theorem and the Type u finite-ring parameter in the smallness theorem.
No ring object is chosen from an unproved existence statement.

## Old

```lean
private theorem brownHypotheses_finiteIntermediateField
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) (F : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    BrownHypothesesFor (Profinite.continuousMapRingObj F) X
```

## New

```lean
private theorem brownHypotheses_finiteIntermediateField
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
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
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    BrownHypothesesFor Λ X
```

## Users

`tools/downstream.py Sheaf.SixFunctorsBasics.BrownHypotheses --uses
brownHypotheses BrownHypothesesFor` reports zero live downstream modules.
The private specialization has no external user. Existing public signatures, definition
bodies, public imports and visibility are identical, so preserved quarantined consumers
need no adaptation. Their arbitrary-field calls remain dependent on the disputed hole.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctorsBasics.BrownHypotheses | N1 | Private specialization strengthened and proved for six coefficient cases. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | quarantined; not adapted | Original public theorem calls and bundle interface unchanged. |
| Sheaf.Paper.ExceptionalInverseImageExistence | quarantined; not adapted | Original public theorem call unchanged. |
| Sheaf.Paper.BrownExceptionalAdjoint | quarantined; not adapted | Original public interface unchanged. |
| Sheaf.Paper.MateOpenRestriction | quarantined; not adapted | Original public interface unchanged. |

## Status

landed 20261023T131707-L-2139404 2026-10-23 (merge of deliver/N1/Sheaf.SixFunctorsBasics.BrownHypotheses)
