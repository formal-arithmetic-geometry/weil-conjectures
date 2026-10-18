# CochainComplex.exists_projective_lift_of_nilpotent

## Reason

The preflight conservatively flags the additional universe and open commands needed to
elaborate private proof helpers. They are local elaboration context; no global instance,
notation, attribute, public definition, or existing declaration signature changes. The
public imports are preserved verbatim; every added import is proof-only. All new definitions
and helper theorems are private, and all their proofs are complete.

The proof uses extra universe names for universal derived-functor transport across four
independently chosen derived categories. It opens limits and existing tensor/scalar notations
to express the quotient and K-flat computations. These commands do not change any target's
meaning or any importing module's elaboration context.

## Old

```lean
universe u v w w'

open CategoryTheory
```

The original public declaration signature is:

```lean
theorem exists_projective_lift_of_nilpotent
    (A : Type u) [CommRing A] (I : Ideal A)
    (hI : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = ⊥)
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (A ⧸ I))]
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} (A ⧸ I)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars (Ideal.Quotient.mk I))
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))]
    (C : DerivedCategory (ModuleCat.{max u v} A))
    (E : CochainComplex (ModuleCat.{max u v} (A ⧸ I)) ℤ)
    (hEbound : ∃ b : ℤ, E.IsStrictlyLE b)
    (hEproj : ∀ i : ℤ, Module.Projective (A ⧸ I) (E.X i))
    (hReduction : Nonempty (L.obj C ≅ DerivedCategory.Q.obj E)) :
    ∃ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      (∃ b : ℤ, P.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Projective A (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ C) ∧
      Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ≅ E)
```

## New

```lean
universe u v w w' w₀ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct Pointwise ChangeOfRings
```

Each transparency option before a helper has a trailing `in`, so it applies only to that
private declaration. Existing public statements and visibility remain identical. The
public theorem now has a complete proof. Its signature, compared verbatim, remains:

```lean
theorem exists_projective_lift_of_nilpotent
    (A : Type u) [CommRing A] (I : Ideal A)
    (hI : ∃ N : ℕ, 1 ≤ N ∧ I ^ N = ⊥)
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (A ⧸ I))]
    (L : DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} (A ⧸ I)))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars (Ideal.Quotient.mk I))
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).left_adjoint_additive
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))]
    (C : DerivedCategory (ModuleCat.{max u v} A))
    (E : CochainComplex (ModuleCat.{max u v} (A ⧸ I)) ℤ)
    (hEbound : ∃ b : ℤ, E.IsStrictlyLE b)
    (hEproj : ∀ i : ℤ, Module.Projective (A ⧸ I) (E.X i))
    (hReduction : Nonempty (L.obj C ≅ DerivedCategory.Q.obj E)) :
    ∃ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      (∃ b : ℤ, P.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Projective A (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ C) ∧
      Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ≅ E)
```

## Users

`tools/downstream.py Sheaf.RingTheory.NilpotentProjectiveComplexLift` lists the four
consumers below. None currently has a claim on this machine. Every existing public signature
and the public import interface remain identical, so no consumer adaptation is required.

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.NilpotentProjectiveComplexLift | A2 | Complete proof; private helpers and proof imports. |
| Sheaf.RingTheory.PseudoCoherentInverseRingReconstruction | unclaimed | Unchanged; same public interface and theorem signature. |
| Sheaf.RingTheory.PseudoCoherentNilpotentInvariance | unclaimed | Unchanged; same public interface and theorem signature. |
| Sheaf.RingTheory.PseudoCoherentNormalizedAlgebraTower | unclaimed | Unchanged; same public interface and theorem signature. |
| Sheaf.RingTheory.RlimPerfectComplete | unclaimed | Unchanged; same public interface and theorem signature. |

No target uses a changed definition. `#print axioms` for the proved theorem reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Status

landed 20261018T091355-L-3252488 2026-10-18 (merge of deliver/A2/Sheaf.RingTheory.NilpotentProjectiveComplexLift)
