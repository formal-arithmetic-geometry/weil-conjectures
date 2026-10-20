# pbc_constructible_reduction_criterion and its reduction-operation interfaces

## Reason

Repair C-acb12 points 1--3. The returned packet duplicated the landed integral uniform
criterion and its cohomology predicate. Use the existing uniform-profile homologyProperty
clause, specialize the criterion to the integral datum, and remove the duplicate predicate,
model assembly, origin assembly and local-descent modules. These packet modules never
landed on main; their only consumers are in this packet. The assigned preservation theorem
retains its exact signature and all eight conclusions.

## Old

```lean
theorem pbc_constructible_reduction_criterion
    (T : Scheme.{u}) [IsNoetherian T] {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (a b : ℤ) (K : PbcCompletedDerived T d)
    (_hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj ((pbcCompletedReduction T d n).obj K))) :
    PbcIsBoundedConstructibleComplete T d K ↔
      PbcIsIntrinsicallyComplete T d K ∧ pbcReductionCohomologyConstructible T d K
```

```lean
theorem pbc_constructible_reduction_directImage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (_hDimS : ∃ k : ℕ, topologicalKrullDim S ≤ (k : WithBot ℕ∞))
    (_hDimT : ∃ k : ℕ, topologicalKrullDim T ≤ (k : WithBot ℕ∞))
    (f : S ⟶ T) [IsProper f] (N : ℕ) (_hN : 0 < N)
    (_hAnn : (N : Padic.coefficientExtensionRing l E 1) = 0)
    (_hInvertS : IsUnit (N : Γ(S, ⊤))) (_hInvertT : IsUnit (N : Γ(T, ⊤)))
    (e : ℕ)
    (_hFib : ∀ (Ω : Type u) [Field Ω] (y : Spec (.of Ω) ⟶ T),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (a b : ℤ) (K : PbcCompletedDerived S (pbcIntegralDatum l E))
    (_hcomplete : PbcIsIntrinsicallyComplete S (pbcIntegralDatum l E) K)
    (_hconstructible : pbcReductionCohomologyConstructible S (pbcIntegralDatum l E) K)
    (_hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcCompletedReduction S (pbcIntegralDatum l E) n).obj K))) :
    PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E)
        ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K) ∧
      pbcReductionCohomologyConstructible T (pbcIntegralDatum l E)
        ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K) ∧
      ∀ (n : ℕ) (q : ℤ), (q < a ∨ b + 2 * (e : ℤ) < q) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj
            ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K)))
```

```lean
theorem pbc_constructible_reduction_pullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T] (g : S ⟶ T)
    (a b : ℤ) (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (_hcomplete : PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E) K)
    (_hconstructible : pbcReductionCohomologyConstructible T (pbcIntegralDatum l E) K)
    (_hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K))) :
    PbcIsIntrinsicallyComplete S (pbcIntegralDatum l E)
        (completedPullbackObject g (pbcIntegralDatum l E) K) ∧
      pbcReductionCohomologyConstructible S (pbcIntegralDatum l E)
        (completedPullbackObject g (pbcIntegralDatum l E) K) ∧
      ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((pbcCompletedReduction S (pbcIntegralDatum l E) n).obj
            (completedPullbackObject g (pbcIntegralDatum l E) K)))
```

## New

```lean
theorem pbc_constructible_reduction_criterion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T] (a b : ℤ)
    (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K))) :
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K ↔
      PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E) K ∧
        ∀ n : ℕ, DerivedCategory.homologyProperty
          (@IsConstructibleProEtaleCoefficientModuleSheaf T
            (PbcQuotient (pbcIntegralDatum l E) n) _
            ((pbcIntegralDatum l E).quotientFinite n))
          ((pbcConstantReduction T (pbcIntegralDatum l E) n).obj K)
```

```lean
theorem pbc_constructible_reduction_directImage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (_hDimS : ∃ k : ℕ, topologicalKrullDim S ≤ (k : WithBot ℕ∞))
    (_hDimT : ∃ k : ℕ, topologicalKrullDim T ≤ (k : WithBot ℕ∞))
    (f : S ⟶ T) [IsProper f] (N : ℕ) (_hN : 0 < N)
    (_hAnn : (N : Padic.coefficientExtensionRing l E 1) = 0)
    (_hInvertS : IsUnit (N : Γ(S, ⊤))) (_hInvertT : IsUnit (N : Γ(T, ⊤)))
    (e : ℕ)
    (_hFib : ∀ (Ω : Type u) [Field Ω] (y : Spec (.of Ω) ⟶ T),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (a b : ℤ) (K : PbcCompletedDerived S (pbcIntegralDatum l E))
    (_hcomplete : PbcIsIntrinsicallyComplete S (pbcIntegralDatum l E) K)
    (_hconstructible : (fun K ↦ ∀ n : ℕ, DerivedCategory.homologyProperty
        (@IsConstructibleProEtaleCoefficientModuleSheaf S
          (PbcQuotient (pbcIntegralDatum l E) n) _
          ((pbcIntegralDatum l E).quotientFinite n))
        ((pbcConstantReduction S (pbcIntegralDatum l E) n).obj K)) K)
    (_hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcCompletedReduction S (pbcIntegralDatum l E) n).obj K))) :
    PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E)
        ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K) ∧
      (fun K ↦ ∀ n : ℕ, DerivedCategory.homologyProperty
        (@IsConstructibleProEtaleCoefficientModuleSheaf T
          (PbcQuotient (pbcIntegralDatum l E) n) _
          ((pbcIntegralDatum l E).quotientFinite n))
        ((pbcConstantReduction T (pbcIntegralDatum l E) n).obj K))
        ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K) ∧
      ∀ (n : ℕ) (q : ℤ), (q < a ∨ b + 2 * (e : ℤ) < q) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj
            ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K)))
```

```lean
theorem pbc_constructible_reduction_pullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T] (g : S ⟶ T)
    (a b : ℤ) (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (_hcomplete : PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E) K)
    (_hconstructible : (fun K ↦ ∀ n : ℕ, DerivedCategory.homologyProperty
        (@IsConstructibleProEtaleCoefficientModuleSheaf T
          (PbcQuotient (pbcIntegralDatum l E) n) _
          ((pbcIntegralDatum l E).quotientFinite n))
        ((pbcConstantReduction T (pbcIntegralDatum l E) n).obj K)) K)
    (_hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K))) :
    PbcIsIntrinsicallyComplete S (pbcIntegralDatum l E)
        (completedPullbackObject g (pbcIntegralDatum l E) K) ∧
      (fun K ↦ ∀ n : ℕ, DerivedCategory.homologyProperty
        (@IsConstructibleProEtaleCoefficientModuleSheaf S
          (PbcQuotient (pbcIntegralDatum l E) n) _
          ((pbcIntegralDatum l E).quotientFinite n))
        ((pbcConstantReduction S (pbcIntegralDatum l E) n).obj K))
        (completedPullbackObject g (pbcIntegralDatum l E) K) ∧
      ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((pbcCompletedReduction S (pbcIntegralDatum l E) n).obj
            (completedPullbackObject g (pbcIntegralDatum l E) K)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PreservationConstructible | B5 | Five criterion calls pass l and E; all output conclusions unchanged. |
| Sheaf.Paper.PbcConstructibleReductionCriterion | B5 packet | Integral uniform criterion replaces duplicate assembly modules. |
| Sheaf.Paper.PbcConstructibleReductionDirectImage | B5 packet | Exact homology isomorphism transports the existing profile clause. |
| Sheaf.Paper.PbcConstructibleReductionPullback | B5 packet | Exact homology isomorphism transports the existing profile clause. |
| Sheaf.Paper.PbcFiniteDirectImageCohomology | B5 packet | Import the existing profile instead of the withdrawn duplicate; the finite theorem signature is unchanged apart from an unused binder name. |
| Sheaf.Paper.PbcFinitePullbackConstructibility | B5 packet | Import the existing profile instead of the withdrawn duplicate; theorem signature unchanged. |

The shared tree contains the assigned PreservationConstructible module but none of
the five packet support modules. A source search for the support modules and their
declaration names finds no external consumer. No other group's module
is adapted. The four deleted modules and their nodes existed only in the returned packet;
they are removed from this resubmission, rather than withdrawn from the live library.
The target declarations and definitions they use have unchanged meanings.

## Status

landed 20261020T051020-L-1529792 2026-10-20 (merge of deliver/B5/Sheaf.Paper.PreservationConstructible)
