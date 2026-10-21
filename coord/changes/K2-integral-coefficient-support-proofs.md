# Coefficient support theorem proofs

## Reason

These existing assertions are direct inputs to the integral completed criterion.
Fill their proof holes without changing the mathematical interface. The module
`Sheaf.Paper.BoundedConstructibleComplete` is unclaimed when checked.

## Old

```lean
theorem pbcFunctionScalars_locallyBijective (n : ℕ) :
    Presheaf.IsLocallyInjective (ProEt.topology T) (pbcFunctionScalars T d n) ∧
      Presheaf.IsLocallySurjective (ProEt.topology T) (pbcFunctionScalars T d n)

theorem pbcAssociatedRestriction_exists
    (P Q : Type (u + 1)) [CommRing P] [CommRing Q]
    (R S : Sheaf (ProEt.topology T) RingCat.{u + 1})
    (α : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    (β : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of Q) ⟶ S.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology T) α]
    [Presheaf.IsLocallySurjective (ProEt.topology T) α]
    [Presheaf.IsLocallyInjective (ProEt.topology T) β]
    [Presheaf.IsLocallySurjective (ProEt.topology T) β]
    (q : P →+* Q) (r : R ⟶ S)
    (_h : α ≫ r.hom = (Functor.const T.ProEtᵒᵖ).map (RingCat.ofHom q) ≫ β) :
    ∃! e : Sheaf.restrictScalars (ProEt.topology T) q ⋙ pbcAssociatedModule T P R α ≅
        pbcAssociatedModule T Q S β ⋙ SheafOfModules.restrictScalars r,
      Functor.whiskerRight e.hom (SheafOfModules.toSheaf R) =
        (pbcAssociatedRestrictionSource T P Q R α q).hom ≫
          (pbcAssociatedRestrictionTarget T Q R S β r).inv

theorem pbcFunctionRealization_exact (n : ℕ) :
    (pbcFunctionRealization T d n).IsEquivalence ∧
      (pbcFunctionRealization T d n).Additive ∧
      PreservesFiniteLimits (pbcFunctionRealization T d n) ∧
      PreservesFiniteColimits (pbcFunctionRealization T d n)

theorem pbcDerivedFunctionRealization_equivalence (n : ℕ) :
    (pbcDerivedFunctionRealization T d n).IsEquivalence

theorem pbcFunctionScalars_comp (n : ℕ) :
    pbcFunctionScalars T d (n + 1) ≫
        ((adicLisseForget T).map
          (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).hom =
      (Functor.const T.ProEtᵒᵖ).map
        (RingCat.ofHom (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))) ≫
          pbcFunctionScalars T d n

theorem pbcFunctionReductionMap_isIso (n : ℕ) : IsIso (pbcFunctionReductionMap T d n)

theorem pbcCoefficientDatumProperties :
    IsNoetherianRing (PbcIntegralRing l E) ∧
      (Ideal.span ({pbcUniformizer l E} : Set (PbcIntegralRing l E))).FG ∧
      (∀ x : PbcIntegralRing l E ⧸ Ideal.span {pbcUniformizer l E},
        ∃ m : ℕ, 0 < m ∧ m • x = 0) ∧
      (∀ n : ℕ, 1 ≤ n → adicQuotientPerfect (PbcIntegralRing l E)
        (Ideal.span {pbcUniformizer l E}) n) ∧
      ∀ n : ℕ, Finite (PbcIntegralRing l E ⧸
        (Ideal.span {pbcUniformizer l E}) ^ (n + 1))
```

## New

Every signature above is identical. Definition bodies, public imports and visibility
are unchanged; only proofs, private proof imports and proved private helpers change.
The coefficient proof transports the DVR structures and finite quotients through
ULift, then constructs the actual two-term finite free quotient resolutions. The
realization proofs reuse the existing associated-module equivalence. The inverse-mate
argument is adapted from `FiniteConstantCoefficientTransport`: conjugate the two
adjunctions by the realization equivalences, and use the iterated-mate identity.
The scalar normalization follows from sheafification units and their naturality.

## Users

`tools/downstream.py --uses` finds only the defining module using the five previously
checked proof names directly; their instances and definitions retain the same types.
All 267 transitive module consumers therefore see identical interfaces and definition
bodies. No consumer requires adaptation, and no target meaning changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.BoundedConstructibleComplete | unclaimed | Existing theorem proofs filled. |
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | K2 | Uses the same coefficient datum. |

## Status

landed 20261021T061432-L-1774768 2026-10-21 (merge of deliver/K2/Sheaf.Paper.IntegralStratifiedPerfectCharacterization)
