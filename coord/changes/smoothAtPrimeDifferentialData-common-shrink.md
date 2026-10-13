# Algebra.exists_smoothAtPrime_differential_data

## Reason

The old fixed-open assertion is false. Take R = the real numbers, n = 3, m = c = 1,
f = x²+y²+z²-1, a = 1, V the singleton, and q the evaluation prime at (0,0,1).
This smooth hypersurface has free conormal module of rank one (the nonzerodivisor
f supplies its basis). Its differential module is stably free of rank two but
is not free: a free algebraic cotangent basis would restrict to a continuous
cotangent frame on the real two-sphere and hence a nowhere-zero tangent field,
contradicting the hairy-ball theorem. The corrected statement follows the explicit
further shrink in the proof of Stacks Tag 07C6:
https://stacks.math.columbia.edu/tag/07C6 .

The target declarations and all definitions remain unchanged. The parent only
needs existence of a common localization, so its original statement is preserved.
No target meaning is changed; no renewed target-definition review is needed.

## Old

```lean
theorem exists_smoothAtPrime_differential_data (R : Type u) [CommRing R] (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) R) (a : MvPolynomial (Fin n) R) (V : Finset (Fin m)) (c : ℕ) (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) (ha : Ideal.Quotient.mk (Ideal.span (Set.range f)) a ∉ q.asIdeal) (hcard : V.card = c) (hbound : c ≤ min n m) (hsm : Algebra.Smooth R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))) : (∃ (e : Fin c ≃ V), ∃ b : Module.Basis (Fin c) (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)) (LocalizedModule.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) a) (Ideal.span (Set.range f)).Cotangent), ∀ j : Fin c, b j = LocalizedModule.mkLinearMap (Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)) (Ideal.span (Set.range f)).Cotangent ((Ideal.span (Set.range f)).toCotangent ⟨f (e j).1, Ideal.subset_span ⟨(e j).1, rfl⟩⟩)) → Nonempty (Module.Basis (Fin (n - c)) (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)) (KaehlerDifferential R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))))
```

## New

```lean
theorem exists_smoothAtPrime_differential_data (R : Type u) [CommRing R] (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) R) (a : MvPolynomial (Fin n) R) (V : Finset (Fin m)) (c : ℕ) (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) (ha : Ideal.Quotient.mk (Ideal.span (Set.range f)) a ∉ q.asIdeal) (_hcard : V.card = c) (hbound : c ≤ min n m) (hsm : Algebra.Smooth R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) a))) : (∃ (e : Fin c ≃ V), ∃ b : Module.Basis (Fin c) (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)) (LocalizedModule.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) a) (Ideal.span (Set.range f)).Cotangent), ∀ j : Fin c, b j = LocalizedModule.mkLinearMap (Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range f)) a)) (Ideal.span (Set.range f)).Cotangent ((Ideal.span (Set.range f)).toCotangent ⟨f (e j).1, Ideal.subset_span ⟨(e j).1, rfl⟩⟩)) → ∃ a' : MvPolynomial (Fin n) R, Ideal.Quotient.mk (Ideal.span (Set.range f)) a' ∉ q.asIdeal ∧ Algebra.Smooth R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) a')) ∧ (∃ (e : Fin c ≃ V), ∃ b : Module.Basis (Fin c) (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) a')) (LocalizedModule.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) a') (Ideal.span (Set.range f)).Cotangent), ∀ j : Fin c, b j = LocalizedModule.mkLinearMap (Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range f)) a')) (Ideal.span (Set.range f)).Cotangent ((Ideal.span (Set.range f)).toCotangent ⟨f (e j).1, Ideal.subset_span ⟨(e j).1, rfl⟩⟩)) ∧ Nonempty (Module.Basis (Fin (n - c)) (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) a')) (KaehlerDifferential R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range f)) a'))))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.SmoothAtPrimeDifferentialData | S3 | Own statement corrected and proved using the split conormal sequence and two fully proved helpers. |
| Sheaf.RingTheory.SmoothAtPrimeFreeConormalBasis | unclaimed | Forced adaptation only at the final proof lines: destructure the new shrink witness and assemble the unchanged conclusion on that open. |

The read-only downstream --uses search finds no other direct users. The 207
transitive importers see the unchanged parent statement. Its conormal-data
component stays needed by that parent, but is no longer needed by this item.

## Status

landed 20261013T001616-L-2330907 2026-10-13 (merge of deliver/S3/Sheaf.RingTheory.SmoothAtPrimeDifferentialData)
