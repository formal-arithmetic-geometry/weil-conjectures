# RingTheory.powerSeriesRingSubfields

## Reason

Human-authorized twin retirement, coord/changes/retire-sheaf-twins-20261020.md. The complete upstream theorem has exactly the same signature and proof after renaming. No current Lean module imports the Sheaf copy or uses its declaration.

## Old

```lean
theorem powerSeriesRingSubfields
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    (I : Type w) (t : I → k)
    (hpb : ∃ b : Module.Basis
      {E : I →₀ ℕ // ∀ i : I, E i < p}
      (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k => x ^ p))) k,
      ∀ E, b E = (E : I →₀ ℕ).prod (fun i e => t i ^ e))
    (n m : ℕ)
    (K : Type v) [Field K]
    [Algebra (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K]
    [IsFractionRing (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K]
    (kJ : Finset I → Subfield k)
    (hkJ : ∀ J, kJ J = Subfield.closure
      (Set.range (fun x : k => x ^ p) ∪ {x : k | ∃ i : I, i ∉ J ∧ t i = x}))
    (AJ : Finset I → Subring (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))
    (hAJ : ∀ J f, f ∈ AJ J ↔
      ∀ (a : Fin n →₀ ℕ) (g : Fin m →₀ ℕ),
        MvPowerSeries.coeff a (MvPolynomial.coeff g f) ∈ kJ J ∧
        (MvPowerSeries.coeff a (MvPolynomial.coeff g f) ≠ 0 →
          (∀ i, p ∣ a i) ∧ (∀ j, p ∣ g j)))
    (KJ : Finset I → Subfield K)
    (hKJ : ∀ J z, z ∈ KJ J ↔
      ∃ a b : AJ J, (b : MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) ≠ 0 ∧
        z = algebraMap (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K a /
          algebraMap (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K b) :
    (∀ J : Finset I,
      Module.Finite (AJ J) (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) ∧
      (∀ J : Finset I, Set.range (fun x : K => x ^ p) ⊆ (KJ J : Set K)) ∧
      (Set.range (fun x : K => x ^ p) = ⋂ J : Finset I, (KJ J : Set K)) ∧
      (∀ J J' : Finset I, KJ (J ∪ J') ≤ KJ J ⊓ KJ J')
```

## New

The Sheaf module is withdrawn; use the existing upstream declaration:

```lean
theorem iInter_frobenius_subfields_mvPolynomial_mvPowerSeries
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    (I : Type w) (t : I → k)
    (hpb : ∃ b : Module.Basis
      {E : I →₀ ℕ // ∀ i : I, E i < p}
      (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k => x ^ p))) k,
      ∀ E, b E = (E : I →₀ ℕ).prod (fun i e => t i ^ e))
    (n m : ℕ)
    (K : Type v) [Field K]
    [Algebra (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K]
    [IsFractionRing (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K]
    (kJ : Finset I → Subfield k)
    (hkJ : ∀ J, kJ J = Subfield.closure
      (Set.range (fun x : k => x ^ p) ∪ {x : k | ∃ i : I, i ∉ J ∧ t i = x}))
    (AJ : Finset I → Subring (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))
    (hAJ : ∀ J f, f ∈ AJ J ↔
      ∀ (a : Fin n →₀ ℕ) (g : Fin m →₀ ℕ),
        MvPowerSeries.coeff a (MvPolynomial.coeff g f) ∈ kJ J ∧
        (MvPowerSeries.coeff a (MvPolynomial.coeff g f) ≠ 0 →
          (∀ i, p ∣ a i) ∧ (∀ j, p ∣ g j)))
    (KJ : Finset I → Subfield K)
    (hKJ : ∀ J z, z ∈ KJ J ↔
      ∃ a b : AJ J, (b : MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) ≠ 0 ∧
        z = algebraMap (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K a /
          algebraMap (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K b) :
    (∀ J : Finset I,
      Module.Finite (AJ J) (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))) ∧
      (∀ J : Finset I, Set.range (fun x : K => x ^ p) ⊆ (KJ J : Set K)) ∧
      (Set.range (fun x : K => x ^ p) = ⋂ J : Finset I, (KJ J : Set K)) ∧
      (∀ J J' : Finset I, KJ (J ∪ J') ≤ KJ J ⊓ KJ J')
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.PowerSeriesRingSubfields | Q4 | Withdraw unused duplicate. |
| WeilConjectures.RingTheory.PowerSeriesFiniteSubfieldFamily | unchanged | Already imports and uses the upstream theorem; compile checked. |
| WeilConjectures.RingTheory.Derivation.PowerSeriesPolynomialDifferential | unchanged | Already imports the upstream module; compile checked. |

No current consumer of the withdrawn declaration or module exists. The two Sheaf consumers listed in the retirement inventory are already absent. No target signature or definition changes.

## Status

landed 20261020T132024-L-1403080 2026-10-20 (merge of deliver/Q4/Sheaf.RingTheory.PowerSeriesRingSubfields)
