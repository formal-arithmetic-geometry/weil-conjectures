# Rep.contract_insert_zero and Rep.contract_insert_succ

## Reason

Repair of the return at head 00fc1e143: the homotopy-identity delivery duplicated
these two existing private lemmas. Make the original lemmas public in their
unclaimed module and use them through a proof-only import. Their hypotheses,
conclusions and proofs are unchanged. No definition or target statement changes.

## Old

```lean
private theorem contract_insert_zero (G : Type u) [Group G] (n : ℕ)
    (g : Fin (n + 1) → G) (x : G) :
    Fin.contractNth 0 (· * ·) (Fin.cons x g) =
      Fin.cons (x * g 0) (fun i ↦ g i.succ)

private theorem contract_insert_succ (G : Type u) [Group G] (n : ℕ)
    (g : Fin (n + 1) → G) (x : G) (k : Fin (n + 1)) :
    Fin.contractNth k.succ (· * ·) (Fin.cons x g) =
      Fin.cons x (Fin.contractNth k (· * ·) g)
```

## New

```lean
theorem contract_insert_zero (G : Type u) [Group G] (n : ℕ)
    (g : Fin (n + 1) → G) (x : G) :
    Fin.contractNth 0 (· * ·) (Fin.cons x g) =
      Fin.cons (x * g 0) (fun i ↦ g i.succ)

theorem contract_insert_succ (G : Type u) [Group G] (n : ℕ)
    (g : Fin (n + 1) → G) (x : G) (k : Fin (n + 1)) :
    Fin.contractNth k.succ (· * ·) (Fin.cons x g) =
      Fin.cons x (Fin.contractNth k (· * ·) g)
```

Only visibility and documentation change in the original module. Its existing
contraction proof uses the same lemmas with identical arguments.

## Users

`tools/downstream.py` with `--uses contract_insert_zero` and
`--uses contract_insert_succ` found only the defining module among existing users.
The table also includes all nine transitive downstream modules and the new user.
No other consumer needs adaptation, and no target needs statement re-review.
Claim status was checked on 2026-10-18 before editing.

| module | group holding it | effect |
|---|---|---|
| Sheaf.RepresentationTheory.LocallyConstantCochainsAcyclicEmbedding | unclaimed | Existing internal uses unchanged; expose the two proved helpers. |
| Sheaf.RepresentationTheory.CoinducedHomotopyIdentity | P1 | Delete duplicate private lemmas; import and use the originals. |
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unclaimed | No helper use; unchanged. |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | unclaimed | No helper use; unchanged. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | No helper use; unchanged. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding | unclaimed | No helper use; unchanged. |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | unclaimed | No helper use; unchanged. |
| Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison | unclaimed | No helper use; unchanged. |
| Sheaf.RepresentationTheory.DiscreteResolutionContinuousCohomology | unclaimed | No helper use; unchanged. |
| Sheaf.RepresentationTheory.DiscreteResolutionInhomogeneousCohomology | unclaimed | No helper use; unchanged. |
| Sheaf.RepresentationTheory.LocallyConstantCochainsEffaceable | unclaimed | No helper use; unchanged. |

## Status

landed 20261018T071208-L-1673419 2026-10-18 (merge of deliver/P1/Sheaf.RepresentationTheory.CoinducedHomotopyIdentity)
