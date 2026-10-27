# AlgebraicGeometry.FiniteReduction.System.coherentAt

## Reason

Restore the quarantined coherence module after upstream sync `8bd69aede` and repair
its ordinary comparison proof. The archived proof fails at generic cancellation
of a sheaf associator inverse, with a stuck coefficient-module universe constraint.
The replacement uses the explicit isomorphism cancellation lemmas and their mapped
inverse equations, avoiding mono/epi instance synthesis. This is a proof-only
elaboration repair; no definition, signature, or public import changes.

## Old

```lean
theorem System.coherentAt (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (S : System T l) (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m)
    (K : DerivedCategory
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r)))) :
    S.CoherentAt r m n hmr hnm K
```

The private `ordinary_coherence` proof cancels the mapped inverse with `cancel_epi`
and the pro-etale associator inverse with `cancel_mono`.

## New

```lean
theorem System.coherentAt (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (S : System T l) (r m n : ℕ) (hmr : m ≤ r) (hnm : n ≤ m)
    (K : DerivedCategory
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r)))) :
    S.CoherentAt r m n hmr hnm K
```

The private `ordinary_coherence` proof cancels the same explicit isomorphisms with
`Iso.cancel_iso_inv_left` and `Iso.cancel_iso_inv_right`; simplification includes
`Functor.mapIso_inv`. All other proof steps are preserved.

## Users

The live downstream scan reports zero modules. Searching `lean/` and `quarantine/`
also identifies the following archived consumer, which is retained. No target
statement or definition changes, so no target meaning review is reopened.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteReductionSystemExistence | unclaimed | Quarantined direct consumer; theorem signature unchanged; no adaptation. |

The DAG node `lem-pur-finite-reduction-system-coherence` retains the same Lean
attachment, statement, proof steps and dependencies. No node update is needed.

## Status

landed 20261023T151753-L-406967 2026-10-23 (merge of deliver/A3/Sheaf.Paper.FiniteReductionSystemCoherence)
