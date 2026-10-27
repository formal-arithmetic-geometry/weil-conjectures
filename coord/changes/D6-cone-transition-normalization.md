# WeilConjectures.ConcreteIntegralProjection.coneTransition

## Reason

Write the original inferred source and target of the two-summand cone map
explicitly, and mark `coneComparison` and `coneTransition` `[irreducible]`, so
that importing proofs do not repeatedly expand their signed-biproduct
implementations. The body is unchanged: it is still the map of cones induced by
the unrestricted quotient transitions on both summands. (The delivered version
had replaced the body by a transport of the intrinsic transition through the
cone comparisons, which made the item's last conjunct nearly definitional; the
reviewer restored the original body.)

In the item's proof, the private theorem `transition_eq` identifies the
unrestricted transition with the intrinsic one by their unique sectionwise
pure-tensor formula, and the private generic theorem `coneNaturality` (degreewise
cone naturality of a natural transformation of additive functors) then proves
the signed-cone equations `intrinsicConeTransition_eq` and `coneTransition_eq`.
No target statement changes.

## Old

```lean
def coneTransition (W : Scheme.{u})
    {P Q : CochainComplex (scalarReductionSource l E W) ℤ} (v : P ⟶ Q) (n : ℕ) :=
  CochainComplex.mappingCone.map
    (((sfReductionRestricted l E W (n + 1)).mapHomologicalComplex (.up ℤ)).map v)
    (((sfReductionRestricted l E W n).mapHomologicalComplex (.up ℤ)).map v)
    (unrestrictedTowerTransition l E W P n) (unrestrictedTowerTransition l E W Q n)
    ((unrestrictedIntegralTransition l E W n).naturality v)
```

## New

```lean
def coneTransition (W : Scheme.{u})
    {P Q : CochainComplex (scalarReductionSource l E W) ℤ} (v : P ⟶ Q) (n : ℕ) :
    CochainComplex.mappingCone
      (((sfReductionRestricted l E W (n + 1)).mapHomologicalComplex (.up ℤ)).map v) ⟶
        CochainComplex.mappingCone
          (((sfReductionRestricted l E W n).mapHomologicalComplex (.up ℤ)).map v) :=
  CochainComplex.mappingCone.map
    (((sfReductionRestricted l E W (n + 1)).mapHomologicalComplex (.up ℤ)).map v)
    (((sfReductionRestricted l E W n).mapHomologicalComplex (.up ℤ)).map v)
    (unrestrictedTowerTransition l E W P n) (unrestrictedTowerTransition l E W Q n)
    ((unrestrictedIntegralTransition l E W n).naturality v)

attribute [irreducible] coneComparison coneTransition
```

## Users

`tools/downstream.py Sheaf.Paper.ConcreteIntegralProjectionCone --uses coneTransition`
finds only the defining module. The single downstream module,
`Sheaf.Paper.ConcreteProjectionFieldDescent`, does not mention this definition.
Its value and type are unchanged; no consumer requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConcreteIntegralProjectionCone | D6 | Explicit type and irreducibility; same value. |

## Status

landed 20261025T201631-L-2591332 2026-10-25 (merge of deliver/D6/Sheaf.Paper.ConcreteIntegralProjectionCone)
