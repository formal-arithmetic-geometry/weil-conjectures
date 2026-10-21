# AlgebraicGeometry.ProEtale.CondensedRing.constructible_open_closed_images

## Reason

Restore the source preserved by the current rework row and repair its failing
elimination of a dependent existential. The preserved theorem already has zero
sorry proofs. Its actual constructibility argument is retained.

## Old

The live path `lean/Sheaf/Paper/CondensedConstructibleOpenClosedImages.lean` is absent.
Its authoritative source is
`quarantine/Sheaf/Paper/CondensedConstructibleOpenClosedImages.lean`.
The proof starts with:

```lean
  obtain ⟨hex, _, _, _, _, _, _, _, _, _, _, _, ⟨e⟩, _⟩ :=
    condensed_open_closed_recollement Λ k j hjk
```

This fails with `Tactic generalize failed: result is not type correct`.

## New

Restore the archived module and preserve its exact theorem signature, universes,
public imports and dependencies. Replace only the counit acquisition with:

```lean
  have := moduleCounitOfAbelian Λ k (ProEtale.abelian_closed_support k j hjk).1
  let e := asIso (upperStarLowerStarAdjunction Λ k).counit
```

Add the proof-only import of
`Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport` and clarify the docstring.
The existing vanishing, scalar transport and stratification arguments are unchanged.
Update the attached node's proof, proof_deps and proof_origin accordingly.
No definition or mathematical statement changes, and no target review is reopened.
The restored module compiles cleanly in 3.6 seconds.

## Users

A direct import scan of both live Lean roots and both quarantine roots finds the
three consumers below. All are quarantined and remain untouched. The restored
signature and public import interface agree verbatim with the archive, so their
existing uses still receive exactly the same theorem. The source-only downstream
script cannot inventory an absent live item; the quarantine scan supplies this
inventory. No adaptations or additional claims are needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | not queried; not edited | Identical theorem interface; no adaptation. |
| Sheaf.Paper.IntegralTensorShriek | not queried; not edited | Identical theorem interface; no adaptation. |
| Sheaf.Paper.ProperHeartBoundTorsion | not queried; not edited | Identical theorem interface; no adaptation. |

## Status

landed 20261021T021007-L-2689102 2026-10-21 (merge of deliver/D3/Sheaf.Paper.CondensedConstructibleOpenClosedImages)
