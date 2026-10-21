# AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_pullback_cube

## Reason

Restore the assigned module from the quarantine path named in coord/rework.tsv.
The archive contains the complete cube proof and zero sorry occurrences. The recorded
upstream-sync error is an unknown finiteCoefficientDerivedToAlgCl identifier in the
private qbarPullIso_comp proof. The current derivedExtendScalarsToPadicAlgCl abbreviation
already unfolds directly to the canonical left derived scalar extension, so the removed
alias is unnecessary in its dsimp normalization list.

## Old

The live item file is absent. The authoritative module is
quarantine/Sheaf/Paper/CondensedQbarPullbackCube.lean, with its complete original interface.
The obsolete proof fragment is:

```lean
      derivedExtendScalarsToPadicAlgCl, finiteCoefficientDerivedToAlgCl,
```

## New

Restore the archived module at lean/Sheaf/Paper/CondensedQbarPullbackCube.lean.
The obsolete alias is removed from the normalization line:

```lean
      derivedExtendScalarsToPadicAlgCl,
```

The complete original proof exceeds 60 seconds in current compiles. Its signature
unfolds concrete derived coefficient comparisons during definitional equality. A local
CompositionCalculation section now marks constructibleToPadicAlgCl and
constructibleToQbarPullIso and boundedConstructibleUpperStarComp irreducible. The local backward conversion option respects
that transparency except when comparing types. The proof explicitly unfolds these
constructions before its existing projection normalization. The Omega bounded_comp_hom
rewrite infers the already-unfolded object, and final normalization explicitly includes
Over.Hom.left. No definitions or global reducibility attributes change. The final complete
file compiled without warnings in 58.3 seconds.

The changed proof-control lines are:

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
section CompositionCalculation
attribute [local irreducible] constructibleToPadicAlgCl constructibleToQbarPullIso
  boundedConstructibleUpperStarComp
```

The section ends immediately after qbarPullIso_comp. The proof explicitly uses:

```lean
  unfold constructibleToPadicAlgCl constructibleToQbarPullIso
```

and the second composition-component rewrite now infers its object:

```lean
    erw [bounded_comp_hom ℓ k (Profinite.padicAlgClRingObj ℓ) h j _]
```

Every declaration, public import, signature, definition, visibility and mathematical
hypothesis is retained. No source-library file changes. The DAG proof and dependencies
are retained; its proof_origin records this restoration.

## Users

The prescribed downstream query with --allow-missing --uses
constructibleToQbar_pullback_cube reports zero live importers. An import-graph scan of
both roots, overlaying live sources on quarantined sources, finds the four consumers
below. Only CondensedQbarExchangeLeftAdjunct directly imports and names the theorem.
The restored interface has exactly the archived statements, so none needs adaptation.
The DAG still requires the cube from lem-weil-pbc-qbar-condensed-exchange-left-adjunct.
No target statement or meaning, definition data, or unit route changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CondensedQbarPullbackCube | J7 | Restore complete cube and repair proof normalization. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed in shared snapshot | Quarantined direct consumer; identical interface, no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed in shared snapshot | Quarantined indirect consumer; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed in shared snapshot | Quarantined indirect consumer; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed in shared snapshot | Quarantined indirect consumer; no adaptation. |

## Status

landed 20261021T190432-L-3595078 2026-10-21 (merge of deliver/J7/Sheaf.Paper.CondensedQbarPullbackCube)
