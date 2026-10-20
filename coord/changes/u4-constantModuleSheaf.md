# AlgebraicGeometry.Etale.constantModuleSheaf

## Reason

Expose the existing tensor-unit presentation of the constant rank-one module as an abbreviation. The monoidal unit of this fixed-coefficient sheaf category is definitionally the same constant sheaf of ModuleCat.of A A. This lets the proof use monoidal unit axioms without repeatedly comparing constant-sheaf construction terms. No target signature changes. Definitions used by targets retain the same mathematical meaning; their canonical constructions can be read directly in the new helper bodies. The semantic review should verify these definitional identities.

## Old

```lean
noncomputable def constantModuleSheaf (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)
```

## New

```lean
noncomputable abbrev constantModuleSheaf (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor | U4 | Same object or arrow, with its canonical generic API; proof adapted here. |

`tools/downstream.py --uses constantModuleSheaf` finds no other direct user. The three transitive consumers are Sheaf.Paper.SupportedCup, Sheaf.Paper.PurityFrameClass and Sheaf.Paper.PurityFramePrincipalBoundary. Their original statements and proofs require no edits; they compile unchanged against the delivered definitions (SupportedCup 17.6 s, PurityFramePrincipalBoundary 23.7 s, PurityFrameClass 13.9 s). No source-library declaration is changed.

## Status

landed 20261020T233227-L-908718 2026-10-20 (merge of deliver/U4/Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor)
