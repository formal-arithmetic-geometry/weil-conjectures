# AlgebraicGeometry.ProEtale.CondensedRing.isIso_properProjection_bounded

## Reason

Prove the current restored module
`Sheaf.PoincareDuality.ProperProjectionFormulaBounded`, assigned to C2.
The existing proper projection clauses already concern internal module objects.
Coefficient isomorphisms, their projection square, and the integral constructibility
comparison give the required proof without a ringed-topos equivalence.

## Old

```lean
theorem isIso_properProjection_bounded (f : X ⟶ Y) (c : Compactification f.left)
    (K : Dᵇc(X.left)⟦Λ⟧) (B : Dᵇc(Y.left)⟦Λ⟧) :
    IsIso ((derivedUpperStarLowerStarAdjunction Λ c.g).projectionMorphism
      ((D((c.i)_!open⟦Λ⟧)).obj K.obj) B.obj) := by
  sorry
```

The original public imports, universe and variable context are retained. The original
proof context registered seven named local `projection*` caches, whose names are no
longer available through the recorded imports.

## New

```lean
theorem isIso_properProjection_bounded (f : X ⟶ Y) (c : Compactification f.left)
    (K : Dᵇc(X.left)⟦Λ⟧) (B : Dᵇc(Y.left)⟦Λ⟧) :
    IsIso ((derivedUpperStarLowerStarAdjunction Λ c.g).projectionMorphism
      ((D((c.i)_!open⟦Λ⟧)).obj K.obj) B.obj)
```

The proof uses the existing rational and integral projection clauses, with explicit
coefficient realization and transport. The local cache registrations are replaced by
canonical instances. Local irreducibility boundaries prevent elaboration from expanding
the chosen localization and graded tensor data. The coefficient-square helper alone
uses two scoped backward unification options; ordinary kernel checking remains enabled.
All additional mathematical helpers are proved. In this module no existing public definition, instance, signature or public import changes. The separate compact projection-map definition repair is recorded
in `C2-module-object-projection-record.md`. No source-library file is edited.

The node changes only its proof, proof dependencies and proof origin. Its Lean attachment,
statement, unit and parent dependencies are preserved. The removed proof import
`Sheaf.Paper.ModuleRingedToposDerivedComparison` remains available to all other consumers.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | C2 | current source retained; proof completed |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | unclaimed | the preserved application `isIso_properProjection_bounded Λ ℓ f c K B` has the same signature; no edit required |

The current live parent imports and applies this item. Its preserved application,
DAG dependency, and unit `sk-thm-sf-verdier-exchange` still need the item. No withdrawal
or forced consumer adaptation is made.

The 2026-10-22 return identified a source creation after the earlier delivery base.
The retained proof has been reapplied to the current file, preserving its exact theorem
signature and original docstring. The new delivery is generated against the current base.

## Status

landed 20261022T040148-L-2814682 2026-10-22 (merge of deliver/C2/Sheaf.PoincareDuality.ProperProjectionFormulaBounded)
