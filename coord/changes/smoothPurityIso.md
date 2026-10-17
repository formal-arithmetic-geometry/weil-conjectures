# AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso

## Reason

Report a false elaborated statement without changing its type. The section smoothness
instance is unused by the original result type and sorry body, so Lean drops it. The
identity on Spec(F_3), ell = 2, d = 1 contradicts the resulting claim: the left side has
nonzero H^0 and the shifted-single right side has zero H^0. No Tate-line property is needed.

## Old

```lean
@[no_expose]
noncomputable def smoothPurityIso :
    ((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))).obj ≅
      (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d) :=
  sorry
```

The elaborated declaration has no SmoothOfRelativeDimension argument.

## New

```lean
@[no_expose]
noncomputable def smoothPurityIso :
    ((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))).obj ≅
      (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d) :=
  sorry
```

Identical declaration, with a STATEMENT-DISPUTED comment immediately before its docstring.
No change to its elaborated signature, body, attributes, visibility or imports. The report
requests authorization to retain the missing smoothness binder before attempting its proof.

## Users

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.SmoothPurity.Defs | G1 | Existing false elaborated type marked disputed. |
| WeilConjectures.PoincareDuality.Poincare | B3 | Unchanged; correcting the dropped binder would affect its inferred signatures and two omit commands. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Unchanged. |

Challenge.lean and all existing declarations remain unchanged. The failed reconstructed
proof is retained in scratch and is not part of this delivery. No forced adaptation is made.

## Status

landed 20261017T133353-L-2578124 2026-10-17 (merge of deliver/G1/WeilConjectures.SmoothPurity.Defs)
