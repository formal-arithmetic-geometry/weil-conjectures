# AlgebraicGeometry.Scheme.Modules.determinant_wedge_quotient_factor

## Reason

Retire the zero-hole Sheaf copy under coord/retire-items.tsv row 1047 and the human's
2026-10-20 hand-off in coord/changes/retire-sheaf-twins-20261020.md. Its official twin
is already fully proved, but uses exteriorPower and wedge. The canonical
exteriorSheafPowerIso comparison preserves pure wedges in both directions.
Each consumer now imports the official twin and the existing comparison module.
A fully proved private bridge conjugates the two supplied maps, verifies the
upstream hypotheses, and transports the factorization back. Generator
extensionality verifies the factorization equation without unfolding the tensor
isomorphisms. All existing consumer signatures, definitions and public imports
stay verbatim. No upstream source or target is changed.

The item is withdrawn through deleted.txt. Its node points at the official theorem
with its verbatim signature and official proof dependencies. Both parent nodes
retain the factorization step and record the comparison transport. The unit's
realized statement and steps are unchanged. Rank zero, either exterior degree zero,
empty schemes/opens and zero rings are covered by the same isomorphisms and theorem;
no additional hypothesis or arbitrary existence choice is introduced.

## Old

```lean
theorem determinant_wedge_quotient_factor {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ)
    (hr : r₂ = r₁ + r₃) [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (q : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₂ r₃ ⟶
      exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃)
    (ψ : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₂ r₃ ⟶ exteriorSheaf S.X₂ r₂)
    (hq : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (c : Fin r₃ → S.X₂.val.obj (op U)),
      q.val.app (op U)
        (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
          (exteriorSheafSection S.X₂ r₃ U c)) =
        tmulSection (M := exteriorSheaf S.X₁ r₁)
          (N := exteriorSheaf S.X₃ r₃) (U := U)
          (exteriorSheafSection S.X₁ r₁ U a)
          (exteriorSheafSection S.X₃ r₃ U (fun i ↦ S.g.val.app (op U) (c i))))
    (hψ : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (c : Fin r₃ → S.X₂.val.obj (op U)),
      ψ.val.app (op U)
        (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
          (exteriorSheafSection S.X₂ r₃ U c)) =
        exteriorSheafSection S.X₂ r₂ U
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))) :
    ∃ φ : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶ exteriorSheaf S.X₂ r₂,
      q ≫ φ = ψ
```

## New

Existing proved declaration in
WeilConjectures.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor:

```lean
theorem determinant_wedge_quotient_factor {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ)
    (hr : r₂ = r₁ + r₃) [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (q : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₂ r₃ ⟶
      exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃)
    (ψ : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₂ r₃ ⟶ exteriorPower S.X₂ r₂)
    (hq : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (c : Fin r₃ → S.X₂.val.obj (op U)),
      q.val.app (op U)
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₂) (r := r₃) (U := U) c)) =
        tmulSection (M := exteriorPower S.X₁ r₁)
          (N := exteriorPower S.X₃ r₃) (U := U)
          (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₃) (r := r₃) (U := U) (fun i ↦ S.g.val.app (op U) (c i))))
    (hψ : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (c : Fin r₃ → S.X₂.val.obj (op U)),
      ψ.val.app (op U)
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₂) (r := r₃) (U := U) c)) =
        wedge (M := S.X₂) (r := r₂) (U := U)
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))) :
    ∃ φ : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ ⟶ exteriorPower S.X₂ r₂,
      q ≫ φ = ψ
```

## Users

The downstream.py --uses scan finds nine downstream modules; only the two direct
consumers import the copy or call its theorem. Neither direct consumer is held by
another group at the time of the change. All other users see unchanged APIs.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Unchanged: direct consumer public API is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel | unclaimed | Adapted private proof import, added proved comparison helpers, and changed one call; public interface unchanged. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Unchanged: direct consumer public API is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Unchanged: direct consumer public API is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism | unclaimed | Unchanged: direct consumer public API is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismGlue | unclaimed | Unchanged: direct consumer public API is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocal | unclaimed | Unchanged: direct consumer public API is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt | unclaimed | Adapted private proof import, added proved comparison helpers, and changed one call; public interface unchanged. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Unchanged: direct consumer public API is preserved. |

## Status

landed 20261021T003458-L-1642022 2026-10-21 (merge of deliver/A5/Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor)
