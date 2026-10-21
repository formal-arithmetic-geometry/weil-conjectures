# AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_local_data_at

## Reason

Retire the duplicate listed in coord/retire-items.tsv, row 1206, under the human's
hand-off in coord/changes/retire-sheaf-twins-20261020.md. The item has zero holes.
Its official twin is proved but uses exteriorPower and wedge. The sole direct
consumer, DeterminantWedgeMorphismLocal, now imports the twin privately and the
existing ExteriorSheafPowerComparison module. It precomposes the official map
with the tensor of the two comparison hom maps and postcomposes with the target
comparison inverse. A proved private helper derives the hom wedge formula from
the inverse wedge formula and the isomorphism identity. Tensor-section naturality,
the official formula and the inverse wedge formula prove the original conclusion.
All existing consumer signatures, visibility, definitions and public imports stay
verbatim. No upstream source file or target statement changes.

The item is withdrawn through deleted.txt; its node points at the official
statement verbatim and records the official proof. The consumer node now records
the actual transport proof, preserving the same determinant-unit argument. No
parent node has a current dependency on new-local-wedge-at; the consumer node is
updated to name its actual use. Occurrences in blueprint.from provenance do not
require an obsolete Lean module. The unit's realized statement and steps stay
unchanged. The comparison exists in every degree, including zero, so empty tuples,
rank zero, empty opens/schemes and zero rings need no extra hypothesis or choice.

## Old

```lean
theorem determinant_wedgeMorphism_local_data_at {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] (U : X.Opens) :
    ∃ φU : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶
      exteriorSheaf S.X₂ r₂,
      ∀ (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φU.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))
```

## New

The duplicate declaration is removed. Its existing official replacement is:

```lean
theorem determinant_wedgeMorphism_local_data_at {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] (U : X.Opens) :
    ∃ φU : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ ⟶
      exteriorPower S.X₂ r₂,
      ∀ (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φU.val.app (op U)
          (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
            (wedge (M := S.X₃) (r := r₃) (U := U) b)) =
          wedge (M := S.X₂) (r := r₂) (U := U)
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))
```

The consumer retains its existing exteriorSheaf statement, proved by the explicit
isomorphism transport above; the two representations have the same wedge formula.

## Users

The downstream.py --uses scan lists six downstream modules. Only the local-data
consumer imports the withdrawn module or invokes its theorem. A source scan of
lean/ and quarantine/ found no other imports of the withdrawn copy.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Unchanged; consumer API preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Unchanged; consumer API preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Unchanged; consumer API preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism | unclaimed | Unchanged; consumer API preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocal | unclaimed | Private imports migrated, proved private helper added, local-data proof transported; existing public signatures and imports unchanged. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Unchanged; consumer API preserved. |

## Status

landed 20261021T011045-L-2034162 2026-10-21 (merge of deliver/V4/Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt)
