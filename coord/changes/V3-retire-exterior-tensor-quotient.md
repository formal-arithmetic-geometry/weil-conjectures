# AlgebraicGeometry.Scheme.Modules.exteriorTensor_quotient_exists

## Reason

The item is a retirement row of coord/retire-items.tsv, governed by the human's
2026-10-20 hand-off in coord/changes/retire-sheaf-twins-20261020.md. Both twins are
already proved. The older theorem uses exteriorSheaf/exteriorSheafSection whereas
the official theorem uses exteriorPower/wedge. Simply changing the imports would
therefore change the objects of the two direct consumers, whose public signatures
must stay identical. The existing canonical exteriorSheafPowerIso comparison
identifies the constructions without asserting definitional equality.

## Old

The retired Sheaf module declared:

```lean
theorem exteriorTensor_quotient_exists {X : Scheme.{v}} (A B C : X.Modules)
    (g : B ⟶ C) [Epi g] (r s : ℕ) :
    ∃ q : exteriorSheaf A r ⊗ exteriorSheaf B s ⟶
        exteriorSheaf A r ⊗ exteriorSheaf C s,
      Epi q ∧ ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
        (c : Fin s → B.val.obj (op U)),
        q.val.app (op U)
            (tmulSection (exteriorSheafSection A r U a) (exteriorSheafSection B s U c)) =
          tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf C s)
            (exteriorSheafSection A r U a)
            (exteriorSheafSection C s U (fun i ↦ g.val.app (op U) (c i)))
```

Both direct consumers privately imported the retired module and applied this name.

## New

The existing node now points to the official, unchanged declaration:

```lean
theorem exteriorTensor_quotient_exists {X : Scheme.{v}} (A B C : X.Modules)
    (g : B ⟶ C) [Epi g] (r s : ℕ) :
    ∃ q : exteriorPower A r ⊗ exteriorPower B s ⟶
        exteriorPower A r ⊗ exteriorPower C s,
      Epi q ∧ ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
        (c : Fin s → B.val.obj (op U)),
        q.val.app (op U)
            (tmulSection (wedge (M := A) (r := r) (U := U) a)
              (wedge (M := B) (r := s) (U := U) c)) =
          tmulSection (M := exteriorPower A r) (N := exteriorPower C s)
            (wedge (M := A) (r := r) (U := U) a)
            (wedge (M := C) (r := s) (U := U) (fun i ↦ g.val.app (op U) (c i)))
```

The old module is withdrawn through deleted.txt. New module
Sheaf.AlgebraicGeometry.Modules.ExteriorSheafTensorQuotientComparison proves
exteriorSheafTensor_quotient_exists by conjugating the official epimorphism with
tensors of exteriorSheafPowerIso. Its only private helper computes the inverse
comparison on tensors of wedges using the existing inverse wedge formula.
The cancellation equality of the conjugate, evaluated on an official wedge tensor,
proves the required section formula. Epimorphy follows from composition with
isomorphisms. Every proof is complete; no definitions, upstream files, or targets
are changed. Both consumers replace one private import and one theorem call only.
The consumer proof records now point to the compatibility result. No rank,
nonemptiness, or nonzero-ring hypothesis has been introduced.

## Users

The downstream.py --uses check lists the ten modules below; only two directly
import or use the old theorem. Both were unclaimed when prepared (no current
claim file names either module). All other users keep their source verbatim and
consume unchanged public signatures. The three immediate downstream consumers
DeterminantLiftWedgeKernel, DeterminantWedgeMorphismLocalAt, and
DeterminantWedgeMorphismLocal were additionally compiled unchanged against the
sandbox overlay; all passed without warnings.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismGlue | unclaimed | Replace private import and call by the proved compatibility theorem; signature unchanged. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor | unclaimed | Replace private import and call by the proved compatibility theorem; signature unchanged. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel | unclaimed | No source or signature change. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt | unclaimed | No source or signature change. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocal | unclaimed | No source or signature change. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism | unclaimed | No source or signature change. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | No source or signature change. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | No source or signature change. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | No source or signature change. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | No source or signature change. |

## Status

landed 20261020T154054-L-3043145 2026-10-20 (merge of deliver/V3/Sheaf.AlgebraicGeometry.Modules.ExteriorTensorQuotient)
