# AlgebraicGeometry.Scheme.Modules.exteriorTensor_kernel_eq_zero_of_relations

## Reason

Retirement row 920 and the human hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The copy and official twin are already
proved, with zero holes. The official theorem uses exteriorPower/wedge; the copy
uses exteriorSheaf/exteriorSheafSection. Withdraw the duplicate and repoint its DAG
attachment to the official theorem. No upstream source or target is changed.

The only direct consumer is DeterminantWedgeQuotientFactor, currently unclaimed.
Its public signature, attributes and public imports are unchanged. A proved private
comparison lemma is moved from the withdrawn module into that consumer. The proof
tensors exteriorSheafPowerIso, conjugates q, precomposes ψ with the inverse source
comparison, and checks both generator hypotheses. The official theorem kills the
transported kernel. Lift kernel.ι q ≫ eB.hom into that kernel and precompose the
vanishing; inverse cancellation gives the original kernel vanishing. The existing
epimorphism descent finishes. All new proof work is complete.

The comparison preserves all degrees, including zero, and needs no freeness or
rank beyond the existing consumer hypotheses. Empty schemes and zero rings are
unchanged. The mathematical statement and the unit route are preserved.

## Old

In Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelRelations:

```lean
theorem exteriorTensor_kernel_eq_zero_of_relations {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (A D : X.Modules) (r s : ℕ)
    (q : exteriorSheaf A r ⊗ exteriorSheaf S.X₂ s ⟶
      exteriorSheaf A r ⊗ exteriorSheaf S.X₃ s)
    (ψ : exteriorSheaf A r ⊗ exteriorSheaf S.X₂ s ⟶ D)
    (hq : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → S.X₂.val.obj (op U)),
      q.val.app (op U)
        (tmulSection (exteriorSheafSection A r U a)
          (exteriorSheafSection S.X₂ s U c)) =
        tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf S.X₃ s)
          (exteriorSheafSection A r U a)
          (exteriorSheafSection S.X₃ s U (fun i ↦ S.g.val.app (op U) (c i))))
    (hzero : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → S.X₂.val.obj (op U)) (j : Fin s) (d : S.X₁.val.obj (op U)),
      c j = S.f.val.app (op U) d →
      ψ.val.app (op U)
        (tmulSection (exteriorSheafSection A r U a)
          (exteriorSheafSection S.X₂ s U c)) = 0) :
    kernel.ι q ≫ ψ = 0
```

## New

In WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorKernelRelations:

```lean
theorem exteriorTensor_kernel_eq_zero_of_relations {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (A D : X.Modules) (r s : ℕ)
    (q : exteriorPower A r ⊗ exteriorPower S.X₂ s ⟶
      exteriorPower A r ⊗ exteriorPower S.X₃ s)
    (ψ : exteriorPower A r ⊗ exteriorPower S.X₂ s ⟶ D)
    (hq : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → S.X₂.val.obj (op U)),
      q.val.app (op U)
        (tmulSection (wedge (M := A) (r := r) (U := U) a)
          (wedge (M := S.X₂) (r := s) (U := U) c)) =
        tmulSection (M := exteriorPower A r) (N := exteriorPower S.X₃ s)
          (wedge (M := A) (r := r) (U := U) a)
          (wedge (M := S.X₃) (r := s) (U := U) (fun i ↦ S.g.val.app (op U) (c i))))
    (hzero : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → S.X₂.val.obj (op U)) (j : Fin s) (d : S.X₁.val.obj (op U)),
      c j = S.f.val.app (op U) d →
      ψ.val.app (op U)
        (tmulSection (wedge (M := A) (r := r) (U := U) a)
          (wedge (M := S.X₂) (r := s) (U := U) c)) = 0) :
    kernel.ι q ≫ ψ = 0
```

The copy is withdrawn through deleted.txt. The existing declaration above is the
node's new attachment, not a new statement or a replacement axiom.

## Users

The downstream scan found ten modules; source scans of both Lean roots and
quarantine found exactly one direct importer/call site, in the adapted consumer.
No module in this table currently has a claim. All indirect users retain exactly
the same public interface. DAG parents keep the same node dependency, now attached
to the official theorem; the direct consumer node records the transport explicitly.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Unchanged; direct consumer public interface is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel | unclaimed | Unchanged; direct consumer public interface is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Unchanged; direct consumer public interface is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Unchanged; direct consumer public interface is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism | unclaimed | Unchanged; direct consumer public interface is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismGlue | unclaimed | Unchanged; direct consumer public interface is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocal | unclaimed | Unchanged; direct consumer public interface is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt | unclaimed | Unchanged; direct consumer public interface is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor | unclaimed | Proof import and kernel-vanishing proof adapted; public interface unchanged. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Unchanged; direct consumer public interface is preserved. |

The adapted consumer, withdrawn empty stub, and its two unchanged immediate
consumers DeterminantLiftWedgeKernel and DeterminantWedgeMorphismLocalAt compiled
together in import order, with no errors or warnings. Their individual times were
10.7, 0.3, 22.4 and 23.5 seconds. The consumer signature and public imports are
byte-identical to the originals. Temporary validation copies are not delivered.

## Status

landed 20261020T233124-L-896660 2026-10-20 (merge of deliver/E5/Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelRelations)
