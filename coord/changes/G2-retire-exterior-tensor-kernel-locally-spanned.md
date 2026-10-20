# AlgebraicGeometry.Scheme.Modules.exteriorTensor_kernel_locally_mem_span

## Reason

Retirement row 750, under the human-approved hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The assigned copy already has zero
holes. Its upstream twin is proved, with exteriorPower/wedge in place of
exteriorSheaf/exteriorSheafSection. Retire the copy and move its DAG attachment
to that twin. No upstream module or target statement is changed.

The sole direct consumer ExteriorTensorKernelRelations is unclaimed. Preserve
its public signature and public imports verbatim. Replace the proof import by
the upstream twin. Tensor the existing canonical exteriorSheafPowerIso in both
factors; its inverse pure-wedge formula follows from tensorHom_app_tmulSection
and exteriorSheafPowerIso_inv_wedge. Inverse cancellation gives the forward
formula. Conjugate q and use the upstream local span theorem on the transported
kernel section. The inverse comparison sends each relation generator to an
original generator. Submodule.span_le extends its vanishing under ψ to the
whole span; naturality and inverse cancellation recover the original vanishing.
The original sheaf section_ext argument then finishes. The only new helper is
private and completely proved; no new data or unproved witness is chosen.

This works for r=0, zero modules, zero section rings and the empty scheme. The
s=0 branch remains unchanged. No finiteness, freeness or rank hypothesis is
added. The unit route and mathematical statement are unchanged: the comparison
identifies the two constructions of the same exterior sheaf.

## Old

In Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelLocallySpanned:

```lean
theorem exteriorTensor_kernel_locally_mem_span {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (A : X.Modules) (r s : ℕ) (hs : s ≠ 0)
    (q : exteriorSheaf A r ⊗ exteriorSheaf S.X₂ s ⟶
      exteriorSheaf A r ⊗ exteriorSheaf S.X₃ s)
    (hq : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → S.X₂.val.obj (op U)),
      q.val.app (op U)
        (tmulSection (exteriorSheafSection A r U a)
          (exteriorSheafSection S.X₂ s U c)) =
        tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf S.X₃ s)
          (exteriorSheafSection A r U a)
          (exteriorSheafSection S.X₃ s U (fun i ↦ S.g.val.app (op U) (c i))))
    (U : X.Opens)
    (t : (exteriorSheaf A r ⊗ exteriorSheaf S.X₂ s).val.obj (op U))
    (ht : q.val.app (op U) t = 0) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      (exteriorSheaf A r ⊗ exteriorSheaf S.X₂ s).val.map (homOfLE hVU).op t ∈
        Submodule.span (X.presheaf.obj (op V))
          {z | ∃ (a : Fin r → A.val.obj (op V))
            (c : Fin s → S.X₂.val.obj (op V)) (j : Fin s)
            (d : S.X₁.val.obj (op V)), c j = S.f.val.app (op V) d ∧
              z = tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf S.X₂ s)
                (exteriorSheafSection A r V a)
                (exteriorSheafSection S.X₂ s V c)}
```

## New

In WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorKernelLocallySpanned:

```lean
theorem exteriorTensor_kernel_locally_mem_span {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (A : X.Modules) (r s : ℕ) (hs : s ≠ 0)
    (q : exteriorPower A r ⊗ exteriorPower S.X₂ s ⟶
      exteriorPower A r ⊗ exteriorPower S.X₃ s)
    (hq : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → S.X₂.val.obj (op U)),
      q.val.app (op U)
        (tmulSection (wedge (M := A) (r := r) (U := U) a)
          (wedge (M := S.X₂) (r := s) (U := U) c)) =
        tmulSection (M := exteriorPower A r) (N := exteriorPower S.X₃ s)
          (wedge (M := A) (r := r) (U := U) a)
          (wedge (M := S.X₃) (r := s) (U := U) (fun i ↦ S.g.val.app (op U) (c i))))
    (U : X.Opens)
    (t : (exteriorPower A r ⊗ exteriorPower S.X₂ s).val.obj (op U))
    (ht : q.val.app (op U) t = 0) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      (exteriorPower A r ⊗ exteriorPower S.X₂ s).val.map (homOfLE hVU).op t ∈
        Submodule.span (X.presheaf.obj (op V))
          {z | ∃ (a : Fin r → A.val.obj (op V))
            (c : Fin s → S.X₂.val.obj (op V)) (j : Fin s)
            (d : S.X₁.val.obj (op V)), c j = S.f.val.app (op V) d ∧
              z = tmulSection (M := exteriorPower A r) (N := exteriorPower S.X₂ s)
                (wedge (M := A) (r := r) (U := V) a)
                (wedge (M := S.X₂) (r := s) (U := V) c)}
```

The copy is withdrawn through deleted.txt; the node now points to the official
declaration with this exact signature. The parent node records the transport.

## Users

The downstream scan found eleven modules. Source scans of lean/Sheaf,
lean/WeilConjectures and quarantine found exactly one direct importer and one
call site outside the retired module, both in ExteriorTensorKernelRelations.
All ten indirect consumers keep the identical public interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Unchanged: the direct consumer retains its public interface. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel | unclaimed | Unchanged: the direct consumer retains its public interface. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Unchanged: the direct consumer retains its public interface. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Unchanged: the direct consumer retains its public interface. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism | unclaimed | Unchanged: the direct consumer retains its public interface. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismGlue | unclaimed | Unchanged: the direct consumer retains its public interface. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocal | unclaimed | Unchanged: the direct consumer retains its public interface. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt | unclaimed | Unchanged: the direct consumer retains its public interface. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor | unclaimed | Unchanged: the direct consumer retains its public interface. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelRelations | unclaimed | Adapted proof import and positive-degree proof; public signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Unchanged: the direct consumer retains its public interface. |

The adapted consumer compiled in 2.9 seconds; an import-order verification also
compiled it in 3.1 seconds and its unchanged immediate downstream consumer
DeterminantWedgeQuotientFactor in 2.1 seconds.

## Status

landed 20261020T221153-L-4152589 2026-10-20 (merge of deliver/G2/Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelLocallySpanned)
