# AlgebraicGeometry.Scheme.Modules.exteriorSheaf_stalk_comparison

## Reason

Retire row 278 of coord/retire-items.tsv under the human's 2026-10-20 instruction
recorded in coord/changes/retire-sheaf-twins-20261020.md. The item has zero holes.
Its upstream twin is fully proved but uses exteriorPower and wedge instead of
exteriorSheaf and exteriorSheafSection. The two sectionwise exterior presheaves
have the same modules and restriction maps characterized by the same pure-wedge
formula. Their identity-on-sections isomorphism sheafifies to an isomorphism of
the two exterior sheaves. Naturality of the sheafification unit proves that it
sends exteriorSheafSection to wedge. Its linear stalk isomorphism transports the
upstream stalk comparison without changing any hypothesis or conclusion of the
consumer. All constructions apply to arbitrary schemes and module sheaves,
including degree zero, zero modules, and zero stalk rings.

The sole direct consumer, ExteriorTensorStalkKernelSpan, is unclaimed. Its private
retainedExteriorSheaf_stalk_comparison contains this transport. Its two existing
call sites use that private bridge, and its import uses the upstream twin. The
unused private proof import Topology.PresheafModuleStalkFunctor is removed.
Every existing public signature and definition of the consumer stays verbatim.
No upstream file, target, or public import of the consumer is changed.

## Old

In Sheaf.AlgebraicGeometry.Modules.ExteriorSheafStalkComparison:

```lean
theorem exteriorSheaf_stalk_comparison {X : Scheme.{v}} (M : X.Modules)
    (n : ℕ) (x : X) :
    ∃ e : (exteriorSheaf M n).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
        ⋀[X.presheaf.stalk x]^n (M.presheaf.stalk x),
      ∀ (U : X.Opens) (hx : x ∈ U) (a : Fin n → M.val.obj (op U)),
        e ((exteriorSheaf M n).presheaf.germ U x hx (exteriorSheafSection M n U a)) =
          exteriorPower.ιMulti (X.presheaf.stalk x) n
            (fun i ↦ M.presheaf.germ U x hx (a i))
```

## New

Use the existing, proved declaration in
WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafStalkComparison:

```lean
theorem exteriorSheaf_stalk_comparison {X : Scheme.{v}} (M : X.Modules)
    (n : ℕ) (x : X) :
    ∃ e : (exteriorPower M n).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
        ⋀[X.presheaf.stalk x]^n (M.presheaf.stalk x),
      ∀ (U : X.Opens) (hx : x ∈ U) (a : Fin n → M.val.obj (op U)),
        e ((exteriorPower M n).presheaf.germ U x hx (wedge (M := M) (r := n) (U := U) a)) =
          exteriorPower.ιMulti (X.presheaf.stalk x) n
            (fun i ↦ M.presheaf.germ U x hx (a i))
```

The Sheaf copy is withdrawn via deleted.txt. Its node points to the upstream
module and records the explicit comparison with the retained exteriorSheaf API.
The parent node records the same bridge. No node or mathematical step is deleted.

## Users

The downstream scan lists thirteen modules. Only ExteriorTensorStalkKernelSpan
directly imports the retired copy or calls its theorem. All other modules keep
the same public API through the adapted consumer. A source scan including
quarantined files found no additional imports or calls to the retired module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Unchanged: public signatures and definitions of its dependency are preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel | unclaimed | Unchanged: public signatures and definitions of its dependency are preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Unchanged: public signatures and definitions of its dependency are preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Unchanged: public signatures and definitions of its dependency are preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism | unclaimed | Unchanged: public signatures and definitions of its dependency are preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismGlue | unclaimed | Unchanged: public signatures and definitions of its dependency are preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocal | unclaimed | Unchanged: public signatures and definitions of its dependency are preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt | unclaimed | Unchanged: public signatures and definitions of its dependency are preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor | unclaimed | Unchanged: public signatures and definitions of its dependency are preserved. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelLocallySpanned | unclaimed | Unchanged: public signatures and definitions of its dependency are preserved. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelRelations | unclaimed | Unchanged: public signatures and definitions of its dependency are preserved. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorTensorStalkKernelSpan | unclaimed | Adapted: import upstream twin, add a proved private bridge, and change its two private call sites; public API unchanged. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Unchanged: public signatures and definitions of its dependency are preserved. |

## Status

landed 20261020T152948-L-2856050 2026-10-20 (merge of deliver/C3/Sheaf.AlgebraicGeometry.Modules.ExteriorSheafStalkComparison)
