# AlgebraicGeometry.Scheme.Modules.exteriorTensor_lift_hom_ext

## Reason

Retire `Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt` under the human's
2026-10-20 hand-off. The official twin uses `exteriorPower` and `wedge`; consumers
still state their results using the older `exteriorSheaf` construction.

## Old

```lean
theorem exteriorTensor_lift_hom_ext {X : Scheme.{v}} {A B C D : X.Modules}
    (g : B ⟶ C) [Epi g] (r s : ℕ)
    (φ ψ : exteriorSheaf A r ⊗ exteriorSheaf C s ⟶ D)
    (h : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → B.val.obj (op U)),
      φ.val.app (op U)
          (tmulSection (exteriorSheafSection A r U a)
            (exteriorSheafSection C s U (fun i ↦ g.val.app (op U) (c i)))) =
        ψ.val.app (op U)
          (tmulSection (exteriorSheafSection A r U a)
            (exteriorSheafSection C s U (fun i ↦ g.val.app (op U) (c i))))) :
    φ = ψ
```

The retired module exported `AlgebraicGeometry.Scheme.Modules.exteriorTensor_lift_hom_ext`
for `exteriorSheaf A r ⊗ exteriorSheaf C s`, with its generator condition expressed
using `exteriorSheafSection`. The rank-vanishing consumer also imported its private
`exterior_section_map` using `import all`.

## New

```lean
theorem exteriorTensor_lift_hom_ext {X : Scheme.{v}} {A B C D : X.Modules}
    (g : B ⟶ C) [Epi g] (r s : ℕ)
    (φ ψ : exteriorPower A r ⊗ exteriorPower C s ⟶ D)
    (h : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → B.val.obj (op U)),
      φ.val.app (op U)
          (tmulSection (wedge (M := A) (r := r) (U := U) a)
            (wedge (M := C) (r := s) (U := U) (fun i ↦ g.val.app (op U) (c i)))) =
        ψ.val.app (op U)
          (tmulSection (wedge (M := A) (r := r) (U := U) a)
            (wedge (M := C) (r := s) (U := U) (fun i ↦ g.val.app (op U) (c i))))) :
    φ = ψ
```

The official `WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt`
provides the same local-generation argument for `exteriorPower` and `wedge`.
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison` constructs the comparison
isomorphism from identity components on the presheaves of exterior powers. Uniqueness
of restriction maps proves naturality; adjunction-unit naturality proves the inverse
wedge formula. Tensoring these comparisons transfers the official extensionality
theorem, under the distinct name `exteriorSheafTensor_lift_hom_ext`, without repeating
its local-generation proof. Consumers retain their signatures and use this compatibility
API. The rank-vanishing proof uses a proved private helper for adjunction-unit naturality
instead of an imported private declaration. No upstream file or target statement changes. No proof is
replaced by sorry and no definition is hollowed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Import compatibility; transfer inverse uniqueness. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor | unclaimed | Import compatibility; transfer equality with the constructed quotient. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero | unclaimed | Remove private import; prove restriction formula in a local private helper. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelRelations | unclaimed | Import compatibility; transfer the degree-zero mono argument. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorTensorQuotient | unclaimed | Import compatibility; transfer epi cancellation. |

The item DAG node points to the twin with its exact statement. The compatibility has
its own node, `lem-sc-exterior-sheaf-power-comparison`; four consumer proof records
name it. The rank-vanishing node records the direct naturality argument. All five
consumer modules are compiled independently through lcompile.py in this packet.

## Status

landed 20261020T144259-L-2261123 2026-10-20 (merge of deliver/P7/Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt)
