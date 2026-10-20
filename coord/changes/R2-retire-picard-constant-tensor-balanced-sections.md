# AlgebraicGeometry.Scheme.Modules.exists_picard_constant_tensor_balanced_sections

## Reason

Complete the retirement assigned in `coord/retire-items.tsv`. The adopted source already
constructs the same balanced additive equivalences, with the scalar-action and restriction
laws required by the Sheaf existential theorem. Use that API directly in the sole consumer
and retire the duplicate theorem and its module. The upstream construction is an explicit
composition of linear/additive equivalences; no data is chosen from mere existence.
No adopted-source file, target, mathematical statement, or definition is changed.

## Old

```lean
theorem exists_picard_constant_tensor_balanced_sections
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) (G : Y.Modules) :
    ∃ e : ∀ V : Y.Opens,
        (picardConstantSectionsTensor k Y g M G).obj (op V) ≃+
          (M ⊗[k] scalarObj g G (op V)),
      (∀ (V : Y.Opens) (a : Γ(Y, V)) (s : M) (t : scalarObj g G (op V)),
        e V (a • (e V).symm (s ⊗ₜ[k] t)) =
          s ⊗ₜ[k] (show scalarObj g G (op V) from a • (show G.val.obj (op V) from t))) ∧
      (∀ {U V : Y.Opensᵒᵖ} (i : U ⟶ V)
          (x : (picardConstantSectionsTensor k Y g M G).obj U),
        e V.unop ((picardConstantSectionsTensor k Y g M G).map i x) =
          ((scalarPresheaf g G ⋙ MonoidalCategory.tensorLeft M).map i) (e U.unop x))
```

This already proved existential theorem is withdrawn with its duplicate Sheaf module.

## New

The existing declarations in
`WeilConjectures.AlgebraicGeometry.PicardConstantTensorBalancedSections` supply the
same family of additive equivalences and exactly its two laws:

```lean
noncomputable def picardConstantTensorBalancedSections
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) (G : Y.Modules)
    (V : Y.Opens) :
    (picardConstantSectionsTensor k Y g M G).obj (op V) ≃+ (M ⊗[k] scalarObj g G (op V))

theorem picardConstantTensorBalancedSections_smul
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) (G : Y.Modules)
    (V : Y.Opens) (a : Γ(Y, V)) (s : M) (t : scalarObj g G (op V)) :
    picardConstantTensorBalancedSections k Y g M G V
        (a • (picardConstantTensorBalancedSections k Y g M G V).symm (s ⊗ₜ[k] t)) =
      s ⊗ₜ[k] (show scalarObj g G (op V) from a • (show G.val.obj (op V) from t))

theorem picardConstantTensorBalancedSections_map
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) (G : Y.Modules)
    {U V : Y.Opensᵒᵖ} (i : U ⟶ V)
    (x : (picardConstantSectionsTensor k Y g M G).obj U) :
    picardConstantTensorBalancedSections k Y g M G V.unop
        ((picardConstantSectionsTensor k Y g M G).map i x) =
      ((scalarPresheaf g G ⋙ MonoidalCategory.tensorLeft M).map i)
        (picardConstantTensorBalancedSections k Y g M G U.unop x)
```

`ExternalConstantSectionsTensorMap` replaces its private import with this upstream module,
binds `e` to the construction, and binds `he` and `hn` to the two laws. The rest of its
proof is unchanged, including the construction of the presheaf morphism, its linearity,
naturality, and componentwise bijectivity equivalence. Its signature and public imports
are identical. The retired node is reattached to the three upstream declarations; its
mathematical statement and dependency on scalar-extension sections remain unchanged.
The parent's proof text records the direct use of these declarations and retains its
balanced-sections dependency. The unit's realized statement and steps are untouched.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardConstantTensorBalancedSections | R2 | Retired duplicate; zero original holes. |
| Sheaf.AlgebraicGeometry.ExternalConstantSectionsTensorMap | unclaimed | Private import replaced and three proof bindings use the upstream construction and laws; public interface unchanged. Compiled successfully. |

`tools/downstream.py` lists only the consumer above. Its `--uses` search finds that
consumer and the retired declaration itself. Searches of `lean/`, `quarantine/`,
`dag/nodes/`, and `dag/units/` find no additional mathematical consumer or importer.
The only DAG parent is `lem-sc-external-constant-sections-tensor-map`; it still uses
the same node through the reattached declarations. The scalar-extension node also
mentions this node as historical provenance, not as a dependency. Neither this node
nor its module realizes a unit statement or proof step.

Validation: the adapted consumer compiles with `lcompile.py` in 10.3 seconds.
The delivery preflight checks all delivered declarations and their axioms.

## Status

landed 20261020T162322-L-3589734 2026-10-20 (merge of deliver/R2/Sheaf.AlgebraicGeometry.PicardConstantTensorBalancedSections)
