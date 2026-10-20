# AlgebraicGeometry.Scheme.Modules.determinant_split_linear_maps_exists

## Reason

Complete the retirement listed in coord/retire-items.tsv, under the human hand-off in
coord/changes/retire-sheaf-twins-20261020.md. Both implementations already have complete
proofs, but their exterior-power APIs differ. Retain the upstream theorem and retire the
619-line duplicate rather than continuing to compile two declarations with the same name.
The repository has no rework row or current C8 return for this item.

## Old

The withdrawn Sheaf module provided:

```lean
theorem determinant_split_linear_maps_exists {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b) :
    ∃! (d : ∀ (W : X.Opens), W ≤ U →
      (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W)),
      (∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
        (b : Fin r₃ → S.X₃.val.obj (op W)),
        d W hW (tmulSection (exteriorSheafSection S.X₁ r₁ W a)
          (exteriorSheafSection S.X₃ r₃ W b)) =
        exteriorSheafSection S.X₂ r₂ W
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
            (fun j ↦ l W hW (b j)) (Fin.cast hr i))) ∧
      (∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) y,
        (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
          d Z (hZW.trans hW)
            ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
              (homOfLE hZW).op y))
```

## New

The node now points to the existing theorem in
WeilConjectures.AlgebraicGeometry.Modules.DeterminantSplitLinearMaps:

```lean
theorem determinant_split_linear_maps_exists {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b) :
    ∃! (d : ∀ (W : X.Opens), W ≤ U →
      (exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorPower S.X₂ r₂).val.obj (op W)),
      (∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
        (b : Fin r₃ → S.X₃.val.obj (op W)),
        d W hW (tmulSection (wedge (M := S.X₁) (r := r₁) (U := W) a)
          (wedge (M := S.X₃) (r := r₃) (U := W) b)) =
        wedge (M := S.X₂) (r := r₂) (U := W)
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
            (fun j ↦ l W hW (b j)) (Fin.cast hr i))) ∧
      (∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) y,
        (exteriorPower S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
          d Z (hZW.trans hW)
            ((exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.map
              (homOfLE hZW).op y))
```

No upstream file is edited. The sole direct consumer,
Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison, retains its public signature
and its docstring verbatim. It imports the upstream theorem and the existing
ExteriorSheafPowerComparison API. It transports the section maps by the tensor of source
comparison homs and the target comparison inverse. A proved private helper derives forward
wedge compatibility from the inverse compatibility and inv_hom_id. Tensor naturality
proves the same arbitrary-lift formula, and morphism naturality proves restriction
compatibility. The existing local-bijectivity theorem applies to these same transported
maps. Their LinearMap structures and Equiv.ofBijective supply the equivalences, with
identical forward functions; this explicit construction avoids ring-hom inverse inference
at LinearEquiv.ofBijective after the changed import environment.

This is transport through a constructed canonical isomorphism, in every degree, including
zero. It adds no positivity, nonempty-open or nonzero-ring hypotheses. The unit route is
unchanged. The old module is listed in deleted.txt; DAG nodes are retained.

## Users

The downstream scan and direct declaration search find these modules. No other group
holds the direct consumer at preparation time.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison | unclaimed | Adapt private imports and proof only; signature unchanged. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit | unclaimed | Transitive consumer; no edit required. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Transitive consumer; no edit required. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Transitive consumer; no edit required. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Transitive consumer; no edit required. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Transitive consumer; no edit required. |

The adapted consumer and the direct importer are compiled against the delivered overlay.
The delivery probe checks the axioms. No target statement or public definition changes.

## Status

landed 20261020T211648-L-3485841 2026-10-20 (merge of deliver/C8/Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearMaps)
