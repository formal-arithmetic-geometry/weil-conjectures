# AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_exists

## Reason

Complete the retirement assigned by coord/retire-items.tsv:748 under the human hand-off
in coord/changes/retire-sheaf-twins-20261020.md. Both versions are already proved. The
adopted theorem uses canonical exteriorPower sheaves; its sole direct legacy consumer
uses exteriorSheaf. The existing canonical comparison isomorphisms transfer the full
local conclusion, including its arbitrary-lift formula and restriction compatibility.
No upstream file or target statement changes. There is no current rework row or W4
return for this item.

## Old

The duplicate Sheaf module supplied:

```lean
theorem determinant_split_comparison_exists {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b) :
    ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ (d : ∀ (W : X.Opens), W ≤ V →
        (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
          ≃ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W)),
      (∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
        (b : Fin r₃ → S.X₃.val.obj (op W)),
        d W hW (tmulSection (exteriorSheafSection S.X₁ r₁ W a)
          (exteriorSheafSection S.X₃ r₃ W b)) =
        exteriorSheafSection S.X₂ r₂ W
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
            (fun j ↦ l W (hW.trans hVU) (b j)) (Fin.cast hr i))) ∧
      (∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
        (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
          d Z (hZW.trans hW)
            ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
              (homOfLE hZW).op y))
```

## New

The retained DAG node attaches to the complete, unchanged adopted theorem in
WeilConjectures.AlgebraicGeometry.Modules.DeterminantSplitComparison:

```lean
theorem determinant_split_comparison_exists {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b) :
    ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ (d : ∀ (W : X.Opens), W ≤ V →
        (exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.obj (op W)
          ≃ₗ[X.presheaf.obj (op W)] (exteriorPower S.X₂ r₂).val.obj (op W)),
      (∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
        (b : Fin r₃ → S.X₃.val.obj (op W)),
        d W hW (tmulSection (wedge (M := S.X₁) (r := r₁) (U := W) a)
          (wedge (M := S.X₃) (r := r₃) (U := W) b)) =
        wedge (M := S.X₂) (r := r₂) (U := W)
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
            (fun j ↦ l W (hW.trans hVU) (b j)) (Fin.cast hr i))) ∧
      (∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
        (exteriorPower S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
          d Z (hZW.trans hW)
            ((exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.map
              (homOfLE hZW).op y))
```

Withdraw the duplicate module through deleted.txt. Its sole direct consumer,
Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit, imports the adopted
module and ExteriorSheafPowerComparison privately. Its public signature, public
imports, docstring and existing private helpers stay unchanged. The proved private
forward-wedge helper from the retired module moves to the consumer.

After applying the canonical local comparison, compose its forward linear map with
the evaluated outside tensor comparison and the inverse middle comparison. These are
bijections, so their composite is a bijection. Combine its LinearMap with
Equiv.ofBijective to obtain a linear equivalence with the same forward function.
The tensor section formula and the comparison's forward and inverse wedge equations
prove the legacy wedge formula. Naturality of the comparison morphisms transfers the
restriction equation. The remaining generation and sheaf-gluing argument is unchanged.

All ranks, including zero, and empty opens and zero section rings remain covered.
There is no new hypothesis or choice of data from an unproved existence theorem.
The mathematical node and the parent's edge to it remain. Only its Lean realization
changes, and the parent's proof dependencies now record the comparison isomorphism.
The unit sk-thm-picard-rr and its route are unchanged.

## Users

The downstream scan, declaration search and quarantine search find one direct
consumer and four transitive consumers. No direct consumer claim is present in the
shared claim records at preparation time.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison | W4 | Withdraw duplicate; keep node on adopted theorem. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit | unclaimed | Replace private import; transport canonical local comparison in proof; public signature unchanged. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Transitive consumer; no edit required. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Transitive consumer; no edit required. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Transitive consumer; no edit required. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Transitive consumer; no edit required. |

No quarantined module references the retired module or declaration. The historical
new-determinant-split-local node has no Lean attachment and remains realized by its
existing edge to the retained comparison node. No DAG node is deleted.

## Status

landed 20261021T002938-L-1582174 2026-10-21 (merge of deliver/W4/Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison)
