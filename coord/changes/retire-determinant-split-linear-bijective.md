# AlgebraicGeometry.Scheme.Modules.determinant_split_linear_maps_locally_bijective

## Reason

Retire the duplicate Sheaf module assigned by coord/retire-items.tsv:529 and the
current stage-3 queue. The adopted source-library theorem is already proved, with
identical hypotheses and local bijectivity conclusion, using the canonical
exteriorPower and wedge interface. The existing exteriorSheafPowerIso and its
inverse wedge formula transport the sole direct consumer without changing its
statement. No adopted source-library file changes.

## Old

In Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective:

```lean
theorem determinant_split_linear_maps_locally_bijective {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b)
    (d : ∀ (W : X.Opens), W ≤ U →
      (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W))
    (hd : ∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
        (b : Fin r₃ → S.X₃.val.obj (op W)),
        d W hW (tmulSection (exteriorSheafSection S.X₁ r₁ W a)
          (exteriorSheafSection S.X₃ r₃ W b)) =
        exteriorSheafSection S.X₂ r₂ W
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
            (fun j ↦ l W hW (b j)) (Fin.cast hr i))) :
    ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∀ (W : X.Opens) (hW : W ≤ V), Function.Bijective (d W (hW.trans hVU))
```

## New

The duplicate module is withdrawn through deleted.txt. Its retained DAG node attaches
to the already proved declaration in
WeilConjectures.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective:

```lean
theorem determinant_split_linear_maps_locally_bijective {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b)
    (d : ∀ (W : X.Opens), W ≤ U →
      (exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorPower S.X₂ r₂).val.obj (op W))
    (hd : ∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
        (b : Fin r₃ → S.X₃.val.obj (op W)),
        d W hW (tmulSection (wedge (M := S.X₁) (r := r₁) (U := W) a)
          (wedge (M := S.X₃) (r := r₃) (U := W) b)) =
        wedge (M := S.X₂) (r := r₂) (U := W)
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
            (fun j ↦ l W hW (b j)) (Fin.cast hr i))) :
    ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∀ (W : X.Opens) (hW : W ≤ V), Function.Bijective (d W (hW.trans hVU))
```

The sole direct consumer is rebased on C8 landing 4453be244d6. Its private
bijectivity import switches to the adopted upstream theorem. C8's canonical
linear-family construction, wedge transport, restriction proof, public signature,
imports and docstring remain. Apply upstream bijectivity to the canonical family
d', then compose with the evaluated outside tensor comparison a and inverse
middle comparison b to prove bijectivity of the transported family d0. The
existing conversion to equivalences and final formulas remain unchanged.
A proof-local transparency option permits the comparison coercions to reduce.

All comparisons are genuine isomorphisms, require no positivity or nonzero-ring
assumption, and include rank zero and empty opens. No data are chosen from an
unproved existence result. No definition or target statement changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective | C7 | Withdraw duplicate, preserving the mathematical node with its upstream realization. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison | unclaimed | Sole direct importer and theorem user; private import replacement and bijectivity composition in its proof, with unchanged signature. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit | unclaimed | Next importer; no source edit; compile against the adapted consumer. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Transitive importer; unchanged public consumer theorem. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Transitive importer; unchanged public consumer theorem. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Transitive importer; unchanged public consumer theorem. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Transitive importer; unchanged public consumer theorem. |

These are all downstream library modules. The only DAG parent is
lem-sc-determinant-split-comparison; its proof and dependency list now record the
comparison isomorphism used for transport. The original node and every parent's
edge to it remain: the mathematical lemma is retained, with its source-library
realization. No quarantined consumer references this module or declaration.
The unit sk-thm-picard-rr and its route are unchanged.

## Status

landed 20261020T233108-L-893264 2026-10-20 (merge of deliver/C7/Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective)
