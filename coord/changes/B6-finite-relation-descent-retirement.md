# AlgebraicGeometry.finiteRelation_module_map_descent

## Reason

The queue assigns `Sheaf.AlgebraicGeometry.FiniteRelationDescent` as `retire`.
The adopted source module already provides this theorem, proved without the
Noetherian-ring assumption of the redundant Sheaf copy. The Sheaf module has no
importers. Retain the source declaration verbatim, withdraw the unused duplicate,
and move the existing DAG attachment to the retained source declaration.

## Old

In `Sheaf.AlgebraicGeometry.FiniteRelationDescent`:

```lean
theorem finiteRelation_module_map_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (M : Type u) [Finite M]
    (Fj : M → (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (hFj_fp : ∀ k : M, (Fj k).IsFinitePresentation)
    (hFj_qc : ∀ k : M, (Fj k).IsQuasicoherent)
    (n : ℕ) (src tgt : Fin n → M)
    (lhs rhs : ∀ k : Fin n, Fj (src k) ⟶ Fj (tgt k))
    (hrel : ∀ k : Fin n,
      (Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map (lhs k) =
      (Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map (rhs k)) :
    ∃ (j' : I) (hjj' : j ≤ j'),
      ∀ k : Fin n,
        (Scheme.Modules.moduleBaseChange f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
          (Over.homMk (Spec.map (R.map (homOfLE hjj')))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).map (lhs k) =
        (Scheme.Modules.moduleBaseChange f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
          (Over.homMk (Spec.map (R.map (homOfLE hjj')))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).map (rhs k)
```

## New

The Sheaf module is withdrawn. Its DAG node attaches to the existing declaration
in `WeilConjectures.AlgebraicGeometry.FiniteRelationDescent`, unchanged:

```lean
theorem finiteRelation_module_map_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (M : Type u) [Finite M]
    (Fj : M → (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (hFj_fp : ∀ k : M, (Fj k).IsFinitePresentation)
    (hFj_qc : ∀ k : M, (Fj k).IsQuasicoherent)
    (n : ℕ) (src tgt : Fin n → M)
    (lhs rhs : ∀ k : Fin n, Fj (src k) ⟶ Fj (tgt k))
    (hrel : ∀ k : Fin n,
      (Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map (lhs k) =
      (Scheme.Modules.moduleBaseChange f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map (rhs k)) :
    ∃ (j' : I) (hjj' : j ≤ j'),
      ∀ k : Fin n,
        (Scheme.Modules.moduleBaseChange f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
          (Over.homMk (Spec.map (R.map (homOfLE hjj')))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).map (lhs k) =
        (Scheme.Modules.moduleBaseChange f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
          (Over.homMk (Spec.map (R.map (homOfLE hjj')))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).map (rhs k)
```

The retained theorem directly proves the old signature by application; the
Noetherian instance is unused. The node's mathematical statement and proof remain
unchanged. No definition or target changes meaning, and no target review reopens.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteRelationDescent | B6 | Withdraw the unused duplicate. |
| WeilConjectures.AlgebraicGeometry.FinitelyPresentedComplexDescent | unclaimed | Already imports the retained source module and applies its theorem; no change. |

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteRelationDescent --uses
finiteRelation_module_map_descent` reports zero downstream modules and only the
Sheaf declaration itself as a use in the Sheaf tree. An independent search of
both source roots finds no import of the Sheaf module; the only theorem application
outside the duplicate modules is the source consumer listed above. No consumer
adaptation is needed. No adopted source file, signature, attribute, import, or
proof is changed.

## Status

landed 20261020T135351-L-1814591 2026-10-20 (merge of deliver/B6/Sheaf.AlgebraicGeometry.FiniteRelationDescent)
