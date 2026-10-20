# AlgebraicGeometry.exists_finitePresentation_local_map_lifts

## Reason

The human-approved retirement queue lists this duplicate Sheaf module for retirement
(coord/changes/retire-sheaf-twins-20261020.md and coord/retire-items.tsv).
The upstream theorem proves precisely the same conclusion with no Noetherian assumption.
Use it in the sole direct consumer and attach the existing node to that theorem.
No upstream file or target statement changes.

## Old

The duplicate declaration being withdrawn has this signature:

```lean
theorem exists_finitePresentation_local_map_lifts
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    (∀ (j : I) (hij : i ≤ j) (Fj Gj : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules),
      Fj.IsFinitePresentation → Fj.IsQuasicoherent →
      Gj.IsFinitePresentation → Gj.IsQuasicoherent →
      ∀ φ : (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Fj ⟶
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Gj,
      ∃ (j' : I) (hjj' : j ≤ j'),
        let A := Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let B := Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))
        ∃ e : Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)) ≅ A ⋙ B,
          e = Scheme.Modules.tensorPullbackCompositionIso
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (Over.homMk (Spec.map (R.map (homOfLE hjj')))
                (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))
            (by
              rw [← baseChangeMap_comp]
              congr 1
              ext
              simpa using c.w (homOfLE hjj').op) ∧
        ∃ U : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjj'))))).OpenCover.{u},
          Finite U.I₀ ∧ (∀ a, IsAffine (U.X a)) ∧
          let Q := modulesPseudofunctor.toDescentData U.f
          let p := baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))
          let V := U.pullback₁ p
          ∃ r : ∀ a, (Q.obj (A.obj Fj)).obj a ⟶ (Q.obj (A.obj Gj)).obj a,
            ∀ a,
              let t := Scheme.Modules.openCoverTensorPullbackComparison p U a
              t.inv.app (A.obj Fj) ≫ (Scheme.Modules.pullback
                (U.pullbackHom p a)).map (r a) ≫ t.hom.app (A.obj Gj) =
              (Scheme.Modules.pullback (V.f a)).map
                (e.inv.app Fj ≫ φ ≫ e.hom.app Gj))
```

The consumer imported:

```lean
import Sheaf.AlgebraicGeometry.FinitePresentationLocalMapLifts
```

## New

Withdraw lean/Sheaf/AlgebraicGeometry/FinitePresentationLocalMapLifts.lean using deleted.txt.
The surviving theorem is the existing declaration with the same name in
WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapLifts; its signature is exactly
the old signature above with `[∀ k : I, IsNoetherianRing (R.obj k)]` omitted.
The consumer imports it privately:

```lean
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapLifts
```

The call site is unchanged: the removed hypothesis was an implicit typeclass argument.
The consumer's complete signature, visibility, public imports and proof remain unchanged.
The node's Lean record points to the surviving theorem and records the specialization.
Its mathematical statement, proof route and dependencies remain unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FinitePresentationLocalMapLifts | C7 | Retire duplicate module. |
| Sheaf.AlgebraicGeometry.FinitePresentationLocalMapDatum | unclaimed | Replace one private proof import; theorem call and signature unchanged. |

`tools/downstream.py --direct --uses exists_finitePresentation_local_map_lifts` reports
only this direct consumer. All references in Lean sources were searched with rg.
Downstream users of the consumer see the same declaration signature and public imports.
The upstream declaration is preserved verbatim and the node still expresses its
Noetherian specialization. No target definition is changed.

## Status

landed 20261020T141305-L-2032341 2026-10-20 (merge of deliver/C7/Sheaf.AlgebraicGeometry.FinitePresentationLocalMapLifts)
