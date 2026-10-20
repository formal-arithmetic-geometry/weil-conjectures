# AlgebraicGeometry.finitePresentation_local_maps_eventually_compatible

## Reason

The current stage-3 queue marks the assigned Sheaf module `retire` with one consumer.
Its theorem has zero direct proof holes. The adopted source module
`WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility`
already proves the same statement without the Noetherian-ring hypothesis.
The signatures are byte-identical after removing that one hypothesis from the duplicate.
Use the source theorem and withdraw the redundant Sheaf declaration.

## Old

The withdrawn Sheaf theorem has this signature:

```lean
theorem finitePresentation_local_maps_eventually_compatible
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
      ∀ (k : I) (hjk : j ≤ k),
        let A₀ := Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (Over.homMk (Spec.map (R.map (homOfLE hjk)))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let B₀ := Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
        ∀ (e₀ : Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)) ≅ A₀ ⋙ B₀),
          e₀ = Scheme.Modules.tensorPullbackCompositionIso
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (Over.homMk (Spec.map (R.map (homOfLE hjk)))
                (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))
            (by
              rw [← baseChangeMap_comp]
              congr 1
              ext
              simpa using c.w (homOfLE hjk).op) →
        ∀ (U₀ : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u}),
          Finite U₀.I₀ → (∀ a, IsAffine (U₀.X a)) →
          let Q₀ := modulesPseudofunctor.toDescentData U₀.f
          let p₀ := baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
          let _V₀ := U₀.pullback₁ p₀
          ∀ r₀ : ∀ a, (Q₀.obj (A₀.obj Fj)).obj a ⟶ (Q₀.obj (A₀.obj Gj)).obj a,
            localMapRecovery p₀ U₀ (A₀.obj Fj) (A₀.obj Gj)
              (e₀.inv.app Fj ≫ φ ≫ e₀.hom.app Gj) r₀ →
          ∃ (j' : I) (hkj' : k ≤ j'),
            let hjj' := hjk.trans hkj'
        let A := Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let _B := Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))
            let e := (Scheme.Modules.tensorPullbackCompositionIso
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
              simpa using c.w (homOfLE hjj').op));
            let q := (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (Over.homMk (Spec.map (R.map (homOfLE hkj')))
                (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)));
            let z : A ≅ A₀ ⋙ Scheme.Modules.tensorPullback q :=
              (Scheme.Modules.tensorPullbackCompositionIso q
                (baseChangeMap f
                  (T := Over.mk (Spec.map (R.map (homOfLE hij))))
                  (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
                  (Over.homMk (Spec.map (R.map (homOfLE hjk)))
                    (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
                (baseChangeMap f
                  (T := Over.mk (Spec.map (R.map (homOfLE hij))))
                  (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
                  (Over.homMk (Spec.map (R.map (homOfLE hjj')))
                    (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
                (by
                  rw [← baseChangeMap_comp]
                  congr 1
                  ext
                  change Spec.map (R.map (homOfLE hkj')) ≫
                    Spec.map (R.map (homOfLE hjk)) = Spec.map (R.map (homOfLE hjj'))
                  rw [← Spec.map_comp, ← R.map_comp]; rfl));
            let U : (pullback f
              (Spec.map (R.map (homOfLE (hij.trans hjj'))))).OpenCover.{u} := U₀.pullback₁ q
            let Q := modulesPseudofunctor.toDescentData U.f
            let p := (baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op)))
            let _V := U.pullback₁ p
            let r : ∀ a, (Q.obj (A.obj Fj)).obj a ⟶ (Q.obj (A.obj Gj)).obj a :=
              localMapPullbackFamily q U₀ (A₀.obj Fj) (A₀.obj Gj)
                (A.obj Fj) (A.obj Gj) (z.hom.app Fj) (z.inv.app Gj) r₀
            (∀ a, IsAffine (U.X a)) ∧
            (∃ ψ : Q.obj (A.obj Fj) ⟶ Q.obj (A.obj Gj),
              (∀ a, ψ.hom a = r a)) ∧
            localMapRecovery p U (A.obj Fj) (A.obj Gj)
              (e.inv.app Fj ≫ φ ≫ e.hom.app Gj) r)
```

## New

The existing source theorem has this signature and is preserved verbatim:

```lean
theorem finitePresentation_local_maps_eventually_compatible
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
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
      ∀ (k : I) (hjk : j ≤ k),
        let A₀ := Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (Over.homMk (Spec.map (R.map (homOfLE hjk)))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let B₀ := Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
        ∀ (e₀ : Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)) ≅ A₀ ⋙ B₀),
          e₀ = Scheme.Modules.tensorPullbackCompositionIso
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (Over.homMk (Spec.map (R.map (homOfLE hjk)))
                (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))
            (by
              rw [← baseChangeMap_comp]
              congr 1
              ext
              simpa using c.w (homOfLE hjk).op) →
        ∀ (U₀ : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u}),
          Finite U₀.I₀ → (∀ a, IsAffine (U₀.X a)) →
          let Q₀ := modulesPseudofunctor.toDescentData U₀.f
          let p₀ := baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
          let _V₀ := U₀.pullback₁ p₀
          ∀ r₀ : ∀ a, (Q₀.obj (A₀.obj Fj)).obj a ⟶ (Q₀.obj (A₀.obj Gj)).obj a,
            localMapRecovery p₀ U₀ (A₀.obj Fj) (A₀.obj Gj)
              (e₀.inv.app Fj ≫ φ ≫ e₀.hom.app Gj) r₀ →
          ∃ (j' : I) (hkj' : k ≤ j'),
            let hjj' := hjk.trans hkj'
        let A := Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let _B := Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))
            let e := (Scheme.Modules.tensorPullbackCompositionIso
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
              simpa using c.w (homOfLE hjj').op));
            let q := (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (Over.homMk (Spec.map (R.map (homOfLE hkj')))
                (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)));
            let z : A ≅ A₀ ⋙ Scheme.Modules.tensorPullback q :=
              (Scheme.Modules.tensorPullbackCompositionIso q
                (baseChangeMap f
                  (T := Over.mk (Spec.map (R.map (homOfLE hij))))
                  (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
                  (Over.homMk (Spec.map (R.map (homOfLE hjk)))
                    (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
                (baseChangeMap f
                  (T := Over.mk (Spec.map (R.map (homOfLE hij))))
                  (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
                  (Over.homMk (Spec.map (R.map (homOfLE hjj')))
                    (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
                (by
                  rw [← baseChangeMap_comp]
                  congr 1
                  ext
                  change Spec.map (R.map (homOfLE hkj')) ≫
                    Spec.map (R.map (homOfLE hjk)) = Spec.map (R.map (homOfLE hjj'))
                  rw [← Spec.map_comp, ← R.map_comp]; rfl));
            let U : (pullback f
              (Spec.map (R.map (homOfLE (hij.trans hjj'))))).OpenCover.{u} := U₀.pullback₁ q
            let Q := modulesPseudofunctor.toDescentData U.f
            let p := (baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op)))
            let _V := U.pullback₁ p
            let r : ∀ a, (Q.obj (A.obj Fj)).obj a ⟶ (Q.obj (A.obj Gj)).obj a :=
              localMapPullbackFamily q U₀ (A₀.obj Fj) (A₀.obj Gj)
                (A.obj Fj) (A.obj Gj) (z.hom.app Fj) (z.inv.app Gj) r₀
            (∀ a, IsAffine (U.X a)) ∧
            (∃ ψ : Q.obj (A.obj Fj) ⟶ Q.obj (A.obj Gj),
              (∀ a, ψ.hom a = r a)) ∧
            localMapRecovery p U (A.obj Fj) (A.obj Gj)
              (e.inv.app Fj ≫ φ ≫ e.hom.app Gj) r)
```

The duplicate module is withdrawn using `deleted.txt`. Its sole consumer replaces
`import Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility` with
`import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility`.
Its statement and complete proof are unchanged. The DAG node is retained, with its Lean
attachment redirected to the adopted source theorem. Its natural-language statement remains
the Noetherian specialization, and its proof and proof dependencies remain valid.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FinitePresentationLocalMapDatum | unclaimed in current snapshot | Replace one private proof import; statement and proof unchanged |
| Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility | H5 | Withdraw duplicate; redirect its node to the source theorem |

`tools/downstream.py` lists exactly the one consumer above. A source search finds no
other Lean importer and no source-library importer. The only parent node depending on
this node is `lem-pc-fp-local-map-datum`; its dependency remains satisfied by the same
node attached to the stronger source theorem. No node is deleted. The unit record has
no realization at this node; the unit route is retained. No target or definition changes.
The consumer is unclaimed, so this is an authorized adaptation accompanying retirement.

The adapted consumer compiled cleanly through `lcompile.py` in 18.3 seconds.
`import_direction.py may` confirmed the replacement import is acyclic.

## Status

landed 20261020T160757-L-3407056 2026-10-20 (merge of deliver/H5/Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility)
