# AlgebraicGeometry.finitePresentation_local_maps_eventually_compatible

## Reason

Repeated expansion of the explicit five-map family and its recovery equation caused
the previous delivery's kernel checks to exceed the mandatory 60-second limit.
Share the real construction as localMapPullbackFamily and the explicit equality
predicate as localMapRecovery. Both definitions have concrete bodies and choose no
maps or witnesses. Their unfolded formulas are exactly the original formulas.
The unused lets B, V₀ and V are named _B, _V₀ and _V; the result's let order is kept.
No mathematical hypothesis or conclusion, visibility, universe, or canonical
comparison changes, and no Challenge target declaration is changed.

The new family definition uses ordinary restriction functors in its signature;
these are definitionally the components of toDescentData. Its irreducible attribute
prevents accidental elaborator expansion and is exported only for this new name.
The three theorem modules use local irreducibility and scoped elaboration options;
they do not alter the reducibility of any existing declaration for importers.

## Old

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
          let V₀ := U₀.pullback₁ p₀
          ∀ r₀ : ∀ a, (Q₀.obj (A₀.obj Fj)).obj a ⟶ (Q₀.obj (A₀.obj Gj)).obj a,
            (∀ a,
              let t := Scheme.Modules.openCoverTensorPullbackComparison p₀ U₀ a
              t.inv.app (A₀.obj Fj) ≫ (Scheme.Modules.pullback
                (U₀.pullbackHom p₀ a)).map (r₀ a) ≫ t.hom.app (A₀.obj Gj) =
              (Scheme.Modules.pullback (V₀.f a)).map
                (e₀.inv.app Fj ≫ φ ≫ e₀.hom.app Gj)) →
          ∃ (j' : I) (hkj' : k ≤ j'),
            let hjj' := hjk.trans hkj'
        let A := Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let B := Scheme.Modules.moduleBaseChange f
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
            let V := U.pullback₁ p
            let r : ∀ a, (Q.obj (A.obj Fj)).obj a ⟶ (Q.obj (A.obj Gj)).obj a := fun a ↦
              let t := Scheme.Modules.openCoverTensorPullbackComparison q U₀ a
              (Scheme.Modules.pullback (U.f a)).map (z.hom.app Fj) ≫
                t.inv.app (A₀.obj Fj) ≫
                (Scheme.Modules.pullback (U₀.pullbackHom q a)).map (r₀ a) ≫
                t.hom.app (A₀.obj Gj) ≫
                (Scheme.Modules.pullback (U.f a)).map (z.inv.app Gj)
            (∀ a, IsAffine (U.X a)) ∧
            (∃ ψ : Q.obj (A.obj Fj) ⟶ Q.obj (A.obj Gj),
              (∀ a, ψ.hom a = r a)) ∧
            (∀ a,
              let t := Scheme.Modules.openCoverTensorPullbackComparison p U a
              t.inv.app (A.obj Fj) ≫ (Scheme.Modules.pullback
                (U.pullbackHom p a)).map (r a) ≫ t.hom.app (A.obj Gj) =
              (Scheme.Modules.pullback (V.f a)).map
                (e.inv.app Fj ≫ φ ≫ e.hom.app Gj)))
```

## New

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

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility | F3 | Same statement with two concrete formulas named; complete reduction to two smaller statements. |
| Sheaf.AlgebraicGeometry.FinitePresentationLocalMapDatum | unclaimed | Uses the same equation and family after unfolding; its unchanged source compiles against the delivery. |

tools/downstream.py --uses finds exactly the declaration's own module and
FinitePresentationLocalMapDatum. The latter is the sole direct importer.
Transitive users see the same mathematical statement. The two new intermediate
modules use the shared definitions directly; no existing consumer needs adaptation.

## Status

landed 20261013T190139-L-3216022 2026-10-13 (merge of deliver/F3/Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility)
