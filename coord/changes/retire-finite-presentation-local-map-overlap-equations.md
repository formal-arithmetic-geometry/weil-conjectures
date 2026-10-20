# AlgebraicGeometry.finitePresentation_local_maps_eventual_overlap_equations

## Reason

The stage-3 queue marks `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapEquations` as `retire`.
The adopted source module `WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapOverlapEquations` already proves the same theorem
without assuming that the rings are Noetherian. The local duplicate has zero proof holes.
Keeping both declarations creates an unnecessary duplicate theorem.

## Old

The duplicate in `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapEquations` has signature:

```lean
theorem finitePresentation_local_maps_eventual_overlap_equations
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    (∀ (j : I) (hij : i ≤ j) (Fj Gj : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules),
      Fj.IsFinitePresentation → Fj.IsQuasicoherent →
      Gj.IsFinitePresentation → Gj.IsQuasicoherent →
      ∀ (k : I) (hjk : j ≤ k),
        ∀ (A₀ : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules ⥤
            (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).Modules),
          A₀ = Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (Over.homMk (Spec.map (R.map (homOfLE hjk)))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) →
        let B₀ := Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
        ∀ δ : B₀.obj (A₀.obj Fj) ⟶ B₀.obj (A₀.obj Gj),
        ∀ (U₀ : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u}),
          Finite U₀.I₀ → (∀ a, IsAffine (U₀.X a)) →
          let Q₀ := modulesPseudofunctor.toDescentData U₀.f
          let p₀ := baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
          let V₀ := U₀.pullback₁ p₀
          ∀ r₀ : ∀ a, (Q₀.obj (A₀.obj Fj)).obj a ⟶ (Q₀.obj (A₀.obj Gj)).obj a,
            localMapRecovery p₀ U₀ (A₀.obj Fj) (A₀.obj Gj) δ r₀ →
          ∃ (j' : I) (hkj' : k ≤ j'),
            let q := (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans (hjk.trans hkj'))))))
              (Over.homMk (Spec.map (R.map (homOfLE hkj')))
                (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)));
            let U : (pullback f
              (Spec.map (R.map (homOfLE (hij.trans (hjk.trans hkj')))))).OpenCover.{u} :=
              U₀.pullback₁ q
            let Q := modulesPseudofunctor.toDescentData U.f
            let C := Scheme.Modules.tensorPullback q
            (∀ α, IsAffine (U.X α)) ∧
            (∀ (F' G' : (pullback f
                (Spec.map (R.map (homOfLE (hij.trans (hjk.trans hkj')))))).Modules)
              (κ : F' ⟶ C.obj (A₀.obj Fj)) (ρ : C.obj (A₀.obj Gj) ⟶ G'),
              let r : ∀ α, (Q.obj F').obj α ⟶ (Q.obj G').obj α :=
                localMapPullbackFamily q U₀ (A₀.obj Fj) (A₀.obj Gj) F' G' κ ρ r₀
              ∃ ψ : Q.obj F' ⟶ Q.obj G', ∀ α, ψ.hom α = r α))
```

Its direct consumer has the private proof import:

```lean
import Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapEquations
```

## New

Withdraw `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapEquations` using `deleted.txt`; no source-library declaration is changed.
The node now points to the adopted source theorem:

```lean
theorem finitePresentation_local_maps_eventual_overlap_equations
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    (∀ (j : I) (hij : i ≤ j) (Fj Gj : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules),
      Fj.IsFinitePresentation → Fj.IsQuasicoherent →
      Gj.IsFinitePresentation → Gj.IsQuasicoherent →
      ∀ (k : I) (hjk : j ≤ k),
        ∀ (A₀ : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules ⥤
            (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).Modules),
          A₀ = Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (Over.homMk (Spec.map (R.map (homOfLE hjk)))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) →
        let B₀ := Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
        ∀ δ : B₀.obj (A₀.obj Fj) ⟶ B₀.obj (A₀.obj Gj),
        ∀ (U₀ : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u}),
          Finite U₀.I₀ → (∀ a, IsAffine (U₀.X a)) →
          let Q₀ := modulesPseudofunctor.toDescentData U₀.f
          let p₀ := baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
          let V₀ := U₀.pullback₁ p₀
          ∀ r₀ : ∀ a, (Q₀.obj (A₀.obj Fj)).obj a ⟶ (Q₀.obj (A₀.obj Gj)).obj a,
            localMapRecovery p₀ U₀ (A₀.obj Fj) (A₀.obj Gj) δ r₀ →
          ∃ (j' : I) (hkj' : k ≤ j'),
            let q := (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans (hjk.trans hkj'))))))
              (Over.homMk (Spec.map (R.map (homOfLE hkj')))
                (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)));
            let U : (pullback f
              (Spec.map (R.map (homOfLE (hij.trans (hjk.trans hkj')))))).OpenCover.{u} :=
              U₀.pullback₁ q
            let Q := modulesPseudofunctor.toDescentData U.f
            let C := Scheme.Modules.tensorPullback q
            (∀ α, IsAffine (U.X α)) ∧
            (∀ (F' G' : (pullback f
                (Spec.map (R.map (homOfLE (hij.trans (hjk.trans hkj')))))).Modules)
              (κ : F' ⟶ C.obj (A₀.obj Fj)) (ρ : C.obj (A₀.obj Gj) ⟶ G'),
              let r : ∀ α, (Q.obj F').obj α ⟶ (Q.obj G').obj α :=
                localMapPullbackFamily q U₀ (A₀.obj Fj) (A₀.obj Gj) F' G' κ ρ r₀
              ∃ ψ : Q.obj F' ⟶ Q.obj G', ∀ α, ψ.hom α = r α))
```

Replace the consumer's private proof import with:

```lean
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapOverlapEquations
```

The consumer statement, proof and all its public imports remain verbatim.
The replacement theorem has exactly the same explicit arguments; the unused
Noetherian typeclass assumption was removed upstream. Thus the existing application
uses it directly, with no change to the consumer's statement or proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility | unclaimed | Replace the one private proof import; statement and proof unchanged |
| Sheaf.AlgebraicGeometry.FinitePresentationLocalMapDatum | unclaimed | Transitive importer; unchanged |
| Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapEquations | C5 | Withdraw duplicate theorem and redirect its node to the source theorem |

The users were enumerated with `tools/downstream.py` and a source search for the
module and declaration names. No source-library file imports the withdrawn module.
The adapted consumer compiled cleanly with `lcompile.py` (6.2 seconds).
`import_direction.py may` confirms there is no import cycle.
The node's hypotheses still give a specialization of the more general source theorem.
No definition, target statement or unit route changes.

## Status

landed 20261020T135353-L-1815216 2026-10-20 (merge of deliver/C5/Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapEquations)
