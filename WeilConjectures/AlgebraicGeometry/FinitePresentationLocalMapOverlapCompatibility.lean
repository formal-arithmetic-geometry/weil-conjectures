/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison
public import WeilConjectures.AlgebraicGeometry.LocalMapPullbackFamily
public import WeilConjectures.AlgebraicGeometry.LocalMapRecovery
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapOverlapEquations
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapRecoveryTransport

/-! # Eventual overlap compatibility of local lifts

## References

* Stacks Project, Tag 01ZR
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry


private theorem map_stage {J : Type u} {H : J → Prop}
    {P S : ∀ j, H j → Prop} (h : ∃ j hj, P j hj)
    (g : ∀ j hj, P j hj → S j hj) : ∃ j hj, S j hj := by
  obtain ⟨j, hj, hp⟩ := h
  exact ⟨j, hj, g j hj hp⟩

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackCompositionIso Scheme.Modules.openCoverTensorPullbackComparison

-- The dependent base-change comparisons require additional elaboration heartbeats.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- A given finite family of local lifts becomes compatible at a later stage.
The new family is explicitly the pullback of the given family, on the pullback
of its cover. The conclusion provides a descent morphism with exactly these
components. No new local maps are chosen.
(Stacks, Tag 01ZR, Tag 05N7) -/
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
              (e.inv.app Fj ≫ φ ≫ e.hom.app Gj) r) := by
  intro j hij Fj Gj hF hFq hG hGq φ k hjk A₀ B₀ e₀ he₀ U₀ hfin haff Q₀ p₀ V₀ r₀ hr₀
  let h := baseChangeMap f
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
    (Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
  let δ : B₀.obj (A₀.obj Fj) ⟶ B₀.obj (A₀.obj Gj) :=
    e₀.inv.app Fj ≫ φ ≫ e₀.hom.app Gj
  change localMapRecovery p₀ U₀ (A₀.obj Fj) (A₀.obj Gj) δ r₀ at hr₀
  have ho :=
    finitePresentation_local_maps_eventual_overlap_equations (I := I) (Xi := Xi)
      R c hc i f j hij Fj Gj hF hFq hG hGq k hjk A₀ rfl
      δ U₀ hfin haff r₀ hr₀
  refine map_stage ho ?_
  intro l hkl hl hjj' A _B e q z U Q p V r
  refine ⟨hl.1, hl.2 (A.obj Fj) (A.obj Gj) (z.hom.app Fj) (z.inv.app Gj), ?_⟩
  let a := baseChangeMap f
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (c.π.app (op i)))
    (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
  let d := baseChangeMap f
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
    (Over.homMk (Spec.map (R.map (homOfLE hjj')))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
  exact finitePresentation_local_maps_recovery_transport
    (X₀ := pullback f (Spec.map (R.map (homOfLE hij))))
    (X₁ := pullback f (Spec.map (R.map (homOfLE (hij.trans hjk)))))
    (X₂ := pullback f (Spec.map (R.map (homOfLE (hij.trans hjj')))))
    (Z := pullback f (c.π.app (op i))) h q p p₀ a d
    (by
      rw [← baseChangeMap_comp]
      congr 1
      ext
      simpa using c.w (homOfLE hkl).op)
    (by
      rw [← baseChangeMap_comp]
      congr 1
      ext
      change Spec.map (R.map (homOfLE hkl)) ≫ Spec.map (R.map (homOfLE hjk)) =
        Spec.map (R.map (homOfLE hjj'))
      rw [← Spec.map_comp, ← R.map_comp]; rfl)
    (by
      rw [← baseChangeMap_comp]
      congr 1
      ext
      simpa using c.w (homOfLE hjk).op)
    (by
      rw [← baseChangeMap_comp]
      congr 1
      ext
      simpa using c.w (homOfLE hjj').op)
    A₀ rfl A rfl (Scheme.Modules.moduleBaseChange f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))) rfl
    Fj Gj φ e₀ (heq_of_eq he₀) e (by rfl) z (by rfl) U₀ r₀ hr₀
end AlgebraicGeometry
