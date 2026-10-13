/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import Sheaf.AlgebraicGeometry.OpenCoverTensorPullbackComparison
public import Sheaf.AlgebraicGeometry.LocalMapPullbackFamily
public import Sheaf.AlgebraicGeometry.LocalMapRecovery
import Sheaf.AlgebraicGeometry.FinitePresentationZeroMapDescent

/-! # Eventual overlap equations

Source: Stacks Project, Tags 01ZR and 05N7.
(blueprint: lem-pc-fp-local-map-overlap-equations). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.openCoverTensorPullbackComparison

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The local family eventually descends, including after composition with global maps.
Source: Stacks Project, Limits, Tag 01ZR, first proof, agreement on overlaps;
Algebra, Tag 05N7 (3).
(blueprint: lem-pc-fp-local-map-overlap-equations).

Proof: First substitute the equality identifying A₀ with module base change.
At stage k take the difference of the two restrictions of r₀ on each pairwise
intersection of cover members. Their pullbacks to the limit agree, since both recover
the restriction of the same global map δ. Pullback composition identifies the two
restrictions, so their difference pulls back to zero. Quasi-separatedness makes each
intersection quasi-compact. Restricted tensor pullbacks of Fj and Gj remain finitely
presented and quasi-coherent. Apply finitePresentation_zero_map_descent to this
intersection over Spec R_k, using the pullback universal properties to identify its
identity-stage and later base changes. There are finitely many pairs. Directedness
gives one common later stage, and functors preserve zero maps, so all defects vanish
there. Every test scheme mapping to two cover members factors through their
intersection. Pullback of its equality is the universal-test compatibility equation
for the displayed family of pulled-back maps. Assemble its descent morphism with
those components. The transition q is affine, as a base change of a map between
affine schemes; hence the inverse images of the affine cover members are affine.
For arbitrary F', G', κ and ρ in the conclusion, compose this descent morphism on
the left with Q.map κ and on the right with Q.map ρ. The components of Q.map are
ordinary restriction of the maps; functoriality and associativity give exactly the
five displayed factors defining r. This uses no inverse or property of κ and ρ.
The component identities follow from the construction. Empty covers impose no
compatibility equations and use k itself. Empty intersections, zero modules and
identity transitions cause no exceptions. No new-stage recovery is asserted. -/
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
              ∃ ψ : Q.obj F' ⟶ Q.obj G', ∀ α, ψ.hom α = r α)) := by sorry

end AlgebraicGeometry
