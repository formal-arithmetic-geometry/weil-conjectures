/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
public import Sheaf.AlgebraicGeometry.OpenCoverTensorPullbackComparison

/-! # Transport of a supplied chart map lift to later stages

Source: Stacks Project, Sheaves of Modules, Tags 0095 and 0096,
and Limits Tag 01ZR, persistence under further base change.
(blueprint: lem-pc-open-cover-map-lift-transport).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A chart lift at a supplied stage persists at every later stage. This is
functorial transport only: no finite-presentation, affine-chart, directedness,
affine-limit or limit-universal-property hypothesis is assumed.
Source: Stacks Project, Tags 0095, 0096 and 01ZR, first proof.
(blueprint: lem-pc-open-cover-map-lift-transport).

Proof: Fix a later stage l with j ≤ l and k ≤ l. In the category over Spec R(i),
form q:Tk → Tj, s:Tl → Tk and v:Tl → Tj from the ring-system maps. The ring
functor composition law and Spec.map_comp give s ≫ q = v. Write pk, pl and h
for the cone projections to Tk, Tl and Tj over Spec R(i). Cone naturality gives
pl ≫ s = pk, pk ≫ q = h and pl ≫ v = h. Applying baseChangeMap f yields the
same triangles for the fibre-product schemes.
Let Uk and Ul be the pulled-back covers. Cartesian chart squares give a map
d:Ul.X(a) → Uk.X(a) with d ≫ Uk.f(a) = Ul.f(a) ≫ baseChangeMap(f,s), and
 d ≫ Uj.pullbackHom(baseChangeMap(f,q),a) =
 Uj.pullbackHom(baseChangeMap(f,v),a).
Pull back the supplied chart map rk along d. Restriction of moduleBaseChange(f,v)
is canonically isomorphic to d-pullback of restriction of moduleBaseChange(f,q),
by tensor-to-ordinary pullback comparison, pullback composition and the first
triangle. Conjugating d-pullback(rk) by this comparison gives the required rl.
At the cone vertex the two iterated pulled-back charts are canonically isomorphic
by cartesian pasting. Their refinement triangle follows from pl ≫ s = pk.
Pull rk's recovery equation back along this refinement. Naturality moves each
comparison through rk; associativity identifies the remaining comparisons with
the ones for pl and v. These comparisons are mates of the same pushforward
composition isomorphisms under the pinned adjunctions, so pushforward
associativity establishes their coherence. Thus rl has the displayed recovery
equation. The supplied recovery assertion, not finite presentation or the limit
property, is the only input concerning φ. Empty charts, zero modules, identity
transitions and equivalent indices of the preorder are all included. -/
theorem openCover_map_lift_transport
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec))
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (Fj Gj : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (φ : (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Fj ⟶
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Gj)
    (Uj : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    (a : Uj.I₀) (k : I) (hjk : j ≤ k) :
    (let A := Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (Over.homMk (Spec.map (R.map (homOfLE hjk)))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let B := Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
      let q := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U : (pullback f (Spec.map
        (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} := Uj.pullback₁ q
      let e := Scheme.Modules.tensorPullbackCompositionIso
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
              simpa using c.w (homOfLE hjk).op)
      let Q := modulesPseudofunctor.toDescentData U.f
      let p := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
      let V := U.pullback₁ p
      ∃ r : (Q.obj (A.obj Fj)).obj a ⟶ (Q.obj (A.obj Gj)).obj a,
        let t := Scheme.Modules.openCoverTensorPullbackComparison p U a
        t.inv.app (A.obj Fj) ≫ (Scheme.Modules.pullback
          (U.pullbackHom p a)).map r ≫ t.hom.app (A.obj Gj) =
        (Scheme.Modules.pullback (V.f a)).map
          (e.inv.app Fj ≫ φ ≫ e.hom.app Gj)) →
    ∀ (j' : I) (hjj' : j ≤ j'), k ≤ j' →
      let A := Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let B := Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))
      let q := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
        (Over.homMk (Spec.map (R.map (homOfLE hjj')))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U : (pullback f (Spec.map
        (R.map (homOfLE (hij.trans hjj'))))).OpenCover.{u} := Uj.pullback₁ q
      let e := Scheme.Modules.tensorPullbackCompositionIso
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
              simpa using c.w (homOfLE hjj').op)
      let Q := modulesPseudofunctor.toDescentData U.f
      let p := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))
      let V := U.pullback₁ p
      ∃ r : (Q.obj (A.obj Fj)).obj a ⟶ (Q.obj (A.obj Gj)).obj a,
        let t := Scheme.Modules.openCoverTensorPullbackComparison p U a
        t.inv.app (A.obj Fj) ≫ (Scheme.Modules.pullback
          (U.pullbackHom p a)).map r ≫ t.hom.app (A.obj Gj) =
        (Scheme.Modules.pullback (V.f a)).map
          (e.inv.app Fj ≫ φ ≫ e.hom.app Gj) := by sorry

end AlgebraicGeometry
