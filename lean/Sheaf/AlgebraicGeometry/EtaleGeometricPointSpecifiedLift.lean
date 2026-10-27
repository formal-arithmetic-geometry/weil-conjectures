/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Lifting a geometric point over a specified algebraic-space point

Source: Stacks Project, Properties of Spaces, Tag 05VN, lemma-geometric-lift-to-usual;
Tag 03H4, lemma-points-cartesian
(blueprint: lem-sfb-etale-geometric-point-specified-lift).

Point classes and their induced map are the existing `Point` and `mapPoint`.
The geometric point and its lift have the same field and the same map to the base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private theorem pointRepresentative_rel_equivalence {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type u) : Equivalence (PointRepresentative.Rel (F := F)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact ⟨p.K, inferInstance, p.base, 𝟙 _, 𝟙 _, rfl⟩
  · rintro p q ⟨L, hL, s, a, b, h⟩
    exact ⟨L, hL, s, b, a, h.symm⟩
  · rintro p q r ⟨L, hL, s, a, b, h⟩ ⟨M, hM, t, c, d, k⟩
    let Q := Limits.pullback b c
    let f : Q ⟶ Over.mk s := Limits.pullback.fst b c
    let g : Q ⟶ Over.mk t := Limits.pullback.snd b c
    have hQ : IsPullback f.left g.left b.left c.left :=
      (IsPullback.of_hasPullback b c).map (Over.forget S)
    obtain ⟨z, _, _⟩ := Scheme.exists_preimage_of_isPullback hQ
      (default : Spec (.of L)) (default : Spec (.of M))
      (Subsingleton.elim (α := Spec (.of q.K)) _ _)
    let v : Over.mk (Q.left.fromSpecResidueField z ≫ Q.hom) ⟶ Q :=
      Over.homMk (Q.left.fromSpecResidueField z) rfl
    let m := v ≫ f
    let n := v ≫ g
    have hmn : m ≫ b = n ≫ c := by
      dsimp [m, n, f, g]
      rw [Category.assoc, Category.assoc, Limits.pullback.condition]
    refine ⟨Q.left.residueField z, inferInstance,
      Q.left.fromSpecResidueField z ≫ Q.hom, m ≫ a, n ≫ d, ?_⟩
    calc
      F.map (m ≫ a).op p.value = F.map m.op (F.map a.op p.value) := by simp
      _ = F.map m.op (F.map b.op q.value) := congrArg (F.map m.op) h
      _ = F.map (m ≫ b).op q.value := by simp
      _ = F.map (n ≫ c).op q.value := by rw [hmn]
      _ = F.map n.op (F.map c.op q.value) := by simp
      _ = F.map n.op (F.map d.op r.value) := congrArg (F.map n.op) k
      _ = F.map (n ≫ d).op r.value := by simp

private theorem field_point_class {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {T : Over S} (q : yoneda.obj T ⟶ F) {K : Type u} [Field K]
    (s : Spec (.of K) ⟶ S) (j : Over.mk s ⟶ T) :
    Quot.mk _ (⟨K, s, q.app _ j⟩ : PointRepresentative F) =
      schemePointMap q (j.left (default : Spec (.of K))) := by
  let x := j.left (IsLocalRing.closedPoint K)
  let e := Scheme.descResidueField (Scheme.stalkClosedPointTo j.left)
  have he : Spec.map e ≫ T.left.fromSpecResidueField x = j.left :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K T.left j.left
  let r : Over.mk s ⟶ Over.mk (T.left.fromSpecResidueField x ≫ T.hom) :=
    Over.homMk (Spec.map e) (by
      change Spec.map e ≫ (T.left.fromSpecResidueField x ≫ T.hom) = s
      rw [← Category.assoc, he]
      exact j.w)
  have hr : r ≫ Over.homMk (T.left.fromSpecResidueField x) rfl = j := by
    ext1
    exact he
  have hx : j.left (default : Spec (.of K)) = x :=
    congrArg j.left (Subsingleton.elim (α := Spec (.of K)) _ _)
  rw [hx]
  apply Quot.sound
  refine ⟨K, inferInstance, s, 𝟙 _, r, ?_⟩
  change F.map (𝟙 _).op (q.app _ j) =
    F.map r.op (q.app _ (Over.homMk (T.left.fromSpecResidueField x) rfl))
  rw [op_id, F.map_id, ← NatTrans.naturality_apply]
  change q.app _ j = q.app _ (r ≫ Over.homMk _ rfl)
  rw [hr]

/-- A representable étale morphism lifts a geometric point over any specified source
point above its image, without extending the algebraically closed field.
Source: Stacks Project, Properties of Spaces, Tag 05VN, lemma-geometric-lift-to-usual
(blueprint: lem-sfb-etale-geometric-point-specified-lift).

Proof:
1. Set T = Spec Ω and represent T ×_X U by a scheme P. By
   def-trf-algebraic-space, its projection a : P → T is étale; write b : P → U
   for the other projection. The pullback identity says e b = xbar a.
2. Choose a field-valued representative of u. The equality of its image class with
   the class of xbar gives a common field extension M on which the maps to X agree.
   These maps define a field-valued point of P, centered at a point p whose image
   under b is u and whose image under a is the unique point of T. This is the
   common-field construction in Tag 03H4; extending a representative preserves its class.
3. The singleton family consisting of a is jointly surjective, since T has one point
   and p maps to it. Apply the prescribed-point clause of
   lem-weil-pbc-etale-cover-geometric-point-lift, namely
   Scheme.exists_fac_of_etale_of_isSepClosed, to a, id_T and p. Algebraic closedness
   implies separable closedness. It gives a section t : T → P centered at p.
4. The composite b t has class u and satisfies e b t = xbar a t = xbar. Its source
   is the original T, so the temporary field M in step 2 does not enlarge Ω. -/
theorem exists_etale_geometricPoint_specified_lift {S : Scheme.{u}}
    {X U : AlgebraicSpace S} (e : U ⟶ X) (he : IsEtale e.hom.hom)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (xbar : yoneda.obj (Over.mk s) ⟶ X.obj.obj) (u : Point U.obj.obj)
    (hu : mapPoint e.hom.hom u = Quot.mk _ ⟨Ω, s, yonedaEquiv xbar⟩) :
    ∃ ubar : yoneda.obj (Over.mk s) ⟶ U.obj.obj,
      Quot.mk _ ⟨Ω, s, yonedaEquiv ubar⟩ = u ∧ ubar ≫ e.hom.hom = xbar := by
  classical
  induction u using Quot.inductionOn with
  | h v =>
    have hv : PointRepresentative.Rel (v.map e.hom.hom)
        ⟨Ω, s, yonedaEquiv xbar⟩ :=
      (pointRepresentative_rel_equivalence X.obj.obj).eqvGen_iff.mp
        (Quot.eqvGen_exact hu)
    obtain ⟨L, hL, t, a, b, hab⟩ := hv
    dsimp only [PointRepresentative.map] at a b hab
    obtain ⟨Q, p, q, hQ, hp⟩ := he (Over.mk s) xbar
    have hcompat : e.hom.hom.app _ (U.obj.obj.map a.op v.value) = xbar.app _ b := by
      exact (NatTrans.naturality_apply e.hom.hom a.op v.value).trans
        (hab.trans (map_yonedaEquiv xbar b))
    obtain ⟨j, hjq, _⟩ := Types.exists_of_isPullback
      (hQ.app (op (Over.mk t))) (U.obj.obj.map a.op v.value) b hcompat
    have : Etale p.left := hp
    obtain ⟨l, hl, hlz⟩ := Scheme.exists_fac_of_etale_of_isSepClosed p.left
      (𝟙 _) (j.left (default : Spec (.of L)))
      (Subsingleton.elim (α := Spec (.of Ω)) _ _)
    let lO : Over.mk s ⟶ Q := Over.homMk l (by
      rw [← Over.w p, ← Category.assoc, hl]
      simp)
    have hlO : lO ≫ p = 𝟙 _ := by
      ext1
      exact hl
    refine ⟨yoneda.map lO ≫ q, ?_, ?_⟩
    · have hvalue : yonedaEquiv (yoneda.map lO ≫ q) = q.app _ lO := by
        rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
        rfl
      calc
        Quot.mk _ ⟨Ω, s, yonedaEquiv (yoneda.map lO ≫ q)⟩ =
            Quot.mk _ ⟨Ω, s, q.app _ lO⟩ := by
              rw [hvalue]
              rfl
        _ = schemePointMap q (l default) := field_point_class q s lO
        _ = schemePointMap q (j.left (default : Spec (.of L))) :=
          congrArg (schemePointMap q) hlz
        _ = Quot.mk _ ⟨L, t, q.app _ j⟩ := (field_point_class q t j).symm
        _ = Quot.mk _ v := by
          apply Quot.sound
          refine ⟨L, inferInstance, t, 𝟙 _, a, ?_⟩
          simpa only [op_id, U.obj.obj.map_id, types_id_apply] using hjq
    · rw [Category.assoc, hQ.w, ← Category.assoc, ← Functor.map_comp, hlO]
      simp

end AlgebraicGeometry.AlgebraicSpace
