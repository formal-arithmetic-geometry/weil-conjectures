/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Sheaf.AlgebraicGeometry.AffinePushforwardColimit

/-! # Quasi-coherent sections descend along affine inverse limits

Source: Stacks Project, Limits, Lemma 01Z0 (lemma-descend-section)
(blueprint: lem-sc-valuation-limit-qcoh-section-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- For a qcqs inverse system of schemes with affine transitions, global sections of a
quasi-coherent module on a fixed stage are recovered from the directed system of sections
on the later pullbacks.  The diagram `M` records these section groups (the displayed
equivalences and `hM` specify its objects and maps), and `hq` pins `q` to the canonical
map from their colimit to the sections on the limit. The sheaf morphisms `r` and `t`
are uniquely pinned to pullback by their adjunction-unit equations `hr` and `ht`.

Source: Stacks Project, Limits, Lemma 01Z0.
(blueprint: lem-sc-valuation-limit-qcoh-section-descent).

Proof:
1. Pass to the cofinal tail above `i₀`. Its projections are affine, by
   lem-weil-pbc-limit-affine-transition.
2. Apply affine_pushforward_colimit (lem-sc-valuation-limit-affine-pushforward-colimit):
   pushforwards of the pullbacks identify with `F` tensored with the pushforward algebras;
   the limit algebra and its tensor module are the directed colimits of these diagrams.
3. On the qcqs base, global sections commute with this directed module colimit, by
   lem-weil-pbc-qs-scheme-cohomology-directed-colimit at degree zero and the whole open.
4. Sections of each pushforward are sections on its source. Substitute these identifications
   into step 3 to obtain the canonical bijection. The zero criterion for a directed colimit
   (lem-weil-pbc-filtered-colimit-modules-elementwise) gives eventual vanishing.
-/
theorem valuation_limit_qcoh_section_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (s : Cone D) (hs : IsLimit s)
    [∀ i : I, CompactSpace (D.obj (op i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (op i))]
    (haff : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f.op))
    (i₀ : I) (F : (D.obj (op i₀)).Modules) [F.IsQuasicoherent]
    (g : ∀ j : {j : I // i₀ ≤ j}, D.obj (op j.val) ⟶ D.obj (op i₀))
    (hg : ∀ j, g j = D.map (homOfLE j.property).op)
    (r : ∀ {j k : {j : I // i₀ ≤ j}} (f : j ⟶ k),
      (tensorPullback (g j)).obj F ⟶
        (pushforward (D.map (homOfLE (x := j.val) (y := k.val) (leOfHom f)).op)).obj
          ((tensorPullback (g k)).obj F))
    (hr : ∀ {j k : {j : I // i₀ ≤ j}} (f : j ⟶ k),
      (Classical.choose (exists_tensorPullbackAdjunction (g j))).unit.app F ≫
        (pushforward (g j)).map (r f) ≫
        (pushforwardComp
          (D.map (homOfLE (x := j.val) (y := k.val) (leOfHom f)).op) (g j)).hom.app
          ((tensorPullback (g k)).obj F) ≫
        (pushforwardCongr (f := D.map (homOfLE (x := j.val) (y := k.val)
          (leOfHom f)).op ≫ g j) (g := g k)
          (by rw [hg j, hg k, ← D.map_comp]; rfl)).hom.app
          ((tensorPullback (g k)).obj F) =
      (Classical.choose (exists_tensorPullbackAdjunction (g k))).unit.app F)
    (t : ∀ j : {j : I // i₀ ≤ j}, (tensorPullback (g j)).obj F ⟶
      (pushforward (s.π.app (op j.val))).obj
        ((tensorPullback (s.π.app (op i₀))).obj F))
    (ht : ∀ j,
      (Classical.choose (exists_tensorPullbackAdjunction (g j))).unit.app F ≫
        (pushforward (g j)).map (t j) ≫
        (pushforwardComp (s.π.app (op j.val)) (g j)).hom.app
          ((tensorPullback (s.π.app (op i₀))).obj F) ≫
        (pushforwardCongr (f := s.π.app (op j.val) ≫ g j)
          (g := s.π.app (op i₀))
          (by rw [hg j]; exact s.w (homOfLE j.property).op)).hom.app
          ((tensorPullback (s.π.app (op i₀))).obj F) =
      (Classical.choose (exists_tensorPullbackAdjunction (s.π.app (op i₀)))).unit.app F)
    (M : {j : I // i₀ ≤ j} ⥤ AddCommGrpCat.{u})
    (e : ∀ j : {j : I // i₀ ≤ j}, M.obj j ≅
      AddCommGrpCat.of (Γ((tensorPullback (g j)).obj F, ⊤)))
    (hM : ∀ {j k : {j : I // i₀ ≤ j}} (f : j ⟶ k) (x : M.obj j),
      (e k).hom (M.map f x) =
        ((tensorPullback (g k)).obj F).presheaf.map (eqToHom (by simp)).op
          ((r f).app ⊤ ((e j).hom x)))
    (q : colimit M ⟶ AddCommGrpCat.of
      (Γ((tensorPullback (s.π.app (op i₀))).obj F, ⊤)))
    (hq : ∀ (j : {j : I // i₀ ≤ j}) (x : M.obj j), q (colimit.ι M j x) =
      ((tensorPullback (s.π.app (op i₀))).obj F).presheaf.map (eqToHom (by simp)).op
        ((t j).app ⊤ ((e j).hom x))) :
    IsIso q ∧
      ∀ (j : {j : I // i₀ ≤ j}) (x : M.obj j), q (colimit.ι M j x) = 0 →
        ∃ k : {j : I // i₀ ≤ j}, ∃ (f : j ⟶ k), M.map f x = 0 := by
  sorry

end AlgebraicGeometry
