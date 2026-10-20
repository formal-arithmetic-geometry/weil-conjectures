/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorStalkKernelSpan

/-!
# Local generators of an exterior tensor quotient kernel

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem local_span_realization {X : Scheme.{v}} (M : X.Modules)
    (Q : ∀ V : X.Opens, Submodule (X.presheaf.obj (op V)) (M.val.obj (op V)))
    (hres : ∀ {U V : X.Opens} (h : V ≤ U) (t : M.val.obj (op U)),
      t ∈ Q U → M.presheaf.map (homOfLE h).op t ∈ Q V)
    (x : X) (m : M.presheaf.stalk x)
    (hm : m ∈ Submodule.span (X.presheaf.stalk x)
      {z | ∃ (V : X.Opens) (hxV : x ∈ V) (t : M.val.obj (op V)),
        t ∈ Q V ∧ M.presheaf.germ V x hxV t = z}) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (t : M.val.obj (op V)),
      t ∈ Q V ∧ M.presheaf.germ V x hxV t = m := by
  induction hm using Submodule.span_induction with
  | mem z hz => exact hz
  | zero => exact ⟨⊤, by simp, 0, (Q ⊤).zero_mem, map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨U, hxU, a, ha, ea⟩ := ha
    obtain ⟨V, hxV, b, hb, eb⟩ := hb
    let W := U ⊓ V
    have hxW : x ∈ W := ⟨hxU, hxV⟩
    refine ⟨W, hxW, M.presheaf.map (homOfLE inf_le_left).op a +
      M.presheaf.map (homOfLE inf_le_right).op b,
      (Q W).add_mem (hres inf_le_left a ha) (hres inf_le_right b hb), ?_⟩
    rw [map_add, M.presheaf.germ_res_apply, M.presheaf.germ_res_apply, ea, eb]
  | smul c a _ ha =>
    obtain ⟨U, hxU, a, ha, ea⟩ := ha
    obtain ⟨V, hxV, c, ec⟩ := X.presheaf.exists_germ_eq c
    let W := U ⊓ V
    have hxW : x ∈ W := ⟨hxU, hxV⟩
    refine ⟨W, hxW, X.presheaf.map (homOfLE inf_le_right).op c •
      M.presheaf.map (homOfLE inf_le_left).op a,
      (Q W).smul_mem _ (hres inf_le_left a ha), ?_⟩
    rw [germ_smul, X.presheaf.germ_res_apply, M.presheaf.germ_res_apply, ec, ea]

set_option backward.isDefEq.respectTransparency false in
private theorem locally_mem_of_germ_mem_span {X : Scheme.{v}} (M : X.Modules)
    (Q : ∀ V : X.Opens, Submodule (X.presheaf.obj (op V)) (M.val.obj (op V)))
    (hres : ∀ {U V : X.Opens} (h : V ≤ U) (t : M.val.obj (op U)),
      t ∈ Q U → M.presheaf.map (homOfLE h).op t ∈ Q V)
    (U : X.Opens) (t : M.val.obj (op U)) (x : X) (hx : x ∈ U)
    (ht : M.presheaf.germ U x hx t ∈ Submodule.span (X.presheaf.stalk x)
      {z | ∃ (V : X.Opens) (hxV : x ∈ V) (a : M.val.obj (op V)),
        a ∈ Q V ∧ M.presheaf.germ V x hxV a = z}) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      M.presheaf.map (homOfLE hVU).op t ∈ Q V := by
  obtain ⟨V, hxV, a, ha, ea⟩ := local_span_realization M Q hres x _ ht
  obtain ⟨W, hxW, iV, iU, e⟩ := M.presheaf.germ_eq x hxV hx a t ea
  refine ⟨W, leOfHom iU, hxW, ?_⟩
  have h := hres (leOfHom iV) a ha
  have hV : homOfLE (leOfHom iV) = iV := Subsingleton.elim _ _
  have hU : homOfLE (leOfHom iU) = iU := Subsingleton.elim _ _
  rw [hU]
  rw [hV] at h
  exact e ▸ h

set_option maxHeartbeats 800000 in
-- Elaborating both sheafification naturality equalities needs the larger local budget.
set_option backward.isDefEq.respectTransparency false in
private theorem relationSpan_map {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (A : X.Modules) (r s : ℕ) {U V : X.Opens} (h : V ≤ U)
    (t : (exteriorPower A r ⊗ exteriorPower S.X₂ s).val.obj (op U))
    (ht : t ∈ exteriorTensorRelationSpan S A r s U) :
    (exteriorPower A r ⊗ exteriorPower S.X₂ s).val.map (homOfLE h).op t ∈
      exteriorTensorRelationSpan S A r s V := by
  induction ht using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, c, j, d, hj, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨fun i ↦ A.val.map (homOfLE h).op (a i),
      fun i ↦ S.X₂.val.map (homOfLE h).op (c i), j,
      S.X₁.val.map (homOfLE h).op d, ?_, ?_⟩
    · dsimp only
      rw [hj]
      exact (PresheafOfModules.naturality_apply S.f.val (homOfLE h).op d).symm
    · change (exteriorPower A r ⊗ exteriorPower S.X₂ s).presheaf.map
        (homOfLE h).op _ = _
      rw [tmulSection_map]
      apply congrArg₂ (tmulSection (M := exteriorPower A r) (N := exteriorPower S.X₂ s))
      · exact wedge_map (homOfLE h) a
      · exact wedge_map (homOfLE h) c
  | zero => rw [map_zero]; exact (exteriorTensorRelationSpan S A r s V).zero_mem
  | add a b _ _ ha hb =>
    rw [map_add]
    exact (exteriorTensorRelationSpan S A r s V).add_mem ha hb
  | smul c a _ ha =>
    rw [PresheafOfModules.map_smul]
    exact (exteriorTensorRelationSpan S A r s V).smul_mem _ ha

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorSheaf_comparison {X : Scheme.{v}} (M : X.Modules) (n : ℕ) :
    ∃ e : exteriorSheaf M n ≅ exteriorPower M n,
      ∀ (U : X.Opens) (a : Fin n → M.val.obj (op U)),
        e.hom.app U (exteriorSheafSection M n U a) = wedge a := by
  have hr {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
      exteriorSheafRestriction M n f =
        (PresheafOfModules.exteriorPower (R := X.presheaf) M.val n).map f := by
    apply ((Classical.choose_spec (exteriorSheafRestriction_existsUnique M n f)).2 _ ?_).symm
    intro a
    exact PresheafOfModules.ExteriorPower.map_ιMulti M.val n f a
  let e₀ : exteriorSheafPresheaf M n ≅
      PresheafOfModules.exteriorPower (R := X.presheaf) M.val n :=
    PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
      intro U V f
      change exteriorSheafRestriction M n f = _
      exact hr f)
  let e : exteriorSheaf M n ≅ exteriorPower M n :=
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso e₀
  refine ⟨e, ?_⟩
  intro U a
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit_naturality e₀.hom
  exact congrArg (fun f ↦ f.app (op U)
    (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a)) h

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorTensor_comparison {X : Scheme.{v}} (A B : X.Modules) (r s : ℕ) :
    ∃ e : exteriorSheaf A r ⊗ exteriorSheaf B s ≅ exteriorPower A r ⊗ exteriorPower B s,
      (∀ (U : X.Opens) (a : Fin r → A.val.obj (op U)) (b : Fin s → B.val.obj (op U)),
        e.hom.app U (tmulSection (exteriorSheafSection A r U a)
          (exteriorSheafSection B s U b)) = tmulSection (wedge a) (wedge b)) ∧
      (∀ (U : X.Opens) (a : Fin r → A.val.obj (op U)) (b : Fin s → B.val.obj (op U)),
        e.inv.app U (tmulSection (wedge a) (wedge b)) =
          tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf B s)
            (exteriorSheafSection A r U a) (exteriorSheafSection B s U b)) := by
  obtain ⟨eA, hA⟩ := exteriorSheaf_comparison A r
  obtain ⟨eB, hB⟩ := exteriorSheaf_comparison B s
  let e := eA ⊗ᵢ eB
  have he (U : X.Opens) (a : Fin r → A.val.obj (op U)) (b : Fin s → B.val.obj (op U)) :
      e.hom.app U (tmulSection (exteriorSheafSection A r U a)
        (exteriorSheafSection B s U b)) = tmulSection (wedge a) (wedge b) := by
    change (eA.hom ⊗ₘ eB.hom).app U _ = _
    rw [tensorHom_app_tmulSection, hA, hB]
  refine ⟨e, he, ?_⟩
  intro U a b
  rw [← he U a b]
  exact inv_app_hom_app_apply_of_iso e _

set_option backward.isDefEq.respectTransparency false in
/-- A section killed by an exterior tensor quotient is locally a linear combination of
pure wedge tensors with an argument in the image of the first map.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph; step 1 and the
finite-germ representation part of step 2 of `new-j1-exterior-tensor-kernel-relations`.
(blueprint: lem-sc-exterior-tensor-kernel-locally-spanned).

Proof: Fix a point x. Exactness on stalks identifies C_x with B_x/im(f_x). Present
exterior powers by their alternating multilinear generators and relations. Quotienting
B_x by im(f_x) adds precisely the relations that wedges with an argument in im(f_x)
vanish: multilinearity expands changes of representatives into these relations, so
the resulting quotient has the universal property of the exterior power of C_x.
Tensoring with the exterior power of A_x is right exact. Pure wedges span this first
factor, so the tensor kernel is spanned by the displayed pure wedge tensors. Exterior
powers and tensor products commute with stalks, since their presentations use finite
sums and finite tuples and commute with filtered colimits and scalar extension.
The formula for q identifies its stalk map with this quotient map. Express the germ
of t as a finite linear combination of these generators. Represent the finitely many
coefficients, wedge entries, and preimages under f_x on one common neighborhood V of
x contained in U. Shrink V to make every equation c_j=f(d) hold for sections, and
shrink once more to make the linear combination equal to the restriction of t.
The resulting equality proves membership in the displayed span. The assumption
s ≠ 0 excludes the degree-zero isomorphism case, handled separately by the caller.
For r=0 the empty wedge generates the first factor. At a zero stalk ring all modules
are zero; on an empty open there are no points to check. -/
theorem exteriorTensor_kernel_locally_mem_span {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (A : X.Modules) (r s : ℕ) (hs : s ≠ 0)
    (q : exteriorSheaf A r ⊗ exteriorSheaf S.X₂ s ⟶
      exteriorSheaf A r ⊗ exteriorSheaf S.X₃ s)
    (hq : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → S.X₂.val.obj (op U)),
      q.val.app (op U)
        (tmulSection (exteriorSheafSection A r U a)
          (exteriorSheafSection S.X₂ s U c)) =
        tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf S.X₃ s)
          (exteriorSheafSection A r U a)
          (exteriorSheafSection S.X₃ s U (fun i ↦ S.g.val.app (op U) (c i))))
    (U : X.Opens)
    (t : (exteriorSheaf A r ⊗ exteriorSheaf S.X₂ s).val.obj (op U))
    (ht : q.val.app (op U) t = 0) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      (exteriorSheaf A r ⊗ exteriorSheaf S.X₂ s).val.map (homOfLE hVU).op t ∈
        Submodule.span (X.presheaf.obj (op V))
          {z | ∃ (a : Fin r → A.val.obj (op V))
            (c : Fin s → S.X₂.val.obj (op V)) (j : Fin s)
            (d : S.X₁.val.obj (op V)), c j = S.f.val.app (op V) d ∧
              z = tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf S.X₂ s)
                (exteriorSheafSection A r V a)
                (exteriorSheafSection S.X₂ s V c)} := by
  obtain ⟨eB, _, hiB⟩ := exteriorTensor_comparison A S.X₂ r s
  obtain ⟨eC, heC, _⟩ := exteriorTensor_comparison A S.X₃ r s
  let q' := eB.inv ≫ q ≫ eC.hom
  have hq' (V : X.Opens) (a : Fin r → A.val.obj (op V))
      (c : Fin s → S.X₂.val.obj (op V)) :
      q'.app V (tmulSection (wedge a) (wedge c)) =
        tmulSection (wedge a) (wedge (fun i ↦ S.g.val.app (op V) (c i))) := by
    change eC.hom.app V (q.app V (eB.inv.app V _)) = _
    rw [hiB]
    exact (congrArg (eC.hom.app V) (hq V a c)).trans (heC V a _)
  have ht' : q'.app U (eB.hom.app U t) = 0 := by
    change eC.hom.app U (q.app U (eB.inv.app U (eB.hom.app U t))) = 0
    rw [inv_app_hom_app_apply_of_iso]
    change eC.hom.val.app (op U) (q.val.app (op U) t) = 0
    rw [ht, map_zero]
  let M := exteriorPower A r ⊗ exteriorPower S.X₂ s
  have hk : M.presheaf.germ U x hx (eB.hom.app U t) ∈
      LinearMap.ker (q'.stalkLinearMap x) := by
    rw [LinearMap.mem_ker, Hom.stalkLinearMap_germ]
    change (exteriorPower A r ⊗ exteriorPower S.X₃ s).presheaf.germ U x hx
      (q'.app U (eB.hom.app U t)) = 0
    rw [ht', map_zero]
  have hg := exteriorTensor_stalk_kernel_le_relationSpan S hS A r s hs q' hq' x hk
  obtain ⟨V, hVU, hxV, hV⟩ := locally_mem_of_germ_mem_span M
    (exteriorTensorRelationSpan S A r s)
    (fun h t ht ↦ relationSpan_map S A r s h t ht) U (eB.hom.app U t) x hx hg
  have htransfer (z : M.val.obj (op V)) (hz : z ∈ exteriorTensorRelationSpan S A r s V) :
      eB.inv.app V z ∈ Submodule.span (X.presheaf.obj (op V))
        {z | ∃ (a : Fin r → A.val.obj (op V))
          (c : Fin s → S.X₂.val.obj (op V)) (j : Fin s)
          (d : S.X₁.val.obj (op V)), c j = S.f.val.app (op V) d ∧
            z = tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf S.X₂ s)
              (exteriorSheafSection A r V a) (exteriorSheafSection S.X₂ s V c)} := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, c, j, d, hj, rfl⟩ := hz
      rw [hiB]
      exact Submodule.subset_span ⟨a, c, j, d, hj, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      rw [Hom.app_smul]
      exact Submodule.smul_mem _ c ha
  refine ⟨V, hVU, hxV, ?_⟩
  have h := htransfer _ hV
  have hn := Hom.app_presheaf_map eB.hom (homOfLE hVU) t
  change eB.inv.app V (M.presheaf.map (homOfLE hVU).op (eB.hom.app U t)) ∈ _ at h
  rw [← hn, inv_app_hom_app_apply_of_iso] at h
  exact h

end AlgebraicGeometry.Scheme.Modules
