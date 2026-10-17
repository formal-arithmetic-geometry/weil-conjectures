/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections

/-!
# A finite test for vanishing after pullback from an affine open

Source: Stacks Project, Properties, Tag 01PB; Schemes, Tags 01I9 and 01IA;
Sheaves, Tag 0097.
(blueprint: lem-pc-affine-finite-type-pullback-zero-test).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A finite family of sections on an affine open tests vanishing after every pullback.
Source: Stacks Project, Properties, Tag 01PB; Schemes, Tags 01I9 and 01IA;
Sheaves, Tag 0097.
(blueprint: lem-pc-affine-finite-type-pullback-zero-test).

Proof: finite type and quasi-coherence imply that F(V) is a finite module over O(V).
Choose a finite spanning family. For any g, naturality of its pullback adjunction unit
identifies the image of each pulled-back generator with the pullback of its image
under δ. Hence the hypothesis kills all generators. On any affine open A contained
in g⁻¹(V), the affine pullback-sections comparison identifies sections of g*F with
F(V) tensor O(A); pure tensors of the spanning family generate this module. The
pulled-back map therefore vanishes on A. Affine opens contained in an arbitrary
W cover W. Naturality of δ with respect to restriction, followed by separatedness
of the target sheaf, implies its component on W is zero. No finiteness assumption
on G or g is required. An empty spanning family covers the zero module, and the
empty affine open causes no exception. -/
theorem exists_affine_finiteType_pullback_zero_test
    {Y : Scheme.{u}} (F : Y.Modules) (hF_ft : F.IsFiniteType)
    (hF_qc : F.IsQuasicoherent) (V : Y.Opens) (hV : IsAffineOpen V) :
    ∃ s : Finset Γ(F, V),
      ∀ (G : Y.Modules) (_hG_qc : G.IsQuasicoherent) (δ : F ⟶ G)
        (X : Scheme.{u}) (g : X ⟶ Y),
        (∀ x ∈ s, ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app G).val.app
          (op V) (δ.app V x) = 0) →
        ∀ (W : X.Opens), W ≤ g ⁻¹ᵁ V → ((tensorPullback g).map δ).app W = 0 := by
  classical
  let : F.IsFiniteType := hF_ft
  let : F.IsQuasicoherent := hF_qc
  have := finite_sections_of_finiteType F hV
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule Γ(Y, V) Γ(F, V)).FG)
  refine ⟨s, ?_⟩
  intro G hG_qc δ X g hzero
  let k : Γ(F, V) →ₗ[Γ(Y, V)]
      Γ((pushforward g).obj ((tensorPullback g).obj G), V) :=
    (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app G).val.app
      (op V)).hom.comp (δ.val.app (op V)).hom
  have hk : ∀ x, k x = 0 := by
    have hspan : Submodule.span Γ(Y, V) (s : Set Γ(F, V)) ≤ LinearMap.ker k :=
      Submodule.span_le.mpr (fun x hx ↦ hzero x hx)
    rw [hs] at hspan
    exact fun x ↦ hspan (Submodule.mem_top)
  have haff (U : X.affineOpens) (hUV : U.1 ≤ g ⁻¹ᵁ V) :
      ((tensorPullback g).map δ).app U.1 = 0 := by
    let : Algebra Γ(Y, V) Γ(X, U.1) := (g.appLE V U.1 hUV).hom.toAlgebra
    obtain ⟨c, hc, _, ht, hn⟩ :=
      exists_tensorPullback_affine_sections g ⟨V, hV⟩ U hUV
    ext z
    obtain ⟨t, rfl⟩ := (hc F hF_qc).surjective z
    rw [hn F G hF_qc hG_qc δ t]
    change c G hG_qc (TensorProduct.map (δ.val.app (op V)).hom LinearMap.id t) = 0
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, ht]
      change b • ((tensorPullback g).obj G).presheaf.map (homOfLE hUV).op (k x) = 0
      rw [hk, map_zero, smul_zero]
    | add t t' ht ht' => simp_all only [map_add, add_zero]
  intro W hWV
  ext z
  let N := (tensorPullback g).obj G
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i : {U : X.affineOpens // U.1 ≤ W} ↦ i.1.1) W
    (fun i ↦ homOfLE i.2) ?_ _ _ (fun i ↦ ?_)
  · intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
    exact Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUW⟩, hxU⟩
  · have hn := ((tensorPullback g).map δ).val.naturality (homOfLE i.2).op
    have he := congrArg (fun q ↦ q z) hn
    change ((tensorPullback g).map δ).app i.1.1
        (((tensorPullback g).obj F).presheaf.map (homOfLE i.2).op z) =
      N.presheaf.map (homOfLE i.2).op (((tensorPullback g).map δ).app W z) at he
    change N.presheaf.map (homOfLE i.2).op
      (((tensorPullback g).map δ).app W z) = N.presheaf.map (homOfLE i.2).op 0
    rw [← he, haff i.1 (i.2.trans hWV)]
    simp

end AlgebraicGeometry.Scheme.Modules
