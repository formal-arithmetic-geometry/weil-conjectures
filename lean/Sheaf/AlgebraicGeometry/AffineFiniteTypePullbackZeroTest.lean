/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import all Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections

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
  have hfinite : Module.Finite Γ(Y, V) Γ(F, V) :=
    finite_sections_of_finiteType F hV
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := Γ(Y, V)) (M := Γ(F, V))
  let s : Finset Γ(F, V) := Finset.univ.image v
  refine ⟨s, ?_⟩
  intro G hG δ X g hs W hW
  have hgen (x : Γ(F, V)) :
      ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app G).val.app
        (op V) (δ.app V x) = 0 := by
    have hx : x ∈ Submodule.span (Γ(Y, V)) (Set.range v) := by
      rw [hv]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact hs (v i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    | zero => simp only [map_zero]
    | add a b _ _ ha hb =>
        rw [map_add, map_add]
        rw [ha, hb, add_zero]
    | smul r a _ ha =>
        rw [Scheme.Modules.Hom.app_smul δ]
        change (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app G).val.app
          (op V)).hom (r • ((δ.app V).hom a)) = 0
        rw [(((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app G).val.app
          (op V)).hom.map_smul, ha, smul_zero]
  have hzero (A : X.affineOpens) (hA : A.1 ≤ g ⁻¹ᵁ V) :
      ((tensorPullback g).map δ).app A.1 = 0 := by
    let : Algebra Γ(Y, V) Γ(X, A.1) := (g.appLE V A.1 hA).hom.toAlgebra
    let : ∀ M : Y.Modules, Module Γ(Y, V) Γ((tensorPullback g).obj M, A.1) :=
      fun M ↦ Module.compHom _ (g.appLE V A.1 hA).hom
    obtain ⟨c, hbij, _, hpure, hnat⟩ :=
      exists_tensorPullback_affine_sections g ⟨V, hV⟩ A hA
    ext x
    change ((tensorPullback g).map δ).app A.1 x = 0
    obtain ⟨t, rfl⟩ := (hbij F hF_qc).surjective x
    rw [hnat F G hF_qc hG δ]
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x b =>
        rw [TensorProduct.map_tmul, LinearMap.id_apply, hpure]
        change b • ((tensorPullback g).obj G).presheaf.map (homOfLE hA).op
          (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app G).val.app
            (op V) (δ.app V x)) = 0
        rw [hgen x, map_zero, smul_zero]
    | add t t' ht ht' =>
        simp only [map_add, ht, ht', add_zero]
  ext x
  let M := (tensorPullback g).obj F
  let N := (tensorPullback g).obj G
  let φ : M ⟶ N := (tensorPullback g).map δ
  let S : Sieve W :=
    ⟨fun {U} _ ↦ ∃ A : X.affineOpens, U ≤ A.1 ∧ A.1 ≤ W,
      fun {U U'} _ ⟨A, hUA, hAW⟩ j ↦ ⟨A, (leOfHom j).trans hUA, hAW⟩⟩
  have hS : S ∈ Opens.grothendieckTopology X W := by
    intro p hp
    obtain ⟨A, hA, hpA, hAW⟩ := exists_isAffineOpen_mem_and_subset hp
    exact ⟨A, homOfLE hAW, ⟨⟨A, hA⟩, le_rfl, hAW⟩, hpA⟩
  refine (N.isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext
    fun U i ⟨A, hUA, hAW⟩ ↦ ?_
  change N.presheaf.map i.op (φ.app W x) = N.presheaf.map i.op 0
  rw [map_zero, Subsingleton.elim i (homOfLE hUA ≫ homOfLE hAW),
    ← presheaf_map_map_apply]
  have hA : φ.app A.1 = 0 := hzero A (hAW.trans hW)
  rw [← Hom.app_presheaf_map φ, hA]
  change N.presheaf.map (homOfLE hUA).op (0 : Γ(N, A.1)) = 0
  exact map_zero _

end AlgebraicGeometry.Scheme.Modules
