/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.InvertibleFpTensorModels
import WeilConjectures.AlgebraicGeometry.FinitePresentationLimitIsomorphismDescent
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Mathlib.RingTheory.PicardGroup

/-! # Invertible modules descend along affine transition limits

Source: Stacks Project, Limits, Tag 0B8W, lemma-descend-invertible-modules,
clause (2) (blueprint: lem-trf-invertible-affine-limit-descent).

-- Stage-2 ownership: Q44 re-attaches this existing statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry

open Scheme.Modules

/-- For quasi-coherent modules, a tensor inverse forces local freeness of rank one.
On each affine open the section modules are invertible modules over its coordinate ring.
They are finite projective and their ranks multiply to one, so each has rank one.
Source: Stacks Project, Modules, Tags 0B8K and 0B8M, lemmas `lemma-invertible` and
`lemma-invertible-is-locally-free-rank-1`. -/
private theorem isInvertible_of_tensorIsoUnit {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (e : M ⊗ N ≅ 𝟙_ X.Modules) :
    M.IsInvertible := by
  have hlf : M.IsFiniteLocallyFreeOfRank 1 := by
    apply isFiniteLocallyFreeOfRank_of_isAffineOpen M
    intro U hU
    let t : TensorProduct Γ(X, U) Γ(M, U) Γ(N, U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
      LinearEquiv.ofBijective (tensorSectionsMap M N U)
        ((quasiCoherent_tensor_product_affine_sections M N).2 U hU) ≪≫ₗ
          appLinearEquivOfIso e U
    have := Module.Invertible.left t
    have := Module.Invertible.right t
    refine ⟨Module.finitePresentation_of_projective _ _, inferInstance, fun p ↦ ?_⟩
    have hr := congrFun (Module.rankAtStalk_eq_of_equiv t) p
    have : Nontrivial Γ(X, U) := p.nontrivial
    rw [Module.rankAtStalk_tensorProduct, Pi.mul_apply, Module.rankAtStalk_self] at hr
    exact Nat.eq_one_of_mul_eq_one_right hr
  have := (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one M).2 hlf
  exact IsInvertible.of_sheafOfModules M

/-- An invertible module on an inverse limit of quasi-compact, quasi-separated
schemes with affine transition morphisms descends to an invertible module at a
finite stage.

Source: Stacks Project, Limits, Tag 0B8W, lemma-descend-invertible-modules,
clause (2). Proof (blueprint: lem-trf-invertible-affine-limit-descent):

1. Take the dual tensor inverse of `L` using `lem-pc-tensor-dual-invertible`.
   Both factors are locally rank-one free and therefore finitely presented.
2. Apply clause (1) of `lem-trf-fp-modules-affine-limit-descent` to both factors
   and move them to a common upper stage. Finite presentation is preserved by
   `lem-pc-tensor-pullback-finite-presentation`.
3. Their tensor product is finitely presented: tensor their finite free local
   presentations and quotient by the relations from both factors. The structure
   module is also finitely presented. This uses the sheaf tensor and cokernels of
   `def-pur-sheaf-tensor-product` and `def-weil-sheaf-of-modules-category`.
4. The comparison `lem-weil-pbc-module-pullback-tensor` identifies the pulled-back
   tensor with `L` tensored with its inverse. Descend evaluation and its inverse
   by clause (2) of `lem-trf-fp-modules-affine-limit-descent` to a common stage.
5. Descend the two inverse identities by clause (3) of that same lemma. At a
   common later stage the evaluation map is thus an isomorphism.
6. Pullback's tensor comparison and the tensor-inverse characterization of
   `def-sc-invertible-module` make the descended first factor invertible.
   The composition comparison of `def-pc-module-pullback` identifies its
   limit pullback with `L`. -/
theorem invertible_affine_limit_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c)
    (L : c.pt.Modules) [L.IsInvertible] :
    ∃ i : I, ∃ L_i : (D.obj (op i)).Modules,
      L_i.IsInvertible ∧
        Nonempty (((Scheme.Modules.tensorPullback (c.π.app (op i))).obj L_i) ≅ L) := by
  classical
  obtain ⟨_, _, _, _, i, A, B, hA, hB, a, b, hAB, hunit, heval⟩ :=
    invertible_fp_tensor_models D c hc L
  let ε := (Classical.choose (module_pullback_tensor (c.π.app (op i))) A B).hom ≫
    (a.hom ⊗ₘ b.hom) ≫ dualEvaluation L
  have : IsIso ε := heval
  have := (tensorPullbackObjUnitToUnit_isIso (c.π.app (op i))).1
  let φ : (tensorPullback (c.π.app (op i))).obj (A ⊗ B) ≅
      (tensorPullback (c.π.app (op i))).obj (𝟙_ (D.obj (op i)).Modules) :=
    asIso ε ≪≫ (asIso (tensorPullbackObjUnitToUnit (c.π.app (op i)))).symm
  obtain ⟨k, hik, f, g, hfg, hgf, _, _⟩ :=
    finitePresentation_iso_descent_affineLimit D c hc i (A ⊗ B)
      (𝟙_ (D.obj (op i)).Modules) hAB hunit φ
  let q := D.map (homOfLE hik).op
  let A' := (tensorPullback q).obj A
  let B' := (tensorPullback q).obj B
  let t : (tensorPullback q).obj (A ⊗ B) ≅
      (tensorPullback q).obj (𝟙_ (D.obj (op i)).Modules) :=
    ⟨f, g, hfg, hgf⟩
  have := (tensorPullbackObjUnitToUnit_isIso q).1
  let e : A' ⊗ B' ≅ 𝟙_ (D.obj (op k)).Modules :=
    (Classical.choose (module_pullback_tensor q) A B).symm ≪≫ t ≪≫
      asIso (tensorPullbackObjUnitToUnit q)
  have : A.IsFinitePresentation := hA
  have : B.IsFinitePresentation := hB
  have : A'.IsFinitePresentation := isFinitePresentation_tensorPullback q A
  have : B'.IsFinitePresentation := isFinitePresentation_tensorPullback q B
  exact ⟨k, A', isInvertible_of_tensorIsoUnit A' B' e,
    ⟨affineLimitTensorPullbackComparison D c hik A ≪≫ a⟩⟩

end AlgebraicGeometry
