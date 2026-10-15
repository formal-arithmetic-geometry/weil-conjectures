/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Sections of constant module sheaves

Source: Stacks Project, sites-modules, Tags 093J, 093K, 093L
(blueprint: lem-weil-pbc-constant-module-section-properties).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TensorProduct

namespace CategoryTheory

/-- Sections of constant modules are exact, commute with finitely presented tensor
factors by the canonical comparison, naturally in both modules and the site object,
and preserve flatness over a commutative Noetherian ring.
Source: Stacks Project, sites-modules, Tags 093J, 093K, 093L
(blueprint: lem-weil-pbc-constant-module-section-properties).

Proof: (1) Sheafification is exact and kernels of sheaves are sectionwise kernels
(lem-weil-pbc-sheafification-exact). The module sheafification interface
(lem-pc-sites-module-sheafification-interface) identifies the underlying abelian
sheafification. A set-theoretic section of a surjective module map induces a section
of its constant sheaf of sets, hence surjectivity on every object's sections.
(2) Choose a finite presentation of Q. Tensor right exactness
(lem-weil-pbc-tensor-right-exact) and (1), together with preservation of finite
sums by evaluation, identify the same cokernel on both sides. The displayed formula
on pure tensors specifies the canonical comparison. All maps used commute with
module morphisms and restrictions, giving the two naturality identities.
(3) A finitely generated ideal is finitely presented over a Noetherian ring
(lem-sc-noetherian-finite-module-finite-presentation). Apply (2) to that ideal;
flatness of M and (1) make its tensor inclusion injective on sections. Use tensor
symmetry and the finitely generated ideal flatness criterion
(lem-weil-pbc-flat-fg-ideal-criterion) to conclude flatness of the sections. -/
theorem constantModule_section_properties
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Type (u)) [CommRing R] [IsNoetherianRing R] :
    (∀ (A B D : ModuleCat.{u} R) (f : A ⟶ B) (g : B ⟶ D),
      Function.Injective f → Function.Exact f g → Function.Surjective g →
      ∀ U : C,
        Function.Injective (((constantSheaf J (ModuleCat.{u} R)).map f).hom.app (op U)) ∧
        Function.Exact (((constantSheaf J (ModuleCat.{u} R)).map f).hom.app (op U))
          (((constantSheaf J (ModuleCat.{u} R)).map g).hom.app (op U)) ∧
        Function.Surjective (((constantSheaf J (ModuleCat.{u} R)).map g).hom.app (op U))) ∧
    (∃ e : ∀ (M Q : ModuleCat.{u} R), Module.FinitePresentation R Q → ∀ U : C,
        (((constantSheaf J (ModuleCat.{u} R)).obj M).obj.obj (op U) ⊗[R] Q) ≃ₗ[R]
          ((constantSheaf J (ModuleCat.{u} R)).obj
            (ModuleCat.of R (M ⊗[R] Q))).obj.obj (op U),
      (∀ (M Q : ModuleCat.{u} R) (hQ : Module.FinitePresentation R Q)
          (U : C) (s : ((constantSheaf J (ModuleCat.{u} R)).obj M).obj.obj (op U)) (q : Q),
        e M Q hQ U (s ⊗ₜ[R] q) =
          (((constantSheaf J (ModuleCat.{u} R)).map
            (ModuleCat.ofHom ((TensorProduct.mk R M Q).flip q))).hom.app (op U)) s) ∧
      (∀ (M M' Q Q' : ModuleCat.{u} R)
          (hQ : Module.FinitePresentation R Q) (hQ' : Module.FinitePresentation R Q')
          (f : M ⟶ M') (g : Q ⟶ Q') (U : C)
          (z : ((constantSheaf J (ModuleCat.{u} R)).obj M).obj.obj (op U) ⊗[R] Q),
        e M' Q' hQ' U
            (TensorProduct.map
              (((constantSheaf J (ModuleCat.{u} R)).map f).hom.app (op U)).hom g.hom z) =
          (((constantSheaf J (ModuleCat.{u} R)).map
            (ModuleCat.ofHom (TensorProduct.map f.hom g.hom))).hom.app (op U))
              (e M Q hQ U z)) ∧
      (∀ (M Q : ModuleCat.{u} R) (hQ : Module.FinitePresentation R Q)
          (U V : C) (h : V ⟶ U)
          (z : ((constantSheaf J (ModuleCat.{u} R)).obj M).obj.obj (op U) ⊗[R] Q),
        e M Q hQ V
            (TensorProduct.map (((constantSheaf J (ModuleCat.{u} R)).obj M).obj.map h.op).hom
              (LinearMap.id : Q →ₗ[R] Q) z) =
          (((constantSheaf J (ModuleCat.{u} R)).obj
            (ModuleCat.of R (M ⊗[R] Q))).obj.map h.op) (e M Q hQ U z))) ∧
    (∀ (M : ModuleCat.{u} R), Module.Flat R M → ∀ U : C,
      Module.Flat R (((constantSheaf J (ModuleCat.{u} R)).obj M).obj.obj (op U))) := by
  sorry

end CategoryTheory
