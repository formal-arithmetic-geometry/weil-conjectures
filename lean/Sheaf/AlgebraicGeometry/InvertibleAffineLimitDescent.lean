/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.FinitePresentationAffineLimitDescent
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

/-! # Invertible modules descend along affine transition limits

Source: Stacks Project, Limits, Tag 0B8W, lemma-descend-invertible-modules,
clause (2) (blueprint: lem-trf-invertible-affine-limit-descent).

-- Stage-2 ownership: Q44 re-attaches this existing statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

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
  sorry

end AlgebraicGeometry
