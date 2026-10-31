/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Kaehler.TensorProduct
import WeilConjectures.AlgebraicGeometry.DirectedColimitBaseChangeElementwise

/-!
# Descent of unramified algebra maps along directed ring colimits

Source: Stacks Project, Algebra, Tag 0C4F, `lemma-colimit-unramified`
(blueprint: lem-trf-colimit-unramified-algebra).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

/-- A finite type algebra map which becomes unramified over a directed ring colimit
becomes unramified at a stage. Unramified is written as finite type and vanishing of
Kähler differentials. The tensor map is `id ⊗ φ₀`, with precisely the algebra structures
induced by the colimit coprojection and by the transition from `i₀`.

Source: Stacks Project, Algebra, Tag 0C4F, `lemma-colimit-unramified`
(blueprint: lem-trf-colimit-unramified-algebra).

Proof:
1. Choose finitely many generators `x₁, …, xₘ` of `C₀` over `B₀`, with `m = 0` allowed.
   Tensor expansion shows that `1 ⊗ xᵣ` generate every `Cᵢ` over `Bᵢ` and `C` over `B`.
2. The universal derivation of `def-weil-pbc-kahler-differentials` and the Leibniz rule
   show that the `d xᵣ` generate `Ω[C₀⁄B₀]`; similarly their base changes generate each
   `Ω[Cᵢ⁄Bᵢ]`. For no generators the modules already vanish.
3. Identify `B_T ⊗[B₀] C₀` with `T ⊗[A₀] C₀` by
   `(t ⊗ b) ⊗ c ↦ t ⊗ φ₀(b)c`, with inverse `t ⊗ c ↦ (t ⊗ 1) ⊗ c`.
   Identify `C_T ⊗[C₀] Ω[C₀⁄B₀]` with `T ⊗[A₀] Ω[C₀⁄B₀]` by the analogous formulas.
   The balancing relations verify both pairs of inverse maps.
4. Apply `lem-weil-pbc-kahler-differentials-base-change` (Stacks 00RV) and step 3.
   The resulting isomorphism sends `1 ⊗ d xᵣ` to `d (1 ⊗ xᵣ)`.
   Since the differential module over the colimit is zero, all `1 ⊗ d xᵣ` vanish there.
5. Clause (2) of `lem-weil-pbc-directed-colimit-base-change-elementwise`, applied to
   `Ω[C₀⁄B₀]`, kills each of these finitely many elements at a stage. Directedness gives
   one common later stage (use `i₀` when `m = 0`). The transition maps preserve zero.
6. Step 4 at that stage kills every differential generator, so the differential module
   is zero. Step 1 gives finite type, proving both conditions of the conclusion.
-/
theorem exists_unramified_stage_of_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F] (i₀ : I)
    (B₀ : Type v) (C₀ : Type w) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) (hfg : φ₀.toRingHom.FiniteType)
    (hunramified :
      letI : Algebra (F.obj i₀) ↥(colimit F) := (colimit.ι F i₀).hom.toAlgebra
      (Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) ↥(colimit F)) φ₀).toRingHom.FiniteType ∧
        Subsingleton (@KaehlerDifferential
          (↥(colimit F) ⊗[F.obj i₀] B₀) (↥(colimit F) ⊗[F.obj i₀] C₀) _ _
          (Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) ↥(colimit F)) φ₀).toRingHom.toAlgebra)) :
    ∃ (i : I) (h : i₀ ≤ i),
      letI : Algebra (F.obj i₀) (F.obj i) := (F.map (homOfLE h)).hom.toAlgebra
      (Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj i)) φ₀).toRingHom.FiniteType ∧
        Subsingleton (@KaehlerDifferential
          ((F.obj i) ⊗[F.obj i₀] B₀) ((F.obj i) ⊗[F.obj i₀] C₀) _ _
          (Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj i)) φ₀).toRingHom.toAlgebra) := by
  sorry

end Algebra
