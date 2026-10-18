module

public import Sheaf.RingTheory.IsMittagLeffler
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.RingTheory.MittagLefflerHomSystems
import Sheaf.RingTheory.FinitePresentationTensorProducts

/-!
# Mittag--Leffler characterization by eventual tensor-kernel domination

Source: Stacks Project, Algebra, Tag 059E, proposition-ML-characterization,
equivalence of conditions (2) and the tensor-product Mittag--Leffler condition
(blueprint: lem-trf-mittag-leffler-eventual-domination).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

/-- A directed finitely presented module presentation has the tensor-kernel
Mittag--Leffler property exactly when its stage maps eventually dominate the
canonical maps to the colimit.

For maps `a : P → Q` and `b : P → Q'`, domination is rendered by the displayed
condition `∀ L, ker (a ⊗ id_L) ≤ ker (b ⊗ id_L)`. The cocone `c` supplies the
canonical maps `f_i` from each stage and `hc` identifies its vertex as the colimit;
`f_ij` is `F.map (homOfLE hij)`. The stage modules live in an arbitrary universe
`max u v w`; the index sets of the Mittag--Leffler condition range over that same
universe (the size used by `hom_images_stabilize_of_isMittagLeffler`), and the test
modules over `max u v w t`. Empty test-module families and zero modules are included
by the universal quantifiers; the directed index is nonempty, as in Stacks.

Source: Stacks Project, Algebra, Tags 059E and 059M.
(blueprint: lem-trf-mittag-leffler-eventual-domination)

Proof:
1. Assume `M = c.pt` is Mittag--Leffler and fix `i`. Put `N = ∏_{s ∈ I} M_s`. By
   lem-trf-mittag-leffler-hom-systems (`hom_images_stabilize_of_isMittagLeffler`,
   applied with this single target) there is `j ≥ i` such that for every `k ≥ j`
   the images of `Hom(M_j, N) → Hom(M_i, N)` and `Hom(M_k, N) → Hom(M_i, N)` agree.
2. For `k ≥ j`, project along `N → M_j`: the images of `Hom(M_j, M_j)` and
   `Hom(M_k, M_j)` in `Hom(M_i, M_j)` agree. The identity of `M_j` maps to `f_ij`,
   so there is `h_k : M_k → M_j` with `h_k ∘ f_ik = f_ij`.
3. Let `L` be a module and `x ∈ ker (f_i ⊗ id_L)`. Tensor commutes with the colimit
   (lem-weil-pbc-tensor-commutes-with-colimits), so by the elementwise description
   (lem-weil-pbc-filtered-colimit-modules-elementwise) `(f_ik ⊗ id_L) x = 0` for some
   `k ≥ i`; pass to a common upper bound `k' ≥ k, j`.
4. By functoriality of tensor products (def-weil-pbc-module-tensor-product),
   `f_ij ⊗ id_L = (h_k' ⊗ id_L) ∘ (f_ik' ⊗ id_L)`, so `x ∈ ker (f_ij ⊗ id_L)`:
   `f_ij` dominates `f_i`.
5. Conversely assume eventual domination; fix a family `(Q_α)` and `x` in the kernel
   of `θ : M ⊗ ∏ Q_α → ∏ (M ⊗ Q_α)`. By the tensor-colimit comparison and the
   elementwise criterion, `x = (f_i ⊗ id) z` for some `i` and
   `z ∈ M_i ⊗ ∏ Q_α`.
6. Choose `j ≥ i` with `f_ij` dominating `f_i`. The `α`-component `z_α` of `z`
   satisfies `(f_i ⊗ id_{Q_α}) z_α = 0`, hence `(f_ij ⊗ id_{Q_α}) z_α = 0` by
   domination, for every `α`.
7. Since `M_j` is finitely presented, `M_j ⊗ ∏ Q_α → ∏ (M_j ⊗ Q_α)` is bijective
   (lem-trf-finite-presentation-tensor-products), so `(f_ij ⊗ id) z = 0`. As
   `f_i = f_j ∘ f_ij`, `x = 0`; thus `θ` is injective for every family and `M` is
   Mittag--Leffler (def-trf-mittag-leffler-module). -/
theorem isMittagLeffler_iff_eventual_tensor_kernel
    (R : Type u) [CommRing R]
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ ModuleCat.{max u v w} R)
    [∀ i : I, Module.FinitePresentation R (F.obj i)]
    (c : Cocone F) (hc : IsColimit c) :
    Module.IsMittagLeffler.{u, max u v w, max u v w, t} R c.pt ↔
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        ∀ (L : Type (max u v w t)) [AddCommGroup L] [Module R L],
          LinearMap.ker (((c.ι.app i).hom.rTensor L)) ≤
            LinearMap.ker (((F.map (homOfLE hij)).hom.rTensor L)) := by
  sorry

end Module
