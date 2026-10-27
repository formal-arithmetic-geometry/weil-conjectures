module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Order.Directed
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Sheaf.SecTraceFormula.TensorKernelFactorization

/-!
# A universal tensor witness gives eventual transition factorizations

Source: Stacks Project, Algebra, Tags 059L (`lemma-kernel-tensored-fp`),
059M (`proposition-ML-tensor`), 059E (`proposition-ML-characterization`),
059C (`lemma-domination-fp`), and 059D (`lemma-domination`).
(blueprint: lem-trf-tensor-witness-eventual-factorization)
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module

/-- A tensor-kernel witness universal for finitely presented tests yields one stage
through which every subsequent transition from the fixed source factors.

Source: Stacks Project, Algebra, Tags 059L and 059M, the universal kernel element
in the proof of (2) implies (1); Tag 059E, proof of (2) implies (3), using Tags
059C and 059D. (blueprint: lem-trf-tensor-witness-eventual-factorization)

Proof:
1. Tensoring the given colimit with `T` preserves it
   (lem-weil-pbc-tensor-commutes-with-colimits). Since the index is nonempty and
   directed, eventual vanishing in filtered module colimits
   (lem-weil-pbc-filtered-colimit-modules-elementwise) kills `z` at some `j ≥ i`.
2. For each finitely presented `Q` and each element `x` of the kernel at `i`,
   use its witnessing map `q : T →ₗ[R] Q`. Functoriality of tensor maps
   (def-weil-pbc-module-tensor-product), checked on pure tensors, shows that
   `f_ij ⊗ id_Q` kills `x`. For `k ≥ j`, cocone compatibility gives
   `ker (f_ik ⊗ id_Q) ≤ ker (u_i ⊗ id_Q) ≤ ker (f_ij ⊗ id_Q)`.
3. The cokernel of `f_ik` is finitely presented: choose a finite presentation
   `R^a → R^b → M_k → 0` and finite generators of `M_i` from
   def-sc-finitely-presented-module. Lift their images to vectors `w_r` in
   `R^b` and append these vectors to the relation matrix. Its cokernel is
   `M_k / f_ik(M_i)`: a vector maps to zero exactly when subtracting a linear
   combination of the `w_r` puts it in the old relation image.
4. Apply lem-trf-tensor-kernel-factorization to `f_ik` and `f_ij`, using the
   finite presentation in step 3 and the kernel inclusions in step 2. This
   gives `h : M_k →ₗ[R] M_j` with `f_ij = h.comp f_ik` for every `k ≥ j`.
No flatness, Mittag-Leffler, or countability condition is used. -/
theorem exists_eventual_factorization_of_tensor_witness
    (R : Type u) [CommRing R]
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ ModuleCat.{max u v w} R)
    [∀ s : I, Module.FinitePresentation R (F.obj s)]
    (c : Cocone F) (hc : IsColimit c) (i : I)
    (T : Type t) [AddCommGroup T] [Module R T]
    (z : F.obj i ⊗[R] T) (hz : (c.ι.app i).hom.rTensor T z = 0)
    (hwitness : ∀ (Q : Type (max u v w)) [AddCommGroup Q] [Module R Q]
      [Module.FinitePresentation R Q],
      ∀ x : F.obj i ⊗[R] Q, (c.ι.app i).hom.rTensor Q x = 0 →
        ∃ q : T →ₗ[R] Q, q.lTensor (F.obj i) z = x) :
    ∃ (j : I) (hij : i ≤ j), ∀ (k : I) (hjk : j ≤ k),
      ∃ h : F.obj k →ₗ[R] F.obj j,
        (F.map (homOfLE hij)).hom = h.comp (F.map (homOfLE (hij.trans hjk))).hom := by
  sorry

end Module
