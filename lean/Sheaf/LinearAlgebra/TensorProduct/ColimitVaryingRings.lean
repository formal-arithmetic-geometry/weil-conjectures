/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Tensor products and directed colimits with varying coefficient rings

Source: Stacks Project, Sheaves, Tag 007K, algebraic content; Algebra, Tag 00DD,
second direct proof (blueprint: lem-weil-pbc-filtered-colimit-tensor-varying-rings).
-/

universe z u v w v' w'

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace TensorProduct

/-- Tensoring two semilinear directed systems commutes with their colimits, including
uniqueness and naturality of the comparison. Source: Stacks Project, Tags 007K and 00DD
(blueprint: lem-weil-pbc-filtered-colimit-tensor-varying-rings).

The additive equivalences `e` identify the objects of the tensor diagram with the actual
stage tensor products; `hT` specifies its transition maps. The three action equations
specify the induced actions on the colimits. The last clause states naturality for any
second pair of systems over the same ring diagram, with the induced colimit maps specified
by their equations on coprojections. Thus no choice of a presentation of a tensor diagram
or of its colimit affects the assertion.

Proof:
1. To define each colimit action, move the scalar and module representatives to a
   common stage and multiply there. Semilinearity and passage to a further common stage
   make this independent of representatives; the module laws hold at a common stage.
   This applies also to the tensor system. The balanced maps on pure tensors are
   additive and compatible with transitions by
   semilinearity. The colimit universal property (`def-weil-pbc-category-colimit`)
   gives the unique additive comparison; the prescribed actions make it linear.
2. For surjectivity, represent both factors at stages and move them to a common later
   stage. Each pure tensor is then the image of a tensor from that stage. Pure tensors
   generate, so the comparison is surjective.
3. For injectivity, move a finite sum representing an element to a common stage. If its
   image vanishes, only finitely many additivity and balancing relations are needed.
   Move all their coefficients and factors to a further common stage. There the relation
   vanishes already, so its class in the colimit is zero. This extends the direct
   tensor-colimit construction of Tag 00DD to varying rings using common stages.
4. Equivalently, the inverse sends tensors represented at a common stage to their stage
   tensor class; the preceding argument proves independence and balancing. Both inverse
   identities and the naturality square hold on the generating stage pure tensors. -/
theorem exists_unique_colimit_tensor_varying_rings
    {I : Type z} [Preorder I] [IsDirected I (· ≤ ·)]
    (A : I ⥤ CommRingCat.{u}) (M : I ⥤ AddCommGrpCat.{v})
    (N : I ⥤ AddCommGrpCat.{w}) (T : I ⥤ AddCommGrpCat.{max v w})
    [HasColimit A] [HasColimit M] [HasColimit N] [HasColimit T]
    [∀ i : I, Module (A.obj i) (M.obj i)]
    [∀ i : I, Module (A.obj i) (N.obj i)]
    [Module ↥(colimit A) (↥(colimit M))] [Module ↥(colimit A) (↥(colimit N))]
    [Module ↥(colimit A) (↥(colimit T))]
    (hM : ∀ {i j : I} (f : i ⟶ j) (a : A.obj i) (m : M.obj i),
      M.map f (a • m) = A.map f a • M.map f m)
    (hN : ∀ {i j : I} (f : i ⟶ j) (a : A.obj i) (n : N.obj i),
      N.map f (a • n) = A.map f a • N.map f n)
    (e : ∀ i : I, (M.obj i ⊗[A.obj i] N.obj i) ≃+ T.obj i)
    (hT : ∀ {i j : I} (f : i ⟶ j) (m : M.obj i) (n : N.obj i),
      T.map f (e i (m ⊗ₜ[A.obj i] n)) =
        e j (M.map f m ⊗ₜ[A.obj j] N.map f n))
    (hAM : ∀ (i : I) (a : A.obj i) (m : M.obj i),
      colimit.ι A i a • colimit.ι M i m = colimit.ι M i (a • m))
    (hAN : ∀ (i : I) (a : A.obj i) (n : N.obj i),
      colimit.ι A i a • colimit.ι N i n = colimit.ι N i (a • n))
    (hAT : ∀ (i : I) (a : A.obj i) (t : M.obj i ⊗[A.obj i] N.obj i),
      colimit.ι A i a • colimit.ι T i (e i t) = colimit.ι T i (e i (a • t))) :
    ∃ ψ : ↥(colimit T) →ₗ[↥(colimit A)] (↥(colimit M) ⊗[↥(colimit A)] ↥(colimit N)),
      (∀ (i : I) (m : M.obj i) (n : N.obj i),
        ψ (colimit.ι T i (e i (m ⊗ₜ[A.obj i] n))) =
          colimit.ι M i m ⊗ₜ[↥(colimit A)] colimit.ι N i n) ∧
      (∀ χ : ↥(colimit T) →+ (↥(colimit M) ⊗[↥(colimit A)] ↥(colimit N)),
        (∀ (i : I) (m : M.obj i) (n : N.obj i),
          χ (colimit.ι T i (e i (m ⊗ₜ[A.obj i] n))) =
            colimit.ι M i m ⊗ₜ[↥(colimit A)] colimit.ι N i n) →
        χ = ψ.toAddMonoidHom) ∧
      Function.Bijective ψ ∧
      (∀ (M' : I ⥤ AddCommGrpCat.{v'}) (N' : I ⥤ AddCommGrpCat.{w'})
        (T' : I ⥤ AddCommGrpCat.{max v' w'})
        [HasColimit M'] [HasColimit N'] [HasColimit T']
        [∀ i : I, Module (A.obj i) (M'.obj i)]
        [∀ i : I, Module (A.obj i) (N'.obj i)]
        [Module ↥(colimit A) (↥(colimit M'))] [Module ↥(colimit A) (↥(colimit N'))]
        [Module ↥(colimit A) (↥(colimit T'))]
        (e' : ∀ i : I, (M'.obj i ⊗[A.obj i] N'.obj i) ≃+ T'.obj i)
        (f : ∀ i : I, M.obj i →ₗ[A.obj i] M'.obj i)
        (g : ∀ i : I, N.obj i →ₗ[A.obj i] N'.obj i)
        (F : ↥(colimit M) →ₗ[↥(colimit A)] ↥(colimit M'))
        (G : ↥(colimit N) →ₗ[↥(colimit A)] ↥(colimit N'))
        (H : ↥(colimit T) →ₗ[↥(colimit A)] ↥(colimit T'))
        (ψ' : ↥(colimit T') →ₗ[↥(colimit A)] (↥(colimit M') ⊗[↥(colimit A)] ↥(colimit N'))),
        (∀ {i j : I} (a : i ⟶ j) (r : A.obj i) (m : M'.obj i),
          M'.map a (r • m) = A.map a r • M'.map a m) →
        (∀ {i j : I} (a : i ⟶ j) (r : A.obj i) (n : N'.obj i),
          N'.map a (r • n) = A.map a r • N'.map a n) →
        (∀ {i j : I} (a : i ⟶ j) (m : M'.obj i) (n : N'.obj i),
          T'.map a (e' i (m ⊗ₜ[A.obj i] n)) =
            e' j (M'.map a m ⊗ₜ[A.obj j] N'.map a n)) →
        (∀ (i : I) (r : A.obj i) (m : M'.obj i),
          colimit.ι A i r • colimit.ι M' i m = colimit.ι M' i (r • m)) →
        (∀ (i : I) (r : A.obj i) (n : N'.obj i),
          colimit.ι A i r • colimit.ι N' i n = colimit.ι N' i (r • n)) →
        (∀ (i : I) (r : A.obj i) (t : M'.obj i ⊗[A.obj i] N'.obj i),
          colimit.ι A i r • colimit.ι T' i (e' i t) =
            colimit.ι T' i (e' i (r • t))) →
        (∀ {i j : I} (a : i ⟶ j) (m : M.obj i),
          f j (M.map a m) = M'.map a (f i m)) →
        (∀ {i j : I} (a : i ⟶ j) (n : N.obj i),
          g j (N.map a n) = N'.map a (g i n)) →
        (∀ (i : I) (m : M.obj i), F (colimit.ι M i m) = colimit.ι M' i (f i m)) →
        (∀ (i : I) (n : N.obj i), G (colimit.ι N i n) = colimit.ι N' i (g i n)) →
        (∀ (i : I) (m : M.obj i) (n : N.obj i),
          H (colimit.ι T i (e i (m ⊗ₜ[A.obj i] n))) =
            colimit.ι T' i (e' i (f i m ⊗ₜ[A.obj i] g i n))) →
        (∀ (i : I) (m : M'.obj i) (n : N'.obj i),
          ψ' (colimit.ι T' i (e' i (m ⊗ₜ[A.obj i] n))) =
            colimit.ι M' i m ⊗ₜ[↥(colimit A)] colimit.ι N' i n) →
        ψ'.comp H = (TensorProduct.map F G).comp ψ) := by
  sorry

end TensorProduct
