module

public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures

/-! # Finite coactions descend along directed coalgebra colimits

Source: Milne, Algebraic Groups (2017), Theorem 9.37, printed p.178,
the passage to the directed limit.
(blueprint: lem-sfb-directed-coalgebra-comodule-descent)

Coactions are expressed by their two linear-map identities, including the tensor
associator and right unitor. The vector-space colimit is any colimit cocone.
-/

set_option autoImplicit false

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Coalgebra

/-- A directed vector-space colimit carries a unique compatible coalgebra structure;
finite-dimensional coactions descend, and colinearity is detected at a later stage.
Source: Milne, Algebraic Groups (2017), Theorem 9.37, printed p.178,
the directed-limit passage.
(blueprint: lem-sfb-directed-coalgebra-comodule-descent)

Proof:
1. The maps (iota_i tensor iota_i) Delta_i form a cocone, as do the counits.
   The colimit universal property (def-weil-pbc-category-colimit) gives unique
   Delta and epsilon. Precomposition with each iota_i verifies coassociativity
   and both counit laws, so these maps give the unique compatible coalgebra.
2. Apply lem-weil-pbc-filtered-colimit-tensor-varying-rings to the constant ring
   system k and the two module systems D_i. The underlying abelian colimit
   (def-weil-directed-colimit-abelian-groups) has scalar action a[x_i]=[a x_i]
   and is a vector-space colimit. The constant ring colimit is k, since the
   index set is nonempty and directed. Thus colim (D_i tensor D_i) is D tensor D.
   The lemma lem-weil-pbc-filtered-colimit-modules-elementwise detects the
   vanishing of any tensor at a later stage, without assuming injectivity.
3. Choose a finite basis e_a of M (def-weil-finite-dimensional-subspace).
   Tensor coordinates (def-weil-pbc-module-tensor-product) write uniquely
   rho(e_b)=sum_a e_a tensor c_ab. The coaction equations become
   Delta(c_ab)=sum_s c_as tensor c_sb and epsilon(c_ab)=delta_ab.
4. Represent the finitely many c_ab at stages using the module elementwise
   lemma; take a common upper bound i and lifts c_ab^i. They define a linear
   map lifting rho. Its counit equations already hold in the fixed field k.
   If M=0, choose any i and the zero map.
5. Each defect Delta_i(c_ab^i)-sum_s c_as^i tensor c_sb^i vanishes in D tensor D.
   Step 2 kills it at a later stage. A common upper bound j kills all finitely
   many defects. Transport the coefficients to j; preservation of Delta and
   epsilon gives a genuine coaction whose extension is rho.
6. For a linear map a between finite-dimensional D_i-comodules, choose bases
   and write a(e_b)=sum_s A_sb f_s, with coaction matrices c_tb and d_rs.
   The colinearity defects are sum_s A_sb d_rs-sum_t A_rt c_tb in D_i.
   Colinearity over D kills their images. The module elementwise lemma kills
   all these finitely many defects at one j>=i, proving colinearity there.
   Transported maps satisfy the coaction laws by applying 1 tensor u tensor u
   and preservation of epsilon. If either basis is empty, take j=i.
   No transition map is cancelled and no dimension bound on D_i is used. -/
theorem directed_colimit_coalgebra_comodule_descent
    {k : Type u} [Field k] {I : Type v} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (F : I ⥤ ModuleCat.{v} k)
    [∀ i : I, Coalgebra k (F.obj i)]
    (hΔ : ∀ (i j : I) (h : i ≤ j),
      Coalgebra.comul (R := k) (A := F.obj j) ∘ₗ (F.map (homOfLE h)).hom =
        TensorProduct.map (F.map (homOfLE h)).hom (F.map (homOfLE h)).hom ∘ₗ
          Coalgebra.comul (R := k) (A := F.obj i))
    (hε : ∀ (i j : I) (h : i ≤ j),
      Coalgebra.counit (R := k) (A := F.obj j) ∘ₗ (F.map (homOfLE h)).hom =
        Coalgebra.counit (R := k) (A := F.obj i))
    (c : Cocone F) (hc : IsColimit c) :
    ∃ d : Coalgebra k c.pt,
      (∀ i : I,
        d.comul ∘ₗ (c.ι.app i).hom =
          TensorProduct.map (c.ι.app i).hom (c.ι.app i).hom ∘ₗ
            Coalgebra.comul (R := k) (A := F.obj i)) ∧
      (∀ i : I, d.counit ∘ₗ (c.ι.app i).hom =
        Coalgebra.counit (R := k) (A := F.obj i)) ∧
      (∀ d' : Coalgebra k c.pt,
        (∀ i : I, d'.comul ∘ₗ (c.ι.app i).hom =
          TensorProduct.map (c.ι.app i).hom (c.ι.app i).hom ∘ₗ
            Coalgebra.comul (R := k) (A := F.obj i)) →
        (∀ i : I, d'.counit ∘ₗ (c.ι.app i).hom =
          Coalgebra.counit (R := k) (A := F.obj i)) → d' = d) ∧
      (∀ (M : Type w) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
        (ρ : M →ₗ[k] M ⊗[k] c.pt),
        (TensorProduct.assoc k M c.pt c.pt).toLinearMap ∘ₗ ρ.rTensor c.pt ∘ₗ ρ =
          d.comul.lTensor M ∘ₗ ρ →
        (TensorProduct.rid k M).toLinearMap ∘ₗ d.counit.lTensor M ∘ₗ ρ = LinearMap.id →
        ∃ (i : I) (ρi : M →ₗ[k] M ⊗[k] F.obj i),
          (TensorProduct.assoc k M (F.obj i) (F.obj i)).toLinearMap ∘ₗ
              ρi.rTensor (F.obj i) ∘ₗ ρi =
            (Coalgebra.comul (R := k) (A := F.obj i)).lTensor M ∘ₗ ρi ∧
          (TensorProduct.rid k M).toLinearMap ∘ₗ
              (Coalgebra.counit (R := k) (A := F.obj i)).lTensor M ∘ₗ ρi = LinearMap.id ∧
          ρ = (c.ι.app i).hom.lTensor M ∘ₗ ρi) ∧
      (∀ (i : I) (M : Type w) (N : Type t)
        [AddCommGroup M] [Module k M] [FiniteDimensional k M]
        [AddCommGroup N] [Module k N] [FiniteDimensional k N]
        (ρM : M →ₗ[k] M ⊗[k] F.obj i) (ρN : N →ₗ[k] N ⊗[k] F.obj i)
        (a : M →ₗ[k] N),
        (TensorProduct.assoc k M (F.obj i) (F.obj i)).toLinearMap ∘ₗ
            ρM.rTensor (F.obj i) ∘ₗ ρM =
          (Coalgebra.comul (R := k) (A := F.obj i)).lTensor M ∘ₗ ρM →
        (TensorProduct.rid k M).toLinearMap ∘ₗ
            (Coalgebra.counit (R := k) (A := F.obj i)).lTensor M ∘ₗ ρM = LinearMap.id →
        (TensorProduct.assoc k N (F.obj i) (F.obj i)).toLinearMap ∘ₗ
            ρN.rTensor (F.obj i) ∘ₗ ρN =
          (Coalgebra.comul (R := k) (A := F.obj i)).lTensor N ∘ₗ ρN →
        (TensorProduct.rid k N).toLinearMap ∘ₗ
            (Coalgebra.counit (R := k) (A := F.obj i)).lTensor N ∘ₗ ρN = LinearMap.id →
        (c.ι.app i).hom.lTensor N ∘ₗ ρN ∘ₗ a =
          a.rTensor c.pt ∘ₗ (c.ι.app i).hom.lTensor M ∘ₗ ρM →
        ∃ (j : I) (h : i ≤ j),
          (F.map (homOfLE h)).hom.lTensor N ∘ₗ ρN ∘ₗ a =
            a.rTensor (F.obj j) ∘ₗ (F.map (homOfLE h)).hom.lTensor M ∘ₗ ρM) := by
  sorry

end Coalgebra
