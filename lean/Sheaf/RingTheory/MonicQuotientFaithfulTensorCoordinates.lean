module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # Tensor coordinates for a positive-length monic quotient

Source: Stacks Project, Tags 04GG (proof of (10) implies (1)) and 00HB, parts (2) and (4).
The coordinate argument is the agent-extracted finite-free argument in the DAG.
(blueprint: lem-sfb-monic-quotient-faithful-tensor-coordinates)
-/

@[expose] public section

universe u v w z

open scoped TensorProduct
open Polynomial

namespace AdjoinRoot

/-- A quotient by a monic equation of specified positive length has its power basis,
natural tensor coordinates, and preserves and reflects exactness. The polynomial `f` is
introduced by its defining equation `hf`; `AdjoinRoot f` is literally `R[X]/(f)` with its
canonical algebra structure and `root f` is the class of `X`. The coefficient maps are
`e.coord i`. The displayed equivalences are the composites of Mathlib's basis tensor
coordinates with the finite-support/function equivalence; thus they are actual specified
linear isomorphisms, rather than arbitrary maps.

Source: Stacks Project, Tag 04GG, proof of (10) implies (1), the finite-free monic quotient;
Tag 00HB, parts (2) and (4), and the agent-extracted coordinate argument.
(blueprint: lem-sfb-monic-quotient-faithful-tensor-coordinates)

Proof plan:
1. If `R` is nonzero, `hf` makes `f` monic of degree `d`; use
   `AdjoinRoot.powerBasis'` (lem-weil-pbc-monic-quotient-free). If `R` is zero, both the
   quotient and `Fin d → R` are singleton modules, giving a basis with the same index.
2. Uniqueness of basis coefficients gives the linear maps `e.coord i`, the reconstruction
   formula, and the Kronecker-delta coefficients on the powers of `root f`.
3. The bilinear map `(b,x) ↦ (e.coord i b • x)_i` induces the tensor coordinate map.
   The sum of the tensors of basis vectors with the entries gives its linear inverse.
4. The delta formula proves that their composite on a tuple is the identity. Conversely,
   reconstruction proves the other composite on pure tensors, hence on all tensors.
5. For an `R`-linear `h`, both naturality composites send a pure tensor to the tuple
   `(e.coord i b • h x)_i`. Pure tensors generate, so the composites agree.
6. These isomorphisms identify tensor exactness with coordinatewise exactness. Exactness
   of the original maps supplies a preimage in each coordinate. Conversely, put a kernel
   element in coordinate zero, using `hd`, and read coordinate zero of a preimage. The
   zero-composite hypothesis gives the other inclusion in each direction.
7. This is precisely faithful flatness by Tag 00HB. If `R` is zero, every unital module is
   zero, so all formulas and the exactness equivalence still hold, with index `Fin d`.
-/
theorem exists_monicQuotient_faithful_tensor_coordinates
    (R : Type u) [CommRing R] (d : ℕ) (hd : 1 ≤ d) (a : Fin d → R)
    (f : R[X]) (hf : f = X ^ d + ∑ i : Fin d, C (a i) * X ^ (i : ℕ)) :
    ∃ e : Module.Basis (Fin d) R (AdjoinRoot f),
      (∀ i : Fin d, e i = root f ^ (i : ℕ)) ∧
      (∀ b : AdjoinRoot f, b = ∑ i : Fin d, e.coord i b • root f ^ (i : ℕ)) ∧
      (∀ (N : Type v) [AddCommGroup N] [Module R N],
        (∀ (b : AdjoinRoot f) (x : N) (i : Fin d),
          ((TensorProduct.equivFinsuppOfBasisLeft e).trans
            (Finsupp.linearEquivFunOnFinite R N (Fin d))) (b ⊗ₜ[R] x) i =
              e.coord i b • x) ∧
        (∀ x : Fin d → N,
          ((TensorProduct.equivFinsuppOfBasisLeft e).trans
            (Finsupp.linearEquivFunOnFinite R N (Fin d))).symm x =
              ∑ i : Fin d, (root f ^ (i : ℕ)) ⊗ₜ[R] x i)) ∧
      (∀ (N : Type v) [AddCommGroup N] [Module R N]
          (N' : Type w) [AddCommGroup N'] [Module R N']
          (h : N →ₗ[R] N') (q : AdjoinRoot f ⊗[R] N) (i : Fin d),
        ((TensorProduct.equivFinsuppOfBasisLeft e).trans
          (Finsupp.linearEquivFunOnFinite R N' (Fin d))) (h.lTensor (AdjoinRoot f) q) i =
            h (((TensorProduct.equivFinsuppOfBasisLeft e).trans
              (Finsupp.linearEquivFunOnFinite R N (Fin d))) q i)) ∧
      (∀ (N₁ : Type v) [AddCommGroup N₁] [Module R N₁]
          (N₂ : Type w) [AddCommGroup N₂] [Module R N₂]
          (N₃ : Type z) [AddCommGroup N₃] [Module R N₃]
          (h : N₁ →ₗ[R] N₂) (k : N₂ →ₗ[R] N₃), k.comp h = 0 →
        (Function.Exact (h.lTensor (AdjoinRoot f)) (k.lTensor (AdjoinRoot f)) ↔
          LinearMap.range h = LinearMap.ker k)) ∧
      RingHom.FaithfullyFlat (algebraMap R (AdjoinRoot f)) := by
  classical
  obtain ⟨e, he⟩ : ∃ e : Module.Basis (Fin d) R (AdjoinRoot f),
      ∀ i : Fin d, e i = root f ^ (i : ℕ) := by
    cases subsingleton_or_nontrivial R with
    | inl hR =>
      have : Subsingleton (AdjoinRoot f) := Module.subsingleton R _
      refine ⟨Module.Basis.ofEquivFun (LinearEquiv.ofSubsingleton (R := R) _ _), ?_⟩
      intro i
      exact Subsingleton.elim _ _
    | inr hR =>
      have hm : f.Monic := hf ▸ monic_X_pow_add (degree_sum_fin_lt a)
      have hdeg : f.natDegree = d := by
        rw [hf, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
        simpa using degree_sum_fin_lt a
      subst d
      exact ⟨(powerBasis' hm).basis, (powerBasis' hm).basis_eq_pow⟩
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hflat : Module.FaithfullyFlat R (AdjoinRoot f) :=
    Module.FaithfullyFlat.of_linearEquiv R (Fin d →₀ R) e.repr
  refine ⟨e, he, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    simpa only [Module.Basis.coord_apply, ← he] using (e.sum_repr b).symm
  · intro N _ _
    constructor
    · intro b x i
      exact TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply e b x i
    · intro x
      rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply,
        TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
        Finsupp.sum_fintype _ _ (by simp)]
      simp only [Finsupp.linearEquivFunOnFinite_symm_apply, he]
  · intro N _ _ N' _ _ h q i
    induction q using TensorProduct.induction_on with
    | zero => simp
    | tmul b x =>
      simpa only [LinearMap.lTensor_tmul, LinearEquiv.trans_apply,
        Finsupp.linearEquivFunOnFinite_apply,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
        Module.Basis.coord_apply] using (h.map_smul (e.repr b i) x).symm
    | add q q' hq hq' =>
      simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) hq hq'
  · intro N₁ _ _ N₂ _ _ N₃ _ _ h k _
    rw [Module.FaithfullyFlat.lTensor_exact_iff_exact R (AdjoinRoot f),
      LinearMap.exact_iff]
    exact eq_comm
  · exact RingHom.faithfullyFlat_algebraMap_iff.mpr hflat

end AdjoinRoot
