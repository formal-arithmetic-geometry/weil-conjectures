/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Sheaf.AlgebraicGeometry.CompletionInternalHomQuotient
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentSheafHom
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Affine tensor dictionary for compatible internal-Hom sections

Source: Stacks Project, Tags 0882, 087W and 00MA.
(blueprint: lem-weil-pbc-completion-internal-hom-affine-tensor-dictionary).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Affine quotient systems identify the evaluation map with a completed-ring-linear
map on the tensor product of the module of linear maps. On `1 ⊗ h` it is base change of h.
The last clause identifies each specified local evaluation equation with one equation
in the tensor-product Hom module; it asserts no injectivity or surjectivity of beta.

Source: Stacks Project, Cohomology of Schemes, Tag 0882, affine-local proof;
Tag 087W and Algebra, Tag 00MA.
(blueprint: lem-weil-pbc-completion-internal-hom-affine-tensor-dictionary).

Proof:
1. Set A = O_X(U), J = I(U), N = G(U), M = F(U), H = Hom_A(N,M).
   Affine tilde and sections identify the internal Hom with H. Coherence makes
   N, M, H finite. Ideal products and quotient sections identify each level with
   P/J^(n+1)P for P = N, M, H, including the canonical transition maps.
2. Surjectivity of the quotient on H-sections and unique factorization through
   the quotient of G identify the given e_n with quotient evaluation, by he.
   Thus it maps compatible H-section families to compatible local morphisms.
3. The affine formal-module equivalence identifies the latter with Hom over
   A-completion between N-completion and M-completion, acting componentwise.
   The compatible H-sections are H-completion. Tensor-completion equivalences
   c_H, c_N and c_M give rho to A-completion tensor H and conjugate the evaluation
   to beta into Hom(A-completion tensor N, A-completion tensor M).
4. Componentwise evaluation is A-completion-linear. On the image of h it is
   its completed map, which conjugates to baseChange h by naturality of c_N,c_M.
   This proves the generator equation. The compatible t, restricted to U, gives
   an element v in the same Hom module. The faithful affine equivalence and
   the quotient-section identifications give the last iff, in both directions.
   This proof does not use flat base change for Hom. -/
theorem completion_internal_hom_affine_tensor_dictionary {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F G : CoherentModules X)
    (e : ∀ n : ℕᵒᵖ,
      formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
        (R := X.toRingedSpace.sheaf) G.obj F.obj) ⟶
        SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) (formalModuleQuotient I (n.unop + 1) G.obj)
          (formalModuleQuotient I (n.unop + 1) F.obj))
    (he : ∀ n : ℕᵒᵖ,
        formalModuleQuotientπ I (n.unop + 1) (SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) G.obj F.obj) ≫
          e n ≫ SheafOfModules.homObjMap
            (R := X.toRingedSpace.sheaf) (formalModuleQuotientπ I (n.unop + 1) G.obj)
            (𝟙 (formalModuleQuotient I (n.unop + 1) F.obj)) =
        SheafOfModules.homObjMap
          (R := X.toRingedSpace.sheaf) (𝟙 G.obj) (formalModuleQuotientπ I (n.unop + 1) F.obj))
    (U : X.affineOpens) :
    let A := Γ(X, U.val)
    let B := AdicCompletion (I.ideal U) A
    let N := Γ(G.obj, U.val)
    let M := Γ(F.obj, U.val)
    ∃ ρ : {s : ∀ n : ℕᵒᵖ,
          (formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
            (R := X.toRingedSpace.sheaf) G.obj F.obj)).val.obj (op U.val) //
          ∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
            ((formalCompletionSystem I (SheafOfModules.homObj
              (R := X.toRingedSpace.sheaf) G.obj F.obj)).map f).val.app (op U.val)
              (s a) = s b} ≃ (B ⊗[A] (N →ₗ[A] M)),
    ∃ β : B ⊗[A] (N →ₗ[A] M) →ₗ[B] (B ⊗[A] N →ₗ[B] B ⊗[A] M),
      (∀ h : N →ₗ[A] M, β (1 ⊗ₜ[A] h) = LinearMap.baseChangeHom A B N M h) ∧
      ∀ (t : ∀ n : ℕᵒᵖ, formalModuleQuotient I (n.unop + 1) G.obj ⟶
        formalModuleQuotient I (n.unop + 1) F.obj),
        (∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
          t a ≫ (formalCompletionSystem I F.obj).map f =
            (formalCompletionSystem I G.obj).map f ≫ t b) →
        ∃ v : B ⊗[A] N →ₗ[B] B ⊗[A] M, ∀ s,
          (∀ n : ℕᵒᵖ, (e n).val.app (op U.val) (s.val n) =
            ((SheafOfModules.homObjSectionsEquiv (R := X.toRingedSpace.sheaf)
              (formalModuleQuotient I (n.unop + 1) G.obj)
              (formalModuleQuotient I (n.unop + 1) F.obj)).symm (t n)).val (op U.val)) ↔
            β (ρ s) = v := by
  sorry

end AlgebraicGeometry
