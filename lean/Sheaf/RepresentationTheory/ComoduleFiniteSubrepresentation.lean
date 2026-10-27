/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Finite subsets of rational modules lie in finite-dimensional submodules

Source: Milne, Algebraic Groups (2017), Proposition 4.7 and Corollary 4.8,
printed pp.86--87. (blueprint: lem-sfb-comodule-finite-subrepresentation)

The coordinate Hopf algebra and right-coaction laws are the existing HopfAction
constructions. The vector space may have any dimension and an independent universe.
The restricted coaction is specified by its commutation with the subspace inclusion.
-/

set_option autoImplicit false

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.RationalRepresentation

/-- The invariant vectors of a right coordinate coaction.
Source: Milne, Algebraic Groups, Chapter 4, coaction description of invariants.
(blueprint: lem-sfb-comodule-finite-subrepresentation) -/
def coactionFixedVectors (k : Type u) [Field k] (H : Scheme.{u})
    [H.Over (Spec (.of k))] [GrpObj (H.asOver (Spec (.of k)))] [IsAffine H]
    (V : Type v) [AddCommGroup V] [Module k V]
    (ρ : V →ₗ[k] V ⊗[k] Γ(H, ⊤)) : Set V :=
  {x | ρ x = x ⊗ₜ[k] (1 : Γ(H, ⊤))}

/-- Every finite subset of a rational module is contained in a finite-dimensional
rational submodule, with its restricted coaction.
Source: Milne, Algebraic Groups (2017), Proposition 4.7 and Corollary 4.8,
printed pp.86--87. (blueprint: lem-sfb-comodule-finite-subrepresentation)

Proof:
1. Choose a basis (e_i) of k[H] using lem-weil-pbc-vector-space-free and
   def-weil-pbc-free-module. Its coefficient functionals lambda_j are linear.
2. The universal property of def-weil-pbc-module-tensor-product writes each tensor
   uniquely as a finitely supported sum of m_i tensor e_i. Applying id tensor
   lambda_j extracts m_j. The unit and associativity identifications are the usual
   maps on pure tensors, whose spans are the entire tensor products.
3. Expand rho(s) for each s in S and span all its finitely many coefficients to
   obtain W. It is finite-dimensional by def-weil-finite-dimensional-subspace.
   Counitality expresses each s as the sum of epsilon(e_i) times its coefficients,
   proving S is contained in W. For empty S this span is zero.
4. Apply coassociativity to s and extract the last coefficient e_j. This gives
   rho(v_sj) = sum_i v_si tensor (id tensor lambda_j)(Delta(e_i)). Thus each
   spanning vector, and hence W, maps into the image of W tensor k[H].
5. Coefficient extraction proves inclusion tensor id is injective: all coefficients
   of a tensor in its kernel vanish. Repeating proves the triple-tensor inclusion
   injective as well, with no finiteness assumption on V or k[H].
6. Take the unique preimages of rho(w) under inclusion tensor id to define rho_W;
   uniqueness proves linearity and the restriction equation. Compose its two
   coassociativity expressions with the injective triple-tensor inclusion to reduce
   to coassociativity of rho. Compose the counit expression with the inclusion to
   reduce to counitality of rho. Cancel these injections to obtain both laws on W.
-/
theorem exists_finiteDimensional_subcomodule (k : Type u) [Field k] (H : Scheme.{u})
    [H.Over (Spec (.of k))] [GrpObj (H.asOver (Spec (.of k)))] [IsAffine H]
    (V : Type v) [AddCommGroup V] [Module k V]
    (ρ : V →ₗ[k] V ⊗[k] Γ(H, ⊤))
    (hcoassoc : HopfAction.Coassociative k Γ(H, ⊤) V ρ)
    (hcounit : HopfAction.Counital k Γ(H, ⊤) V ρ)
    (S : Set V) (hS : S.Finite) :
    ∃ W : Submodule k V, FiniteDimensional k W ∧ S ⊆ (W : Set V) ∧
      ∃ ρW : W →ₗ[k] W ⊗[k] Γ(H, ⊤),
        HopfAction.Coassociative k Γ(H, ⊤) W ρW ∧
        HopfAction.Counital k Γ(H, ⊤) W ρW ∧
        W.subtype.rTensor Γ(H, ⊤) ∘ₗ ρW = ρ ∘ₗ W.subtype := by
  sorry

end AlgebraicGeometry.RationalRepresentation
