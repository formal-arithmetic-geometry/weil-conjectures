module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.LinearAlgebra.Trace

import Sheaf.RepresentationTheory.CharZeroDifferentiationHom
import Sheaf.AlgebraicGeometry.CharZeroSemisimpleGroupLie

/-! # The Casimir endomorphism of a semisimple algebraic group module

Source: Milne, Algebraic Groups (2017), Section 22c, printed pp.475--476,
Proposition 22.41, printed p.477, and Proposition 10.31, printed p.196.
(blueprint: lem-sfb-semisimple-group-casimir-trace)

The differential is specified on the canonical dual-number tangent points. The Casimir
endomorphism is specified as the actual sum of products for every trace-dual pair of bases.
No arbitrary operator or differential is supplied as a hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The differential image has nondegenerate trace form, and its Casimir sum is canonical,
equivariant, has trace its dimension, preserves rational submodules, and maps into any
rational submodule with trivial quotient. Nontrivial actions have positive-dimensional image.
Source: Milne, Section 22c, printed pp.475--476, Proposition 22.41, printed p.477,
and Proposition 10.31, printed p.196.
(blueprint: lem-sfb-semisimple-group-casimir-trace)

Proof:
1. lem-sfb-char-zero-differentiation-hom identifies the canonical differential and proves
   it is a Lie homomorphism. lem-sfb-char-zero-semisimple-group-lie makes its domain
   semisimple. Apply lem-sfb-semisimple-lie-surjective-image to its corestriction onto
   its image. The inclusion of this image in End(V) is faithful, so
   lem-sfb-faithful-semisimple-trace-form gives the required nondegeneracy.
2. Invert the Gram matrix of any basis to obtain its trace-dual basis. Under a change
   of basis by A, the dual changes by the inverse transpose. Expanding the sum of
   products and cancelling A times its inverse proves that the actual sum is unchanged.
3. Cyclicity of trace gives B([X,Y],Z) + B(Y,[X,Z]) = 0. If the coefficients of
   [X,e_i] are a_ji, those of [X,e^i] are -a_ij. Expanding [X,sum e_i e^i] cancels
   these terms after exchanging i and j. The morphism criterion in
   lem-sfb-char-zero-differentiation-hom promotes this commutation to the coaction square.
4. Each product has trace B(e_i,e^i) = 1. Linearity of trace gives the dimension.
   The empty sum is zero and the trace form on the zero image is nondegenerate.
5. If the image has dimension zero, dr = 0. Apply the same differentiation morphism
   criterion to the identity from the trivial representation to V. It makes the
   original coaction trivial. Contrapositively a nontrivial action has positive image.
6. For a rational submodule W, evaluate its coaction at 1 + epsilon x. The epsilon
   coefficient shows dr(x)W is contained in W. Thus every basis element, dual basis
   element, product and sum preserves W. If the quotient is trivial, its epsilon
   coefficient instead gives dr(x)V contained in W. Each product and its sum then
   maps V into W, including when the sum is empty.
-/
theorem semisimpleGroup_casimir_trace
    (F : Type u) [Field F] [IsAlgClosed F] [CharZero F]
    (G : Scheme.{u}) [G.Over (Spec (.of F))]
    [GrpObj (G.asOver (Spec (.of F)))] [IsAffine G]
    (hG : IsSemisimpleGroupScheme (G.asOver (Spec (.of F))))
    (V : Type v) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (α : V →ₗ[F] V ⊗[F] Γ(G, ⊤))
    (hcoassoc : HopfAction.Coassociative F Γ(G, ⊤) V α)
    (hcounit : HopfAction.Counital F Γ(G, ⊤) V α) :
    ∃ dr : GrpObj.Lie (G.asOver (Spec (.of F))) →ₗ[F] Module.End F V,
      (∀ x : GrpObj.Lie (G.asOver (Spec (.of F))),
        ∃ g : Γ(G, ⊤) →ₐ[F] DualNumber F,
          g.toRingHom = ((GrpObj.lieEquivTangent (G.asOver (Spec (.of F))) x).val.left.appTop ≫
            (Scheme.ΓSpecIso (.of (DualNumber F))).hom).hom ∧
          ∀ v : V, g.toLinearMap.lTensor V (α v) =
            v ⊗ₜ[F] (1 : DualNumber F) + dr x v ⊗ₜ[F] DualNumber.eps) ∧
      (∀ X : LinearMap.range dr,
        (∀ Y : LinearMap.range dr,
          LinearMap.trace F V (X.val * Y.val) = 0) → X = 0) ∧
      ∃ c : Module.End F V,
        (∀ b : Module.Basis (Fin (Module.finrank F (LinearMap.range dr))) F (LinearMap.range dr),
          ∃ d : Module.Basis (Fin (Module.finrank F (LinearMap.range dr))) F (LinearMap.range dr),
            ∀ i j, LinearMap.trace F V ((b i).val * (d j).val) = if i = j then 1 else 0) ∧
        (∀ b d : Module.Basis (Fin (Module.finrank F (LinearMap.range dr))) F (LinearMap.range dr),
          (∀ i j, LinearMap.trace F V ((b i).val * (d j).val) = if i = j then 1 else 0) →
          c = ∑ i, (b i).val * (d i).val) ∧
        α ∘ₗ c = c.rTensor Γ(G, ⊤) ∘ₗ α ∧
        LinearMap.trace F V c = (Module.finrank F (LinearMap.range dr) : F) ∧
        (α ≠ (TensorProduct.mk F V Γ(G, ⊤)).flip 1 →
          0 < Module.finrank F (LinearMap.range dr)) ∧
        (∀ W : Submodule F V,
          @RationalHighestWeight.IsStable F _ (Grp.mk (G.asOver (Spec (.of F))))
            (inferInstanceAs (IsAffine G)) V _ _ α W →
          (∀ w ∈ W, c w ∈ W) ∧
          ((∀ v : V, W.mkQ.rTensor Γ(G, ⊤) (α v) =
            W.mkQ v ⊗ₜ[F] (1 : Γ(G, ⊤))) → ∀ v : V, c v ∈ W)) ∧
        (LinearMap.range dr = ⊥ → c = 0) := by
  sorry

end AlgebraicGeometry
