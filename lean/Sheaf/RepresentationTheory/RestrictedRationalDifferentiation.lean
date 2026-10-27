module

public import Sheaf.Algebra.Lie.RestrictedPBWBasis
public import Sheaf.RingTheory.BialgebraDistributionTangentCalculus
public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Monoidal.Grp
import Sheaf.Algebra.Lie.AssociativeJacobsonIdentities
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.Algebra.Lie.OfAssociative

/-! # Restricted differentiation of rational coactions

Source: Milne, Algebraic Groups (2017), Theorem 10.23, Proposition 10.38,
Definition 10.39, Section 10l, Theorem 11.25, Proposition 11.26 and the paragraph
preceding Proposition 11.36, printed pp.193--194, 205--208, 217--218, 223
(blueprint: lem-sfb-restricted-rational-differentiation).

The Lie algebra and its commutator tangent bracket are the upstream objects.
The functional equivalence is fixed by the actual dual-number point, and the
invariant derivations and restricted powers are fixed by their coordinate formulas.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Restricted differentiation, functoriality and the unital restricted enveloping action,
including arbitrary dimensional rational modules.

Source: Milne, Theorem 10.23, Proposition 10.38, Definition 10.39, Section 10l,
Theorem 11.25, Proposition 11.26 and the paragraph preceding Proposition 11.36,
printed pp.193--194, 205--208, 217--218, 223
(blueprint: lem-sfb-restricted-rational-differentiation).

Proof:
1. Pull back the group diagrams (def-sc-group-scheme) to obtain the coordinate Hopf
   identities. The counit Leibniz rule describes exactly the dual-number points
   epsilon + eps*x. These identify the existing Lie algebra with tangentFunctionals.
   Send x to D_x=(id tensor x)Delta. Multiplicativity and Leibniz give its derivation
   rule; coassociativity gives invariance. The counit gives epsilon D_x=x.
   Conversely an invariant D has tangent functional epsilon D and D_(epsilon D)=D.
2. In the full dual convolution algebra (lem-sfb-convolution-linear-map-algebra),
   R_phi=(id tensor phi)Delta satisfies R_phi R_psi=R_(phi*psi), R_epsilon=id,
   and epsilon R_phi=phi. Thus R is an injective unital algebra map.
3. Expanding DE-ED cancels the mixed Leibniz terms. For a derivation D and
   multiplication M_a, [D,M_a]=M_(D(a)). The associative adjoint identity
   (lem-sfb-associative-jacobson-identities) yields [D^p,M_a]=M_(D^p(a)), hence
   D^p is a derivation. Composing the invariance equation proves invariance of
   DE and of D^p, hence also of the commutator.
4. Transport bracket and pth power through the bijection of step 1. The commutator
   Lie algebra (def-wf-lie-algebra) gives Jacobi. The two associative Jacobson
   identities give the restricted adjoint and sum axioms with the coefficients
   of lem-sfb-restricted-pbw-basis; (cD)^p=c^p D^p gives the scalar axiom.
   Injectivity reflects these identities, and step 2 identifies the operations
   with convolution commutator and convolution pth power.
5. In F[t,s]/(t^2,s^2), the points U=epsilon+tx and V=epsilon+sy have inverses
   epsilon-tx and epsilon-sy. Expanding UVU^-1 V^-1 gives
   epsilon+ts(x*y-y*x). Thus this is precisely the upstream tangent bracket,
   with the same sign even when p=2.
6. For f:H to K, the coordinate pullback preserves comultiplication and counit.
   Precomposition therefore preserves convolution, its commutator and pth power.
   This gives the formula for the existing differential and its restricted
   compatibility. For an automorphism, the differential of its inverse gives
   the inverse Lie map, proving the automorphism assertion.
7. For any counital coassociative alpha on W, put S_phi=(id tensor phi)alpha.
   Coassociativity gives S_phi S_psi=S_(phi*psi) and counitality gives
   S_epsilon=id. Step 4 gives both representation identities. Send tensor words
   to products of these operators and the empty word to id. Multilinearity
   constructs the tensor algebra map. Both kinds of defining relations map
   to zero, so it descends to the specified quotient as a unital algebra map.
   All tensor presentations are finite, with no restriction on dim W. -/
theorem restricted_rational_differentiation
    (F : Type u) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (H : Scheme.{u}) [H.Over (Spec (.of F))]
    [GrpObj (H.asOver (Spec (.of F)))] [IsAffine H]
    [LocallyOfFiniteType (H ↘ Spec (.of F))] [QuasiCompact (H ↘ Spec (.of F))] :
    ∃ (δ : GrpObj.Lie (H.asOver (Spec (.of F))) ≃ₗ[F]
        BialgebraDistribution.tangentFunctionals F Γ(H, ⊤))
      (D : GrpObj.Lie (H.asOver (Spec (.of F))) →ₗ⁅F⁆ Derivation F Γ(H, ⊤) Γ(H, ⊤))
      (q : GrpObj.Lie (H.asOver (Spec (.of F))) →
        GrpObj.Lie (H.asOver (Spec (.of F)))),
      (∀ (x : GrpObj.Lie (H.asOver (Spec (.of F)))) (a : Γ(H, ⊤)),
        (((GrpObj.lieEquivTangent (H.asOver (Spec (.of F))) x).val.left.appTop ≫
          (Scheme.ΓSpecIso (.of (DualNumber F))).hom).hom a) =
            TrivSqZeroExt.inl (Coalgebra.counit (R := F) a) + TrivSqZeroExt.inr ((δ x).1 a)) ∧
      (∀ x : GrpObj.Lie (H.asOver (Spec (.of F))),
        (D x).toLinearMap = BialgebraDistribution.tangentContraction F Γ(H, ⊤) (δ x).1) ∧
      (∀ x : GrpObj.Lie (H.asOver (Spec (.of F))),
        Coalgebra.counit.comp (D x).toLinearMap = (δ x).1) ∧
      Function.Injective D ∧
      (∀ d : Derivation F Γ(H, ⊤) Γ(H, ⊤),
        BialgebraDistribution.invariantDerivation F Γ(H, ⊤) d ↔ ∃ x, D x = d) ∧
      (∀ x y : GrpObj.Lie (H.asOver (Spec (.of F))),
        BialgebraDistribution.invariantDerivation F Γ(H, ⊤) ⁅D x, D y⁆) ∧
      LieAlgebra.IsRestrictedOperation F p q ∧
      (∀ x : GrpObj.Lie (H.asOver (Spec (.of F))),
        (D (q x)).toLinearMap = (D x).toLinearMap ^ p ∧
        BialgebraDistribution.invariantDerivation F Γ(H, ⊤) (D (q x))) ∧
      (∀ (f : H.asOver (Spec (.of F)) ≅ H.asOver (Spec (.of F))) [IsMonHom f.hom],
        ∃ e : GrpObj.Lie (H.asOver (Spec (.of F))) ≃ₗ⁅F⁆
          GrpObj.Lie (H.asOver (Spec (.of F))),
          e.toLieHom = GrpObj.differential f.hom ∧ ∀ x, e (q x) = q (e x)) ∧
      (∀ (K : Scheme.{u}) [K.Over (Spec (.of F))]
        [GrpObj (K.asOver (Spec (.of F)))] [IsAffine K]
        [LocallyOfFiniteType (K ↘ Spec (.of F))] [QuasiCompact (K ↘ Spec (.of F))],
        ∃ (δK : GrpObj.Lie (K.asOver (Spec (.of F))) ≃ₗ[F]
            BialgebraDistribution.tangentFunctionals F Γ(K, ⊤))
          (DK : GrpObj.Lie (K.asOver (Spec (.of F))) →ₗ⁅F⁆ Derivation F Γ(K, ⊤) Γ(K, ⊤))
          (qK : GrpObj.Lie (K.asOver (Spec (.of F))) →
            GrpObj.Lie (K.asOver (Spec (.of F)))),
          (∀ (y : GrpObj.Lie (K.asOver (Spec (.of F)))) (a : Γ(K, ⊤)),
            (((GrpObj.lieEquivTangent (K.asOver (Spec (.of F))) y).val.left.appTop ≫
              (Scheme.ΓSpecIso (.of (DualNumber F))).hom).hom a) =
                TrivSqZeroExt.inl (Coalgebra.counit (R := F) a) +
                  TrivSqZeroExt.inr ((δK y).1 a)) ∧
          (∀ y : GrpObj.Lie (K.asOver (Spec (.of F))),
            (DK y).toLinearMap =
              BialgebraDistribution.tangentContraction F Γ(K, ⊤) (δK y).1) ∧
          LieAlgebra.IsRestrictedOperation F p qK ∧
          (∀ y : GrpObj.Lie (K.asOver (Spec (.of F))),
            (DK (qK y)).toLinearMap = (DK y).toLinearMap ^ p) ∧
          ∀ (f : H.asOver (Spec (.of F)) ⟶ K.asOver (Spec (.of F))) [IsMonHom f],
            (∀ (x : GrpObj.Lie (H.asOver (Spec (.of F)))) (a : Γ(K, ⊤)),
              (δK (GrpObj.differential f x)).1 a = (δ x).1 (f.left.appTop.hom a)) ∧
            (∀ x y : GrpObj.Lie (H.asOver (Spec (.of F))),
              GrpObj.differential f ⁅x, y⁆ =
                ⁅GrpObj.differential f x, GrpObj.differential f y⁆) ∧
            (∀ x : GrpObj.Lie (H.asOver (Spec (.of F))),
              GrpObj.differential f (q x) = qK (GrpObj.differential f x))) ∧
      ∀ (W : Type v) [AddCommGroup W] [Module F W]
        (α : W →ₗ[F] W ⊗[F] Γ(H, ⊤)),
        HopfAction.Coassociative F Γ(H, ⊤) W α →
        HopfAction.Counital F Γ(H, ⊤) W α →
        ∃ ρ : GrpObj.Lie (H.asOver (Spec (.of F))) →ₗ[F] Module.End F W,
          (∀ x : GrpObj.Lie (H.asOver (Spec (.of F))),
            ρ x = (TensorProduct.rid F W).toLinearMap ∘ₗ (δ x).1.lTensor W ∘ₗ α) ∧
          (∀ x y : GrpObj.Lie (H.asOver (Spec (.of F))),
            ρ ⁅x, y⁆ = ρ x * ρ y - ρ y * ρ x) ∧
          (∀ x : GrpObj.Lie (H.asOver (Spec (.of F))), ρ (q x) = ρ x ^ p) ∧
          ∃ A : RestrictedEnvelopingAlgebra F (GrpObj.Lie (H.asOver (Spec (.of F)))) p q
              →ₐ[F] Module.End F W,
            ∀ x : GrpObj.Lie (H.asOver (Spec (.of F))),
              A (RestrictedEnvelopingAlgebra.ι F p q x) = ρ x := by
  sorry

end AlgebraicGeometry
