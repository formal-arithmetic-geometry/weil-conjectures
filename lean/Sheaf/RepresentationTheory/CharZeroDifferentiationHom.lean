module

public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie
public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.Topology.Connected.Basic
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace

import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality

/-! # Differentiation detects rational representation morphisms

Source: Milne, Algebraic Groups (2017), Theorem 10.23, Propositions 10.28--10.31,
Proposition 10.15, Cartier Theorem 3.23, and §10l, printed p.208.
(blueprint: lem-sfb-char-zero-differentiation-hom)

The existing `GrpObj.lieEquivTangent` sends `GrpObj.Lie` to its canonical dual-number
point. The coordinate functional and the invariant derivation below are existentially
specified by their exact formulas, so no arbitrary differential, Lie bracket, or action
is supplied as an additional hypothesis.
-/

set_option autoImplicit false

@[expose] public section

universe u v w r

open CategoryTheory TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Differentiating finite-dimensional rational representations of a smooth connected affine
finite-type group in characteristic zero detects exactly their morphisms.
Source: Milne, Algebraic Groups (2017), Theorem 10.23, Propositions 10.28--10.31,
Proposition 10.15, Cartier Theorem 3.23, and §10l, printed p.208.
(blueprint: lem-sfb-char-zero-differentiation-hom)

Proof:
1. Put A = F[G]. The affine finite-type algebra lemma
   (lem-pc-affine-finite-type-algebra) supplies finitely many generators. A tangent point
   has coordinate map epsilon + eps * delta; multiplicativity is precisely the counit
   Leibniz identity. Derivations are determined by their values on the generators, giving
   finite dimension. The existing lieIdentityTangentEquiv identifies these with the
   scheme tangent vectors (def-sc-scheme-tangent-space).
2. Send delta to (1 tensor delta) Delta. The Hopf counit and coassociativity identities
   prove Leibniz, left invariance and the inverse formula epsilon D = delta. Commutators
   remain left invariant. Transporting their bracket gives the canonical Lie bracket
   (def-wf-lie-algebra), agreeing with the upstream tangent bracket by Theorem 10.23.
3. In bases write alpha(m_j) = sum_i m_i tensor b_ij. The comodule dictionary
   (lem-sfb-rational-representation-comodule-dictionary) gives epsilon(b_ij) = delta_ij
   and Delta(b_ij) = sum_k b_ik tensor b_kj. Evaluation at epsilon + eps * delta yields
   1 + eps * dr(delta); differentiating the coefficient identities proves preservation
   of brackets. The contractions in the statement are basis independent.
4. The coaction square is B_N U - U B_M = 0. Applying a counit derivation gives the
   differential square. Conversely its entries generate an ideal I whose closed
   subscheme H = Spec(A/I) is the stabilizer of the graph of U
   (def-weil-affine-spectrum).
5. For every F-algebra, that stabilizer is closed under multiplication and inversion,
   so H is a closed subgroup scheme (def-sc-group-scheme-subgroup). The differential
   squares imply that every tangent point factors through H.
6. Cartier smoothness (lem-sfb-affine-group-frobenius-smooth-image) makes H smooth.
   Its open identity component H0 is smooth and connected
   (lem-sfb-locally-algebraic-group-identity-component). Tangent points factor through
   H0 by lem-weil-pbc-morphism-factors-through-open-subscheme. Using
   lem-sc-rational-tangent-cotangent-duality, its tangent map onto Lie(G) is surjective.
   Apply lem-sfb-smooth-subgroup-tangent-generation to the one-element family H0 and
   K = H. It gives H = G, hence I = 0 and the coaction square.
7. Evaluate the coaction square at any algebra point to get the square after every
   scalar extension. Conversely use the universal point id_A. Empty bases cause no
   exception, so zero representations are included.
-/
theorem charZero_differentiation_hom
    (F : Type u) [Field F] [IsAlgClosed F] [CharZero F]
    (G : Scheme.{u}) [G.Over (Spec (.of F))]
    [GrpObj (G.asOver (Spec (.of F)))] [IsAffine G]
    [Smooth (G ↘ Spec (.of F))] [ConnectedSpace G]
    [LocallyOfFiniteType (G ↘ Spec (.of F))] [QuasiCompact (G ↘ Spec (.of F))] :
    FiniteDimensional F (GrpObj.Lie (G.asOver (Spec (.of F)))) ∧
    ∃ (δ : GrpObj.Lie (G.asOver (Spec (.of F))) →ₗ[F] (Γ(G, ⊤) →ₗ[F] F))
      (D : GrpObj.Lie (G.asOver (Spec (.of F))) →ₗ⁅F⁆ Derivation F Γ(G, ⊤) Γ(G, ⊤)),
      (∀ (x : GrpObj.Lie (G.asOver (Spec (.of F)))) (a : Γ(G, ⊤)),
        (((GrpObj.lieEquivTangent (G.asOver (Spec (.of F))) x).val.left.appTop ≫
          (Scheme.ΓSpecIso (.of (DualNumber F))).hom).hom a) =
            TrivSqZeroExt.inl (Coalgebra.counit a) + TrivSqZeroExt.inr (δ x a)) ∧
      Function.Injective δ ∧
      (∀ d : Γ(G, ⊤) →ₗ[F] F,
        (∀ a b : Γ(G, ⊤), d (a * b) =
          Coalgebra.counit a * d b + d a * Coalgebra.counit b) ↔
        ∃ x : GrpObj.Lie (G.asOver (Spec (.of F))), δ x = d) ∧
      (∀ x : GrpObj.Lie (G.asOver (Spec (.of F))),
        (D x).toLinearMap = (TensorProduct.rid F Γ(G, ⊤)).toLinearMap ∘ₗ
          (δ x).lTensor Γ(G, ⊤) ∘ₗ Coalgebra.comul) ∧
      (∀ x : GrpObj.Lie (G.asOver (Spec (.of F))),
        Coalgebra.comul ∘ₗ (D x).toLinearMap =
          (D x).toLinearMap.lTensor Γ(G, ⊤) ∘ₗ Coalgebra.comul) ∧
      (∀ x : GrpObj.Lie (G.asOver (Spec (.of F))), Coalgebra.counit ∘ₗ (D x).toLinearMap = δ x) ∧
      (∀ d : Derivation F Γ(G, ⊤) Γ(G, ⊤),
        (Coalgebra.comul ∘ₗ d.toLinearMap =
          d.toLinearMap.lTensor Γ(G, ⊤) ∘ₗ Coalgebra.comul) ↔
        ∃ x : GrpObj.Lie (G.asOver (Spec (.of F))), D x = d) ∧
      ∀ (M : Type v) [AddCommGroup M] [Module F M] [FiniteDimensional F M]
        (N : Type w) [AddCommGroup N] [Module F N] [FiniteDimensional F N]
        (αM : M →ₗ[F] M ⊗[F] Γ(G, ⊤))
        (αN : N →ₗ[F] N ⊗[F] Γ(G, ⊤)),
        HopfAction.Coassociative F Γ(G, ⊤) M αM →
        HopfAction.Counital F Γ(G, ⊤) M αM →
        HopfAction.Coassociative F Γ(G, ⊤) N αN →
        HopfAction.Counital F Γ(G, ⊤) N αN →
        ∃ (drM : GrpObj.Lie (G.asOver (Spec (.of F))) →ₗ[F] Module.End F M)
          (drN : GrpObj.Lie (G.asOver (Spec (.of F))) →ₗ[F] Module.End F N),
          (∀ x : GrpObj.Lie (G.asOver (Spec (.of F))), drM x =
            (TensorProduct.rid F M).toLinearMap ∘ₗ (δ x).lTensor M ∘ₗ αM) ∧
          (∀ x : GrpObj.Lie (G.asOver (Spec (.of F))), drN x =
            (TensorProduct.rid F N).toLinearMap ∘ₗ (δ x).lTensor N ∘ₗ αN) ∧
          (∀ x y : GrpObj.Lie (G.asOver (Spec (.of F))),
            drM ⁅x, y⁆ = (drM x).comp (drM y) - (drM y).comp (drM x)) ∧
          (∀ x y : GrpObj.Lie (G.asOver (Spec (.of F))),
            drN ⁅x, y⁆ = (drN x).comp (drN y) - (drN y).comp (drN x)) ∧
          (∀ x : GrpObj.Lie (G.asOver (Spec (.of F))), ∃ g : Γ(G, ⊤) →ₐ[F] DualNumber F,
            g.toRingHom = ((GrpObj.lieEquivTangent (G.asOver (Spec (.of F))) x).val.left.appTop ≫
              (Scheme.ΓSpecIso (.of (DualNumber F))).hom).hom ∧
            (∀ m : M, g.toLinearMap.lTensor M (αM m) =
              m ⊗ₜ[F] (1 : DualNumber F) + drM x m ⊗ₜ[F] DualNumber.eps) ∧
            (∀ n : N, g.toLinearMap.lTensor N (αN n) =
              n ⊗ₜ[F] (1 : DualNumber F) + drN x n ⊗ₜ[F] DualNumber.eps)) ∧
          ∀ f : M →ₗ[F] N,
            (αN ∘ₗ f = f.rTensor Γ(G, ⊤) ∘ₗ αM ↔
              ∀ x : GrpObj.Lie (G.asOver (Spec (.of F))), f ∘ₗ drM x = drN x ∘ₗ f) ∧
            (αN ∘ₗ f = f.rTensor Γ(G, ⊤) ∘ₗ αM ↔
              ∀ (R : Type (max u r)) [CommRing R] [Algebra F R]
                (g : Γ(G, ⊤) →ₐ[F] R) (m : M),
                f.rTensor R (g.toLinearMap.lTensor M (αM m)) =
                  g.toLinearMap.lTensor N (αN (f m))) := by
  sorry

end AlgebraicGeometry
