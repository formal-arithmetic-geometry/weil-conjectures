module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Invariants
import WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorDecomposition

/-!
# Finite Galois descent for arbitrary vector spaces

Source: Milne, Algebraic Groups (2017), Proposition 3.36, pp. 76–77, and Appendix A.64,
pp. 580–581. (blueprint: lem-sfb-finite-galois-vector-space-descent)

A semilinear action is represented by its underlying `k`-linear representation together
with the displayed scalar compatibility. Its invariant space is Mathlib's
`Representation.invariants`. The tensor action is Mathlib's `Representation.tprod`
of the field-automorphism representation with the trivial representation.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y

open scoped TensorProduct

namespace Field

/-- Scalar extension and invariants are mutually inverse for arbitrary vector spaces over
 a finite Galois extension. The families `θ` and `η` are specified by their pure-tensor
 formulas; their naturality and the bijection on equivariant linear maps are included.
 No vector space in this statement is assumed finite-dimensional.

Proof (Milne, Proposition 3.36 and Appendix A.64, pp. 77, 580–581):
1. The finite-Galois fixed-field theorem gives a finite group Π with fixed field k.
   Use `lem-exc-finite-galois-tensor-decomposition` to choose finitely many aᵢ, bᵢ in L
   with ∑ᵢ aᵢ σ(bᵢ) = δ(σ,1). For v put T_b(v) = ∑σ σ_V(bv).
   Reindexing proves that T_b(v) is invariant. Set S(v) = ∑ᵢ aᵢ ⊗ T_bᵢ(v).
2. The tensor universal property gives θ(λ ⊗ v) = λv. The coefficient identity gives
   θS = id. For invariant w, tensor balancing and the fixed-field theorem give
   S(cw) = c ⊗ w, so Sθ = id. Thus θ is an L-linear isomorphism. Its equivariance
   follows on pure tensors from semilinearity; for an equivariant linear map f,
   f(λw) = λf(w) proves naturality, first on pure tensors and then on all tensors.
3. The same identity yields an element t with trace 1. The k-linear functional
   p(c) = trace(tc) gives P(c ⊗ u) = p(c)u. Then P(1 ⊗ u) = u and
   1 ⊗ P(z) = ∑σ σ(t)σ(z). For invariant z this equals z, proving that η is invertible.
4. The formula η(u) = 1 ⊗ u gives linearity and naturality. Tensoring and restriction
   preserve identities and composition. The triangle identities on λ ⊗ u and on
   invariant w show that these natural isomorphisms give inverse equivalences.
5. For equivariant g define f by applying η_W⁻¹ to g(1 ⊗ u). Then
   g(λ ⊗ u) = λ ⊗ f(u), and tensor generation proves g = 1 ⊗ f. Conversely base change
   is equivariant, and injectivity of η gives uniqueness. All sums are finite independently
   of the dimensions; no division by the order of Π is used.

Source: Milne, Algebraic Groups (2017), Proposition 3.36 and Appendix A.64.
(blueprint: lem-sfb-finite-galois-vector-space-descent) -/
theorem finiteGaloisVectorSpaceDescent
    (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L] :
    ∃ θ : ∀ (V : Type w) [AddCommGroup V] [Module L V] [Module k V]
        [IsScalarTower k L V] (ρ : Representation k (L ≃ₐ[k] L) V),
        (∀ (σ : L ≃ₐ[k] L) (a : L) (z : V), ρ σ (a • z) = σ a • ρ σ z) →
        (L ⊗[k] ρ.invariants) ≃ₗ[L] V,
    ∃ η : ∀ (U : Type x) [AddCommGroup U] [Module k U],
        U ≃ₗ[k] (Representation.tprod (AlgEquiv.toLinearMapHom k L)
          (Representation.trivial k (L ≃ₐ[k] L) U)).invariants,
      (∀ (V : Type w) [AddCommGroup V] [Module L V] [Module k V]
          [IsScalarTower k L V] (ρ : Representation k (L ≃ₐ[k] L) V)
          (hρ : ∀ (σ : L ≃ₐ[k] L) (a : L) (z : V),
            ρ σ (a • z) = σ a • ρ σ z),
        (∀ (a : L) (z : ρ.invariants), θ V ρ hρ (a ⊗ₜ[k] z) = a • (z : V)) ∧
        (∀ (σ : L ≃ₐ[k] L) (z : L ⊗[k] ρ.invariants),
          θ V ρ hρ ((Representation.tprod (AlgEquiv.toLinearMapHom k L)
            (Representation.trivial k (L ≃ₐ[k] L) ρ.invariants)) σ z) =
              ρ σ (θ V ρ hρ z))) ∧
      (∀ (V V' : Type w) [AddCommGroup V] [Module L V] [Module k V]
          [IsScalarTower k L V] [AddCommGroup V'] [Module L V'] [Module k V']
          [IsScalarTower k L V'] (ρ : Representation k (L ≃ₐ[k] L) V)
          (ρ' : Representation k (L ≃ₐ[k] L) V')
          (hρ : ∀ (σ : L ≃ₐ[k] L) (a : L) (z : V),
            ρ σ (a • z) = σ a • ρ σ z)
          (hρ' : ∀ (σ : L ≃ₐ[k] L) (a : L) (z : V'),
            ρ' σ (a • z) = σ a • ρ' σ z)
          (f : V →ₗ[L] V')
          (hf : ∀ (σ : L ≃ₐ[k] L) (z : V), f (ρ σ z) = ρ' σ (f z))
          (z : L ⊗[k] ρ.invariants),
        f (θ V ρ hρ z) = θ V' ρ' hρ'
          ((LinearMap.baseChange L
            (((f.restrictScalars k).comp ρ.invariants.subtype).codRestrict ρ'.invariants
              (fun z σ ↦ (hf σ z).symm.trans (congrArg f (z.property σ))))) z)) ∧
      (∀ (U : Type x) [AddCommGroup U] [Module k U] (z : U),
        (η U z : L ⊗[k] U) = 1 ⊗ₜ[k] z) ∧
      (∀ (U W : Type x) [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
          (f : U →ₗ[k] W) (z : U),
        (η W (f z) : L ⊗[k] W) = LinearMap.baseChange L f (η U z)) ∧
      (∀ (U : Type x) (W : Type y) [AddCommGroup U] [Module k U]
          [AddCommGroup W] [Module k W],
        (∀ (f : U →ₗ[k] W) (σ : L ≃ₐ[k] L) (z : L ⊗[k] U),
          LinearMap.baseChange L f ((Representation.tprod (AlgEquiv.toLinearMapHom k L)
            (Representation.trivial k (L ≃ₐ[k] L) U)) σ z) =
              (Representation.tprod (AlgEquiv.toLinearMapHom k L)
                (Representation.trivial k (L ≃ₐ[k] L) W)) σ (LinearMap.baseChange L f z)) ∧
        (∀ (g : L ⊗[k] U →ₗ[L] L ⊗[k] W),
          (∀ (σ : L ≃ₐ[k] L) (z : L ⊗[k] U),
            g ((Representation.tprod (AlgEquiv.toLinearMapHom k L)
              (Representation.trivial k (L ≃ₐ[k] L) U)) σ z) =
                (Representation.tprod (AlgEquiv.toLinearMapHom k L)
                  (Representation.trivial k (L ≃ₐ[k] L) W)) σ (g z)) →
            ∃! f : U →ₗ[k] W, LinearMap.baseChange L f = g)) := by
  sorry

end Field
