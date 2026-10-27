module

public import Sheaf.RingTheory.QuadraticCotangentRelations
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-! # Invariance and computation of quadratic cotangent relations

Source: Stacks Project, curves.tex, Tag 0C49, `lemma-nodal-algebraic`, conditions
(1)--(3) and the preceding definition. The intrinsic semilinear transport and
principal degree-two kernel calculation expand the source's implicit argument.
(blueprint: lem-trf-cotangent-quadratic-relation-invariance).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open IsLocalRing
open scoped Matrix

namespace IsLocalRing

/-- Multiplication of arbitrary lifts defines a unique residue-linear map on quadratics.
Source: Stacks Project, Tag 0C49, the map Sym²(m/m²) to m²/m³.
(blueprint: lem-trf-cotangent-quadratic-relation-invariance).

Proof: Changing a variable lift by m² changes its quadratic products by m³. Changing
any coefficient lift by m changes its product with two variable lifts by m³.
The quotient m²/m³ is annihilated by m, so multiplication is residue-field linear.
Every quadratic is a sum of quadratic monomials; their values determine the map
uniquely. Surjectivity of the residue and cotangent quotient maps supplies lifts.
This works also for an empty basis, when the homogeneous quadratic space is zero. -/
theorem quadraticCotangentMultiplication_existsUnique
    (A : Type u) [CommRing A] [IsLocalRing A] (d : ℕ)
    (b : Module.Basis (Fin d) (ResidueField A) (CotangentSpace A)) :
    ∃! μ : (MvPolynomial.homogeneousSubmodule (Fin d) (ResidueField A) 2) →ₗ[ResidueField A]
      quadraticCotangentTarget A, IsQuadraticCotangentMultiplication A d b μ := by
  sorry

/-- An arbitrary local ring isomorphism transports quadratic relations semilinearly,
with the transport specified by its action on lifts and substitution of coordinates.
Source: Stacks Project, Tag 0C49, intrinsic degree-two relation condition.
(blueprint: lem-trf-cotangent-quadratic-relation-invariance).

Proof:
1. A ring isomorphism preserves units, hence the maximal ideal and each of its powers.
   Quotienting gives the residue-field isomorphism `ResidueField.mapEquiv φ` and the
   cotangent bijection τ. Multiplication proves τ is semilinear for that residue map.
2. Express τ(b i) in b'. Apply the residue isomorphism to coefficients and replace X_i
   by that linear expression. The inverse is obtained from φ.symm, so this gives T.
3. Apply φ to lifted quadratic products. Errors in linear lifts lie in m'² and
   disappear modulo m'³ after multiplication. Thus μ' T = φ₂ μ, where φ₂ is the
   induced bijection on m²/m³. This gives equivalence of kernel membership.
4. Restrict T and its inverse to the two kernels. The result κ is semilinear,
   bijective, and has the displayed underlying substitution. No coefficient field
   in A or A' is needed. Distinct basis sizes and the empty basis are allowed. -/
theorem quadraticCotangentRelations_transport
    (A : Type u) (A' : Type v) [CommRing A] [CommRing A']
    [IsLocalRing A] [IsLocalRing A'] (φ : A ≃+* A') (d d' : ℕ)
    (b : Module.Basis (Fin d) (ResidueField A) (CotangentSpace A))
    (b' : Module.Basis (Fin d') (ResidueField A') (CotangentSpace A'))
    (μ : (MvPolynomial.homogeneousSubmodule (Fin d) (ResidueField A) 2) →ₗ[ResidueField A]
      quadraticCotangentTarget A)
    (μ' : (MvPolynomial.homogeneousSubmodule (Fin d') (ResidueField A') 2) →ₗ[ResidueField A']
      quadraticCotangentTarget A')
    (hμ : IsQuadraticCotangentMultiplication A d b μ)
    (hμ' : IsQuadraticCotangentMultiplication A' d' b' μ') :
    ∃ τ : CotangentSpace A ≃+ CotangentSpace A',
      (∀ (c : ResidueField A) (v : CotangentSpace A),
        τ (c • v) = ResidueField.mapEquiv φ c • τ v) ∧
      (∀ (a : maximalIdeal A) (a' : maximalIdeal A'), φ a.val = a'.val →
        τ ((maximalIdeal A).toCotangent a) = (maximalIdeal A').toCotangent a') ∧
      ∃ T : (MvPolynomial.homogeneousSubmodule (Fin d) (ResidueField A) 2) ≃+
          (MvPolynomial.homogeneousSubmodule (Fin d') (ResidueField A') 2),
        (∀ (c : ResidueField A) (q : MvPolynomial.homogeneousSubmodule
            (Fin d) (ResidueField A) 2), T (c • q) = ResidueField.mapEquiv φ c • T q) ∧
        (∀ q, (T q).val = MvPolynomial.quadraticLinearSubstitution
          (ResidueField.mapEquiv φ).toRingHom
          (Matrix.of fun i j ↦ b'.repr (τ (b i)) j) q.val) ∧
        (∀ q, μ' (T q) = 0 ↔ μ q = 0) ∧
        ∃ κ : LinearMap.ker μ ≃+ LinearMap.ker μ',
          (∀ (c : ResidueField A) (q : LinearMap.ker μ),
            κ (c • q) = ResidueField.mapEquiv φ c • κ q) ∧
          ∀ q, (κ q).val = T q.val := by
  sorry

end IsLocalRing

namespace MvPolynomial

/-- The polar matrix uses 2a,b,2c, rather than division by two.
Source: Stacks Project, Tag 0C49, definition preceding `lemma-nodal-algebraic`.
(blueprint: lem-trf-cotangent-quadratic-relation-invariance).

Proof: Read the three monomial coefficients of the displayed polynomial. Its X₀²
coefficient is a, its X₀X₁ coefficient is b, and its X₁² coefficient is c.
The definition of binaryPolarMatrix gives the four entries, in every characteristic. -/
theorem binaryPolarMatrix_quadratic
    (k : Type u) [Field k] (a b c : k) :
    binaryPolarMatrix (C a * X 0 ^ 2 + C b * (X 0 * X 1) + C c * X 1 ^ 2) =
      (!![2 * a, b; b, 2 * c] : Matrix (Fin 2) (Fin 2) k) := by
  sorry

/-- Linear substitution transforms the binary polar matrix and its determinant.
Source: Stacks Project, Tag 0C49, nondegenerate symmetric quadratics.
(blueprint: lem-trf-cotangent-quadratic-relation-invariance).

Proof: Write P = ((p,q),(r,s)) and the transported coefficients as A=σ(a), B=σ(b),
C=σ(c). The substituted coefficients are A p²+B p r+C r²,
2A p q+B(p s+q r)+2C r s, and A q²+B q s+C s². Entrywise multiplication gives
Pᵀ σ(B_q) P. The two-by-two determinant expansion is
4a'c'-(b')²=(p s-q r)² σ(4ac-b²). No division by two occurs. -/
theorem binaryPolarMatrix_substitution
    (k : Type u) (k' : Type v) [Field k] [Field k'] (σ : k ≃+* k')
    (P : Matrix (Fin 2) (Fin 2) k') (q : homogeneousSubmodule (Fin 2) k 2) :
    binaryPolarMatrix (quadraticLinearSubstitution σ.toRingHom P q.val) =
        Pᵀ * (binaryPolarMatrix q.val).map σ * P ∧
      (binaryPolarMatrix (quadraticLinearSubstitution σ.toRingHom P q.val)).det =
        P.det ^ 2 * σ (binaryPolarMatrix q.val).det := by
  sorry

end MvPolynomial

namespace IsLocalRing

/-- Existence of a binary relation with invertible polar matrix is invariant under
arbitrary ring isomorphisms, including those not linear over a coefficient field.
Source: Stacks Project, Tag 0C49, intrinsic nondegenerate quadratic relation.
(blueprint: lem-trf-cotangent-quadratic-relation-invariance).

Proof: Use quadraticCotangentRelations_transport and write the cotangent bijection
in the two bases. The inverse cotangent bijection gives an inverse for P, so det P
is a unit. The polar determinant formula preserves being a unit in both directions,
since the residue-field map is an isomorphism. Kernel transport therefore preserves
existence of the required relation. In characteristic two the determinant is -b²;
the same formula and argument still apply. -/
theorem nondegenerateQuadraticCotangentRelation_iff
    (A : Type u) (A' : Type v) [CommRing A] [CommRing A']
    [IsLocalRing A] [IsLocalRing A'] (φ : A ≃+* A')
    (b : Module.Basis (Fin 2) (ResidueField A) (CotangentSpace A))
    (b' : Module.Basis (Fin 2) (ResidueField A') (CotangentSpace A'))
    (μ : (MvPolynomial.homogeneousSubmodule (Fin 2) (ResidueField A) 2) →ₗ[ResidueField A]
      quadraticCotangentTarget A)
    (μ' : (MvPolynomial.homogeneousSubmodule (Fin 2) (ResidueField A') 2) →ₗ[ResidueField A']
      quadraticCotangentTarget A')
    (hμ : IsQuadraticCotangentMultiplication A 2 b μ)
    (hμ' : IsQuadraticCotangentMultiplication A' 2 b' μ') :
    (∃ q : LinearMap.ker μ, IsUnit (MvPolynomial.binaryPolarMatrix q.val.val).det) ↔
      ∃ q : LinearMap.ker μ', IsUnit (MvPolynomial.binaryPolarMatrix q.val.val).det := by
  sorry

end IsLocalRing

namespace MvPolynomial

/-- A formal quotient by H contained in p² has the variable cotangent basis of size e;
its actual multiplication kernel is the explicit degree-two ideal kernel.
Source: Stacks Project, Tag 0C49, implication (3) to (1).
(blueprint: lem-trf-cotangent-quadratic-relation-invariance).

Proof:
1. Apply power_series_mem_combined_ideal_pow_iff with base ideal zero in degrees
   1,2,3. Membership in p^n means vanishing of coefficients below degree n. Thus
   the degree-one and degree-two monomials form bases of the respective quotients.
2. The power-series unit criterion identifies its maximal ideal with p. Since
   H ⊆ p² ⊆ p, the quotient is proper and local, with maximal ideal p/H and residue
   field F. Products of lifts give m^n=(p^n+H)/H.
3. The map p/p² to m/m² is surjective with zero kernel, since H ⊆ p². The variable
   classes are therefore an F-basis, including the empty basis when e=0.
4. Evaluate homogeneous quadratics and reduce modulo m³. Its image lies in m²/m³,
   giving the displayed linear map μ. Its kernel is exactly q ∈ p³+H, as asserted. -/
theorem formalQuotient_quadraticCotangent
    (F : Type u) [Field F] (e : ℕ) (H : Ideal (MvPowerSeries (Fin e) F))
    (hH : H ≤ (Ideal.span
      (Set.range (MvPowerSeries.X : Fin e → MvPowerSeries (Fin e) F))) ^ 2) :
    Nonempty (IsLocalRing (MvPowerSeries (Fin e) F ⧸ H)) ∧
      ∀ [IsLocalRing (MvPowerSeries (Fin e) F ⧸ H)],
        ∃ (ρ : ResidueField (MvPowerSeries (Fin e) F ⧸ H) ≃+* F)
          (b : Module.Basis (Fin e) F (CotangentSpace (MvPowerSeries (Fin e) F ⧸ H)))
          (μ : homogeneousSubmodule (Fin e) F 2 →ₗ[F]
            quadraticCotangentTarget (MvPowerSeries (Fin e) F ⧸ H)),
          (∀ c : F, ρ (residue _ (algebraMap F _ c)) = c) ∧
          (∀ i : Fin e, ∃ hi : Ideal.Quotient.mk H (MvPowerSeries.X i) ∈
              maximalIdeal (MvPowerSeries (Fin e) F ⧸ H),
            b i = (maximalIdeal (MvPowerSeries (Fin e) F ⧸ H)).toCotangent
              ⟨Ideal.Quotient.mk H (MvPowerSeries.X i), hi⟩) ∧
          Module.finrank F (CotangentSpace (MvPowerSeries (Fin e) F ⧸ H)) = e ∧
          (∀ q, (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow
              (maximalIdeal (MvPowerSeries (Fin e) F ⧸ H)) 2 (μ q)).val =
            Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin e) F ⧸ H) ^ 3)
              (eval₂Hom (algebraMap F _) (fun i ↦ Ideal.Quotient.mk H (MvPowerSeries.X i))
                q.val)) ∧
          LinearMap.ker μ = formalQuadraticKernel F e H := by
  sorry

/-- The quadratic kernel of a principal formal hypersurface is the span of its
quadratic initial part; it is zero if that part is zero.
Source: Stacks Project, Tag 0C49, formal hypersurface computation.
(blueprint: lem-trf-cotangent-quadratic-relation-invariance).

Proof: The coefficient criterion identifies quadratics with p²/p³. For H=(f), a
quadratic q lies in p³+(f) exactly when q=t+gf with t ∈ p³. Because f ∈ p², the
quadratic part of gf is g(0)f₂. This gives q=g(0)f₂. Conversely λf-λf₂ ∈ p³, so
every λf₂ lies in the kernel. If f₂=0 its span is zero. When e=0 one has p=0,
f=0 and the same statements hold. -/
theorem formalPrincipal_quadraticKernel
    (F : Type u) [Field F] (e : ℕ) (f : MvPowerSeries (Fin e) F)
    (hf : f ∈ (Ideal.span
      (Set.range (MvPowerSeries.X : Fin e → MvPowerSeries (Fin e) F))) ^ 2) :
    formalQuadraticKernel F e (Ideal.span {f}) = Submodule.span F
        {⟨homogeneousComponent 2 (MvPowerSeries.truncTotal 3 f),
          homogeneousComponent_mem 2 (MvPowerSeries.truncTotal 3 f)⟩} ∧
      (MvPowerSeries.homogeneousComponent 2 f = 0 →
        formalQuadraticKernel F e (Ideal.span {f}) = ⊥) := by
  sorry

/-- Every nonzero binary homogeneous quadratic spans the one-dimensional quadratic
relation space of its formal hypersurface, with no nondegeneracy assumption.
Source: Stacks Project, Tag 0C49, formal hypersurface computation.
(blueprint: lem-trf-cotangent-quadratic-relation-invariance).

Proof: Apply formalPrincipal_quadraticKernel to the homogeneous series Q. Its
quadratic part is Q itself, so the kernel is its span. A nonzero coefficient of Q
makes λ ↦ λQ injective; it is surjective onto the span. Thus its dimension is one.
This includes squares, degenerate quadratics and characteristic two. -/
theorem formalBinary_quadraticKernel
    (F : Type u) [Field F] (Q : homogeneousSubmodule (Fin 2) F 2) (hQ : Q ≠ 0) :
    formalQuadraticKernel F 2 (Ideal.span {Q.val.toMvPowerSeries}) =
        Submodule.span F {Q} ∧
      Module.finrank F (formalQuadraticKernel F 2 (Ideal.span {Q.val.toMvPowerSeries})) = 1 := by
  sorry

end MvPolynomial
