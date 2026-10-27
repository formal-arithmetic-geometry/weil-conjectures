module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

/-! # Quadratic cotangent relations

Source: Stacks Project, curves.tex, Tag 0C49, the definition preceding
`lemma-nodal-algebraic` and its degree-two multiplication map.
(blueprint: def-trf-quadratic-cotangent-relations).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

namespace IsLocalRing

/-- The standard quotient model of m²/m³, with its canonical residue-field action.
Source: Stacks Project, Tag 0C49, degree-two multiplication.
(blueprint: def-trf-quadratic-cotangent-relations). -/
abbrev quadraticCotangentTarget (A : Type u) [CommRing A] [IsLocalRing A] :=
  (maximalIdeal A ^ 2 : Ideal A) ⧸
    (maximalIdeal A • ⊤ : Submodule A (maximalIdeal A ^ 2 : Ideal A))

/-- The residue-field module structure on m²/m³, inherited from Mathlib's torsion quotient.
Source: Stacks Project, Tag 0C49, degree-two multiplication.
(blueprint: def-trf-quadratic-cotangent-relations). -/
instance quadraticCotangentTarget_module
    (A : Type u) [CommRing A] [IsLocalRing A] :
    Module (ResidueField A) (quadraticCotangentTarget A) :=
  inferInstanceAs (Module (A ⧸ maximalIdeal A)
    ((maximalIdeal A ^ 2 : Ideal A) ⧸
      (maximalIdeal A • ⊤ : Submodule A (maximalIdeal A ^ 2 : Ideal A))))

/-- Evaluate a polynomial using arbitrary lifts of its coefficients and variables.
The coefficient lift is a function, with no coefficient-field embedding assumed.
Source: Stacks Project, Tag 0C49, degree-two multiplication.
(blueprint: def-trf-quadratic-cotangent-relations). -/
def quadraticLiftEvaluation (A : Type u) [CommRing A] [IsLocalRing A]
    (d : ℕ) (s : ResidueField A → A) (x : Fin d → maximalIdeal A)
    (q : MvPolynomial (Fin d) (ResidueField A)) : A :=
  ∑ E ∈ q.support, s (MvPolynomial.coeff E q) * ∏ i : Fin d, (x i).val ^ E i

/-- Characterization of the multiplication map on homogeneous quadratics, for every
choice of lifts. The standard quotient embeds into A/m³ by Mathlib's ideal equivalence.
Source: Stacks Project, Tag 0C49, degree-two multiplication.
(blueprint: def-trf-quadratic-cotangent-relations). -/
def IsQuadraticCotangentMultiplication
    (A : Type u) [CommRing A] [IsLocalRing A] (d : ℕ)
    (b : Module.Basis (Fin d) (ResidueField A) (CotangentSpace A))
    (μ : (MvPolynomial.homogeneousSubmodule (Fin d) (ResidueField A) 2) →ₗ[ResidueField A]
      quadraticCotangentTarget A) : Prop :=
  ∀ (s : ResidueField A → A), (∀ c, residue A (s c) = c) →
    ∀ (x : Fin d → maximalIdeal A), (∀ i, (maximalIdeal A).toCotangent (x i) = b i) →
      ∀ q : MvPolynomial.homogeneousSubmodule (Fin d) (ResidueField A) 2,
        (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow (maximalIdeal A) 2 (μ q)).val =
          Ideal.Quotient.mk (maximalIdeal A ^ 3) (quadraticLiftEvaluation A d s x q.val)

end IsLocalRing

namespace MvPolynomial

/-- Apply a coefficient homomorphism and a linear substitution X = P X'. Rows of P
are images of source variables, so the binary polar matrix transforms by Pᵀ B P.
Source: Stacks Project, Tag 0C49, nondegeneracy in symmetric degree two.
(blueprint: def-trf-quadratic-cotangent-relations). -/
def quadraticLinearSubstitution
    {k : Type u} {k' : Type v} [CommRing k] [CommRing k']
    {d d' : ℕ} (σ : k →+* k') (P : Matrix (Fin d) (Fin d') k')
    (q : MvPolynomial (Fin d) k) : MvPolynomial (Fin d') k' :=
  eval₂Hom (C.comp σ) (fun i ↦ ∑ j : Fin d', C (P i j) * X j) q

/-- The polar matrix of a binary quadratic, extracted from its three coefficients.
No division by two is used, including in characteristic two.
Source: Stacks Project, Tag 0C49, definition preceding `lemma-nodal-algebraic`.
(blueprint: def-trf-quadratic-cotangent-relations). -/
def binaryPolarMatrix {k : Type u} [CommRing k] (q : MvPolynomial (Fin 2) k) :
    Matrix (Fin 2) (Fin 2) k :=
  Matrix.of fun i j ↦
    if i = j then 2 * coeff (Finsupp.single i 2) q
    else coeff (Finsupp.single 0 1 + Finsupp.single 1 1) q

/-- Quadratic relations in a formal quotient S/H: degree-two polynomials whose series
belong to p³ + H. This is the kernel of the canonical degree-two quotient map.
Source: Stacks Project, Tag 0C49, implication (3) to (1), formal hypersurface calculation.
(blueprint: def-trf-quadratic-cotangent-relations). -/
def formalQuadraticKernel (F : Type u) [Field F] (e : ℕ)
    (H : Ideal (MvPowerSeries (Fin e) F)) :
    Submodule F (MvPolynomial.homogeneousSubmodule (Fin e) F 2) :=
  Submodule.comap
    ((coeToMvPowerSeries.algHom (σ := Fin e) (R := F) F).toLinearMap.comp
      (MvPolynomial.homogeneousSubmodule (Fin e) F 2).subtype)
    ((Ideal.span (Set.range (MvPowerSeries.X : Fin e → MvPowerSeries (Fin e) F))) ^ 3 ⊔ H
      |>.restrictScalars F)

end MvPolynomial
