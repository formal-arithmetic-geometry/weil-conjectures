/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.NonnegativeStrictGradedAlgebra
public import WeilConjectures.RingTheory.GradedDividedPowers
public import WeilConjectures.RingTheory.DividedPowerVariableAdjunction
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Divided-power differential graded algebras

Source: Stacks Project, `dpa.tex`, Tags 09PF, 09PG and 09PJ, with the polynomial
adjunctions of Tags 09PH, 09PI and 0F4I (blueprint: def-sfb-divided-power-dga).

The differential is an actual linear map on the internally graded algebra. It lowers
integer degrees, including the zero component mapping to the zero negative component.
The underlying chain complex and its homology use Mathlib's existing constructions.
Polynomiality concerns the underlying graded divided-power algebra only.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace GradedAlgebra

open CategoryTheory

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- A nonnegative strictly graded commutative differential graded algebra with compatible
positive-even divided powers. The inherited divided-power structure includes all seven
axioms of 09PG; `compatible` is imposed on arbitrary positive even elements, not just
homogeneous ones. There is no extra requirement about powers of boundaries.
Source: Stacks, Tags 09PF, 09PG and 09PJ
(blueprint: def-sfb-divided-power-dga). -/
structure DividedPowerDGA (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedCommutative 𝒜] extends GradedDividedPowers 𝒜 where
  /-- The differential is linear over the coefficient ring. -/
  d : A →ₗ[R] A
  /-- The differential lowers degree by one, with negative components zero. -/
  degree : ∀ (i : ℤ) (x : A), x ∈ integerComponent 𝒜 (i + 1) →
    d x ∈ integerComponent 𝒜 i
  /-- The differential squares to zero. -/
  square_zero : ∀ x : A, d (d x) = 0
  /-- The Leibniz rule with the homological sign. -/
  leibniz : ∀ (i j : ℕ) (x y : A), x ∈ 𝒜 i → y ∈ 𝒜 j →
    d (x * y) = d x * y + (-1 : A) ^ i * (x * d y)
  /-- Compatibility with positive divided powers on the whole positive even ideal. -/
  compatible : ∀ (n : ℕ) (x : evenSubalgebra 𝒜), 0 < n →
    x ∈ positiveEvenIdeal 𝒜 →
      d (dpow n x : A) = d (x : A) * (dpow (n - 1) x : A)

namespace DividedPowerDGA

variable {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]
    [IsStrictlyGradedCommutative 𝒜]

/-- The actual differential between consecutive integer components.
Source: Stacks, section Tate resolutions, homological convention before 09PG and 09PJ
(blueprint: def-sfb-divided-power-dga). -/
def componentDifferential (D : DividedPowerDGA 𝒜) (i : ℤ) :
    ModuleCat.of R (integerComponent 𝒜 (i + 1)) ⟶
      ModuleCat.of R (integerComponent 𝒜 i) :=
  ModuleCat.ofHom
    ((D.d.domRestrict (integerComponent 𝒜 (i + 1))).codRestrict
      (integerComponent 𝒜 i) (fun x ↦ D.degree i x x.property))

/-- Consecutive component differentials compose to zero, as required for the underlying
chain complex. Source: Stacks, section Tate resolutions and 09PJ
(blueprint: def-sfb-divided-power-dga).

Proof: A component differential is the restriction of the linear map `D.d`, with the
codomain restricted using `D.degree`. Evaluate the composite on a component element.
Its image in A is `D.d (D.d x)`, which is zero by `D.square_zero`. The inclusion of
an integer component in A is injective, so the composite is the zero linear map,
and hence the zero morphism in ModuleCat. -/
theorem componentDifferential_comp (D : DividedPowerDGA 𝒜) (i : ℤ) :
    D.componentDifferential (i + 1) ≫ D.componentDifferential i = 0 := by
  sorry

/-- The underlying chain complex, extended by zero to negative degrees.
Source: Stacks, section Tate resolutions before 09PG and Definition 09PJ
(blueprint: def-sfb-divided-power-dga). -/
def chainComplex (D : DividedPowerDGA 𝒜) : ChainComplex (ModuleCat.{v} R) ℤ :=
  ChainComplex.of (fun i : ℤ ↦ ModuleCat.of R (integerComponent 𝒜 i))
    D.componentDifferential D.componentDifferential_comp

/-- Homology is Mathlib homology of the underlying chain complex: the kernel of the
outgoing differential modulo the image of the incoming differential.
Source: Stacks, section Tate resolutions, homological convention and 09PJ
(blueprint: def-sfb-divided-power-dga). -/
noncomputable def homology (D : DividedPowerDGA 𝒜) (i : ℤ) : ModuleCat.{v} R :=
  D.chainComplex.homology i

/-- Package the given algebra and its existing grading for the recorded variable-adjunction
interface. No algebra or divided-power operations are chosen from an existence theorem.
Source: Stacks, Tags 09PF and 09PH--0F4I
(blueprint: def-sfb-divided-power-dga). -/
def algebraData (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedCommutative 𝒜] : VariableAdjunction.AlgebraData R where
  Carrier := A
  grade := 𝒜

/-- The underlying graded divided-power algebra is polynomial if it is a union of
successive set adjunctions starting with a polynomial algebra concentrated in degree zero.
`SetPresentation` gives the exterior or divided-symbol basis, its multiplication and its
graded inclusion; `SetNormalized` specifies the extended divided powers. `UnionPresentation`
requires injective compatible inclusions, coverage and the union grading, and `Preserves`
identifies the given divided powers with the extended ones at every stage.

A finite sequence is included by taking empty variable sets thereafter. The stage algebras
are presentations of their images in A, so using A itself as the union also permits every
graded divided-power isomorphism to such a union. Index sets live in the carrier universe;
no finiteness, characteristic, degree bound or condition on the differential is imposed.
Source: Stacks, Tags 09PH, 09PI and 0F4I and the polynomial adjunctions in section Tate
resolutions (blueprint: def-sfb-divided-power-dga). -/
def IsPolynomial (D : DividedPowerDGA 𝒜) : Prop :=
  ∃ (B : ℕ → VariableAdjunction.AlgebraData.{u, v} R)
    (γ : ∀ k : ℕ, GradedDividedPowers (B k).grade) (J₀ : Type v),
    Nonempty (MvPolynomial J₀ R ≃ₐ[R] (B 0).Carrier) ∧
    (∀ n : ℕ, (B 0).grade n = if n = 0 then ⊤ else ⊥) ∧
    ∃ (e : ℕ → ℕ) (J : ℕ → Type v), (∀ k : ℕ, 0 < e k) ∧
      ∃ p : ∀ k : ℕ, VariableAdjunction.SetPresentation (B k) (γ k)
        (e k) (J k) (B (k + 1)),
        (∀ k : ℕ, VariableAdjunction.SetNormalized (p k) (γ (k + 1))) ∧
        ∃ q : VariableAdjunction.UnionPresentation B γ e J p (algebraData 𝒜),
          ∀ k : ℕ, VariableAdjunction.Preserves (q.into k) (γ k) D.toGradedDividedPowers

end DividedPowerDGA
end GradedAlgebra

namespace GradedAlgebra

universe w

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- A polynomial presentation of the underlying graded divided-power algebra, with its
specified generators and without a differential. The positive generators can be adjoined
in any sequence of positive degrees; `labels_bijective` says that each specified positive
label occurs exactly once. The initial polynomial variables are precisely the degree-zero
labels. Empty adjunctions allow finite presentations to be padded to an infinite sequence.
Source: Stacks, 09PH, 09PI, 0F4I and the polynomial hypothesis of 09PS.
(blueprint: def-sfb-divided-power-dga). -/
structure GradedDividedPowers.PolynomialPresentation
    {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedCommutative 𝒜]
    (γ : GradedDividedPowers 𝒜) (J : ℕ → Type w) (generator : ∀ e : ℕ, J e → A) where
  stage : ℕ → VariableAdjunction.AlgebraData.{u, v} R
  dp : ∀ k : ℕ, GradedDividedPowers (stage k).grade
  base : MvPolynomial (J 0) R ≃ₐ[R] (stage 0).Carrier
  base_grading : ∀ n : ℕ, (stage 0).grade n = if n = 0 then ⊤ else ⊥
  degree : ℕ → ℕ
  positive : ∀ k : ℕ, 0 < degree k
  labels : ℕ → Type w
  label : ∀ k : ℕ, labels k → J (degree k)
  labels_bijective : Function.Bijective
    (fun z : Sigma labels ↦
      (⟨⟨degree z.1, positive z.1⟩, label z.1 z.2⟩ :
        Σ e : {n : ℕ // 0 < n}, J e.val))
  step : ∀ k : ℕ, VariableAdjunction.SetPresentation
    (stage k) (dp k) (degree k) (labels k) (stage (k + 1))
  normalized : ∀ k : ℕ, VariableAdjunction.SetNormalized (step k) (dp (k + 1))
  union : VariableAdjunction.UnionPresentation stage dp degree labels step
    (DividedPowerDGA.algebraData 𝒜)
  preserves : ∀ k : ℕ, VariableAdjunction.Preserves (union.into k) (dp k) γ
  zero_generators : ∀ j : J 0,
    (union.into 0).toAlgHom (base (MvPolynomial.X j)) = generator 0 j
  positive_generators : ∀ (k : ℕ) (j : labels k),
    (union.into (k + 1)).toAlgHom ((step k).generator j) = generator (degree k) (label k j)

end GradedAlgebra
