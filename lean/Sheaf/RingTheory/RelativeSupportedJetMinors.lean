module

public import Sheaf.RingTheory.SupportedHomogeneousDivision
public import Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum
public import Sheaf.LinearAlgebra.Matrix.MinorIdeal
public import Sheaf.RingTheory.DiagonalJets
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-! # Relative supported Taylor minors

Source: the agent relative-coefficient version of Bierstone--Milman, Theorem 7.14,
pp.264--268, and Stacks Project, Algebra, Tags 0H93, 0H90, 0H8Z.
(blueprint: lem-per-relative-supported-jet-minors)

The transverse variables alone are translated. Polynomial coordinate bases of principal
parts specify the geometric comparison, including the image of the ideal in principal
parts, rather than principal parts of the ideal as an abstract module.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v w
open scoped BigOperators TensorProduct
open AlgebraicGeometry
open AlgebraicGeometry.HilbertCoefficient (iteratedPartial)

namespace RelativeSupportedJets

/-- Exponents of the finite transverse Taylor module.
Source: relative-coefficient BM 7.14 calculation, step 1
(blueprint: lem-per-relative-supported-jet-minors). -/
def exponents (n t : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Finsupp.finite_of_degree_lt (σ := Fin n) (t + 1)).toFinset

/-- The number of Taylor monomials.
Source: relative-coefficient BM 7.14 calculation, step 1
(blueprint: lem-per-relative-supported-jet-minors). -/
def size (n t : ℕ) : ℕ := (exponents n t).card

/-- A fixed enumeration, used identically over every coefficient ring.
Source: relative-coefficient BM 7.14 calculation, step 1
(blueprint: lem-per-relative-supported-jet-minors). -/
def exponent (n t : ℕ) (i : Fin (size n t)) : Fin n →₀ ℕ := by
  classical
  exact ((Fintype.equivFinOfCardEq
    (by simp only [Fintype.card_coe, size]) :
      ↥(exponents n t) ≃ Fin (size n t)).symm i).val

/-- The coefficient of Y^nu in f(Z+Y), by binomial expansion over any ring.
Source: relative-coefficient BM 7.14 calculation, step 1
(blueprint: lem-per-relative-supported-jet-minors). -/
def taylorCoefficient {n : ℕ} {R : Type u} [CommRing R]
    (ν : Fin n →₀ ℕ) (f : MvPowerSeries (Fin n) R) : MvPowerSeries (Fin n) R :=
  fun μ ↦ (∏ j : Fin n, Nat.choose (μ j + ν j) (ν j)) • MvPowerSeries.coeff (μ + ν) f

/-- The relative Taylor matrix, with columns (i,eta) representing Y^eta f_i(Z+Y).
Source: relative-coefficient BM 7.14 calculation, steps 1--2
(blueprint: lem-per-relative-supported-jet-minors). -/
def matrix {n s : ℕ} {R : Type u} [CommRing R]
    (f : Fin s → MvPowerSeries (Fin n) R) (t : ℕ) :
    Matrix (Fin (size n t)) (Fin (s * size n t)) (MvPowerSeries (Fin n) R) := by
  classical
  exact fun a b ↦
    if exponent n t ((finProdFinEquiv.symm b).2) ≤ exponent n t a then
      taylorCoefficient
        (exponent n t a - exponent n t ((finProdFinEquiv.symm b).2))
        (f (finProdFinEquiv.symm b).1)
    else 0

/-- The specified minor ideal, including oversized minors.
Source: relative-coefficient BM 7.14 calculation, step 4
(blueprint: lem-per-relative-supported-jet-minors). -/
def minor {n s : ℕ} {R : Type u} [CommRing R]
    (f : Fin s → MvPowerSeries (Fin n) R) (t r : ℕ) : Ideal (MvPowerSeries (Fin n) R) :=
  Matrix.minorIdeal (size n t) (s * size n t) r (matrix f t)

/-- The prescribed closed-fibre diagram rank; it is held fixed under base change.
Source: relative-coefficient BM 7.14 calculation, step 3
(blueprint: lem-per-relative-supported-jet-minors). -/
def rank {n : ℕ} (D : Set (Fin n →₀ ℕ)) (t : ℕ) : ℕ :=
  {γ : Fin n →₀ ℕ | γ ∈ D ∧ γ.degree ≤ t}.ncard

/-- Variables accumulated through the degree cutoff q.
Source: relative-coefficient BM 7.14 calculation, step 6
(blueprint: lem-per-relative-supported-jet-minors). -/
def prefixVariables {n s : ℕ} (α : Fin s → Fin n →₀ ℕ) (q : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j ↦ ∃ i : Fin s, (α i).degree ≤ q ∧ α i j ≠ 0

/-- The ideal of the accumulated transverse variables.
Source: relative-coefficient BM 7.14 calculation, step 6
(blueprint: lem-per-relative-supported-jet-minors). -/
def variableIdeal {n s : ℕ} {R : Type u} [CommRing R]
    (α : Fin s → Fin n →₀ ℕ) (q : ℕ) : Ideal (MvPowerSeries (Fin n) R) :=
  Ideal.span {F | ∃ j ∈ prefixVariables α q, F = MvPowerSeries.X j}

/-- The selected derivative for each essential variable; zero on unused variables.
Source: relative-coefficient BM 7.14 calculation, step 7
(blueprint: lem-per-relative-supported-jet-minors). -/
def selectedDerivative {n s : ℕ} {R : Type u} [CommRing R]
    (α : Fin s → Fin n →₀ ℕ) (f : Fin s → MvPowerSeries (Fin n) R)
    (pick : MonomialDiagram.EssentialVariables α → Fin s)
    (β : MonomialDiagram.EssentialVariables α → Fin n →₀ ℕ)
    (j : Fin n) : MvPowerSeries (Fin n) R := by
  classical
  exact if h : ∃ i : Fin s, α i j ≠ 0 then
    iteratedPartial (β ⟨j, h⟩) (f (pick ⟨j, h⟩)) else 0

/-- The determinant of the transverse Jacobian at W=Z=0 in one degree prefix.
Source: relative-coefficient BM 7.14 calculation, step 7
(blueprint: lem-per-relative-supported-jet-minors). -/
def jacobian {m n s : ℕ} {L : Type u} [Field L]
    (α : Fin s → Fin n →₀ ℕ)
    (f : Fin s → MvPowerSeries (Fin n) (MvPowerSeries (Fin m) L))
    (pick : MonomialDiagram.EssentialVariables α → Fin s)
    (β : MonomialDiagram.EssentialVariables α → Fin n →₀ ℕ) (q : ℕ) : L := by
  classical
  exact Matrix.det fun i j : ↥(prefixVariables α q) ↦ MvPowerSeries.constantCoeff
    (MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (MvPowerSeries (Fin m) L) j.val
      (selectedDerivative α f pick β i.val)))

/-- The initial polynomial after setting the coefficient parameters W to zero.
Source: relative-coefficient BM 7.14 calculation, step 3
(blueprint: lem-per-relative-supported-jet-minors). -/
def initialForm {m n : ℕ} {L : Type u} [Field L]
    (f : MvPowerSeries (Fin n) (MvPowerSeries (Fin m) L)) (d : ℕ) :
    MvPolynomial (Fin n) L :=
  MvPowerSeries.truncTotal (d + 1)
    (MvPowerSeries.homogeneousComponent d
      (MvPowerSeries.map MvPowerSeries.constantCoeff f))

/-- Exactly the supported transverse hypotheses, with no total-order bound in (W,Z).
Source: relative-coefficient BM 7.14 calculation, steps 2--8
(blueprint: lem-per-relative-supported-jet-minors). -/
structure Hypotheses {m n s : ℕ} {L : Type u} [Field L]
    (D : Set (Fin n →₀ ℕ)) (α : Fin s → Fin n →₀ ℕ)
    (f : Fin s → MvPowerSeries (Fin n) (MvPowerSeries (Fin m) L))
    (J : Ideal (MvPowerSeries (Fin n) (MvPowerSeries (Fin m) L))) (Q : ℕ)
    (pick : MonomialDiagram.EssentialVariables α → Fin s)
    (β : MonomialDiagram.EssentialVariables α → Fin n →₀ ℕ) : Prop where
  monotone : MonomialDiagram.IsMonotone D
  vertices : MonomialDiagram.IsOrderedVertexFamily D α
  positive : ∀ i : Fin s, 0 < (α i).degree
  generators : J = Ideal.span (Set.range f)
  flat : Module.Flat (MvPowerSeries (Fin m) L)
    (MvPowerSeries (Fin n) (MvPowerSeries (Fin m) L) ⧸ J)
  fibre_order : ∀ i : Fin s,
    (MvPowerSeries.map MvPowerSeries.constantCoeff (f i)).order = (α i).degree
  division : ∀ q t : ℕ, MonomialDiagram.HasUniqueDivision
    (MonomialDiagram.generated (MonomialDiagram.prefixVertices α q))
    (MonomialDiagram.prefixVertices α q)
    (fun i ↦ initialForm (f i.val) (α i.val).degree) t
  supported_generation : ∀ F : MvPowerSeries (Fin n) (MvPowerSeries (Fin m) L),
    F ∈ J ↔ ∃ a : Fin s → MvPowerSeries (Fin n) (MvPowerSeries (Fin m) L),
      (∀ (i : Fin s) (γ : Fin n →₀ ℕ), MvPowerSeries.coeff γ (a i) ≠ 0 →
        γ ∈ MonomialDiagram.quotientSupport α i) ∧ F = ∑ i : Fin s, a i * f i
  chosen_vertex : ∀ j : MonomialDiagram.EssentialVariables α,
    α (pick j) = β j + Finsupp.single j.val 1
  first_block : ∀ (j : MonomialDiagram.EssentialVariables α) (i : Fin s),
    α i j.val ≠ 0 → (α (pick j)).degree ≤ (α i).degree
  derivative_in_prefix : ∀ (q : ℕ) (j : Fin n), j ∈ prefixVariables α q →
    selectedDerivative α f pick β j ∈ variableIdeal α q
  jacobian_unit : ∀ q : ℕ, IsUnit (jacobian α f pick β q)
  later_derivatives : ∀ (q : ℕ) (i : Fin s) (δ : Fin n →₀ ℕ),
    q < (α i).degree → (∀ j : Fin n, j ∉ prefixVariables α q → δ j = 0) →
    (∃ h : Fin s, (α h).degree ≤ q ∧ α h ≤ δ) → δ.degree ≤ Q →
    iteratedPartial δ (f i) ∈ variableIdeal α q
  bound : ∀ i : Fin s, (α i).degree - 1 ≤ Q

/-- The ideal of all lower transverse derivatives of the supported generators.
Source: relative-coefficient BM 7.14 calculation, step 4
(blueprint: lem-per-relative-supported-jet-minors). -/
def lowerIdeal {n s : ℕ} {R : Type u} [CommRing R]
    (α : Fin s → Fin n →₀ ℕ) (f : Fin s → MvPowerSeries (Fin n) R) :
    Ideal (MvPowerSeries (Fin n) R) :=
  Ideal.span {F | ∃ (i : Fin s) (ν : Fin n →₀ ℕ),
    ν.degree < (α i).degree ∧ F = iteratedPartial ν (f i)}

/-- The universal second-factor jet, in the dependency's actual principal-parts algebra.
Source: Stacks 0H90 (blueprint: lem-per-relative-supported-jet-minors). -/
def second {R₀ : Type u} {R : Type v} [CommRing R₀] [CommRing R] [Algebra R₀ R]
    (t : ℕ) (h : R) : DiagonalJets.principalParts R₀ R t :=
  Ideal.Quotient.mk _ (1 ⊗ₜ[R₀] h)

/-- The coordinate-difference monomial times the second-factor jet of a relation.
Source: Stacks 0H90 and 0H93 (blueprint: lem-per-relative-supported-jet-minors). -/
def column {R₀ : Type u} {R : Type v} [CommRing R₀] [CommRing R] [Algebra R₀ R]
    {n : ℕ} (z : Fin n → R) (t : ℕ) (η : Fin n →₀ ℕ) (h : R) :
    DiagonalJets.principalParts R₀ R t :=
  (∏ j : Fin n,
    (second (R₀ := R₀) t (z j) - algebraMap R _ (z j)) ^ η j) * second t h

/-- A relation matrix in the prescribed monomial basis of relative principal parts.
Source: Stacks 0H90 and 0H93 (blueprint: lem-per-relative-supported-jet-minors). -/
def principalMatrix {R₀ : Type u} {R : Type v} [CommRing R₀] [CommRing R] [Algebra R₀ R]
    {n s t : ℕ} (z : Fin n → R)
    (b : Module.Basis (Fin (size n t)) R (DiagonalJets.principalParts R₀ R t))
    (h : Fin s → R) : Matrix (Fin (size n t)) (Fin (s * size n t)) R :=
  fun a c ↦ b.repr (column z t (exponent n t (finProdFinEquiv.symm c).2)
    (h (finProdFinEquiv.symm c).1)) a

/-- The basis is pinned down by actual coordinate differences, including its empty monomial.
Source: Stacks 0H93 (blueprint: lem-per-relative-supported-jet-minors). -/
def IsCoordinateBasis {R₀ : Type u} {R : Type v}
    [CommRing R₀] [CommRing R] [Algebra R₀ R] {n t : ℕ} (z : Fin n → R)
    (b : Module.Basis (Fin (size n t)) R (DiagonalJets.principalParts R₀ R t)) : Prop :=
  ∀ a : Fin (size n t), b a = column z t (exponent n t a) 1

/-- Geometric principal-parts matrices, their relation spans, centered Taylor comparison,
and arbitrary coefficient base change, all with the same prescribed minor size.
Source: Stacks 0H93, 0H90, 0H8Z, relative-coefficient BM calculation, steps 11--12
(blueprint: lem-per-relative-supported-jet-minors). -/
def GeometricCompatibility : Prop :=
  ∀ (R₀ R : Type v) [CommRing R₀] [CommRing R] [Algebra R₀ R]
    (n t : ℕ) (c : MvPolynomial (Fin n) R₀ →ₐ[R₀] R),
    AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom c.toRingHom)) →
    ∀ (e : R →ₐ[R₀] R₀), (∀ j : Fin n, e (c (MvPolynomial.X j)) = 0) →
    ∀ K : Ideal R,
    RingedSpace.IsCoherent (Spec (CommRingCat.of R)).toRingedSpace
      (tilde (ModuleCat.of R K)) →
    ∃ b : Module.Basis (Fin (size n t)) R (DiagonalJets.principalParts R₀ R t),
      IsCoordinateBasis (fun j ↦ c (MvPolynomial.X j)) b ∧
      (∀ (s : ℕ) (h : Fin s → R), Ideal.span (Set.range h) = K →
        Submodule.span R {x | ∃ a ∈ Ideal.span (Set.range h), x = second (R₀ := R₀) t a} =
          Submodule.span R (Set.range fun p : Fin (s * size n t) ↦
            column (fun j ↦ c (MvPolynomial.X j)) t
              (exponent n t (finProdFinEquiv.symm p).2) (h (finProdFinEquiv.symm p).1))) ∧
      (∀ (s s' r : ℕ) (h : Fin s → R) (h' : Fin s' → R),
        Ideal.span (Set.range h) = K → Ideal.span (Set.range h') = K →
        Matrix.minorIdeal (size n t) (s * size n t) r
          (principalMatrix (fun j ↦ c (MvPolynomial.X j)) b h) =
        Matrix.minorIdeal (size n t) (s' * size n t) r
          (principalMatrix (fun j ↦ c (MvPolynomial.X j)) b h')) ∧
      (∀ (C : Type w) [CommRing C] [Algebra R₀ C]
        (τ : R →ₐ[R₀] MvPowerSeries (Fin n) C),
        (∀ j : Fin n, τ (c (MvPolynomial.X j)) = MvPowerSeries.X j) →
        ∀ (s r : ℕ) (h : Fin s → R), Ideal.span (Set.range h) = K →
          (fun a p ↦ τ (principalMatrix (fun j ↦ c (MvPolynomial.X j)) b h a p)) =
            matrix (fun i ↦ τ (h i)) t ∧
          Ideal.map τ.toRingHom
            (Matrix.minorIdeal (size n t) (s * size n t) r
              (principalMatrix (fun j ↦ c (MvPolynomial.X j)) b h)) =
            minor (fun i ↦ τ (h i)) t r) ∧
      (∀ (R₀' : Type w) [CommRing R₀'] [Algebra R₀ R₀'],
        ∃ b' : Module.Basis (Fin (size n t)) (R₀' ⊗[R₀] R)
          (DiagonalJets.principalParts R₀' (R₀' ⊗[R₀] R) t),
          IsCoordinateBasis
            (fun j ↦ Algebra.TensorProduct.includeRight.toRingHom (c (MvPolynomial.X j))) b' ∧
          ∀ (s r : ℕ) (h : Fin s → R), Ideal.span (Set.range h) = K →
            Ideal.map Algebra.TensorProduct.includeRight.toRingHom
              (Matrix.minorIdeal (size n t) (s * size n t) r
                (principalMatrix (fun j ↦ c (MvPolynomial.X j)) b h)) =
              Matrix.minorIdeal (size n t) (s * size n t) r
                (principalMatrix
                  (fun j ↦ Algebra.TensorProduct.includeRight.toRingHom (c (MvPolynomial.X j)))
                  b' (fun i ↦ Algebra.TensorProduct.includeRight.toRingHom (h i))))

/-- The relative supported jet-minor identity and all its invariance clauses.

Source: agent relative-coefficient version of BM Theorem 7.14, pp.264--268;
Stacks Project, Algebra, Tags 0H93, 0H90, 0H8Z, and More on Algebra, Tag 07Z7.
(blueprint: lem-per-relative-supported-jet-minors).

Proof plan (the twelve accepted DAG steps):
1. Translate only Z. The coefficient of Y^gamma in Y^eta tau(f_i) is the
(gamma-eta)-derivative divided by its multi-factorial, or zero if eta is not below gamma.
2. The span of tau(J) is Y-stable, since Y_j tau(h)=tau(Z_j h)-Z_j tau(h).
Downward closure of the quotient supports shows that the supported columns span it.
3. Good columns satisfy |eta|+d_i<=t and correspond to D in degrees <=t.
After reduction at W=Z=0, supported homogeneous division gives invertible diagonal
blocks. The square pivot minor on these rows is therefore a unit in the power-series ring.
4. Every bad column has entries in the lower derivative ideal. Laplace expansion,
then Cauchy--Binet for the equal column spans, puts every prescribed minor in that ideal.
5. Add the column (i,0) and an outside-D row to the unit pivot. Its cofactor expansion
solves for each outside-D lower derivative modulo minors and the inside-D derivatives.
6. Induct on degree blocks. Restrict an inside-D lower derivative to the earlier
essential variables; the later-generator hypothesis puts it in the earlier variable ideal.
Derivatives in complementary variables preserve that ideal.
7. Step 5 now puts all current-block lower derivatives in the sum of minors. The
chosen derivatives have invertible transverse Jacobian and lie in the prefix variable
ideal, so formal graph factorization identifies their ideal with that variable ideal.
At the last block this proves the reverse inclusion and hence equality.
8. Empty vertices give J=0 and zero ideals; n=0 forces this case. Empty pivot determinants
are one. Only closed-fibre transverse order was used, never total (W,Z)-order.
9. Any two finite generating families give the same Taylor image. Cauchy--Binet in
both directions proves equality of minors with the original rank index held fixed.
10. Coefficientwise maps preserve binomial Taylor coefficients and determinants.
Thus extension of the minor ideal equals the ideal of the mapped matrix; flatness
of the coefficient change is unnecessary.
11. In etale coordinates, Stacks 0H93 and 0H90 identify principal parts with truncated
polynomials in coordinate differences. The second-factor ideal is spanned by the displayed
monomial multiples. Unique infinitesimal etale lifting gives the centered Taylor comparison.
12. Stacks 0H8Z identifies these coordinate bases after arbitrary coefficient base change.
Determinants, finite polynomials in their entries, commute with both comparison maps.
-/
theorem relativeSupportedJetMinors {L : Type u} [Field L] [CharZero L]
    {m n s Q : ℕ} (D : Set (Fin n →₀ ℕ)) (α : Fin s → Fin n →₀ ℕ)
    (f : Fin s → MvPowerSeries (Fin n) (MvPowerSeries (Fin m) L))
    (J : Ideal (MvPowerSeries (Fin n) (MvPowerSeries (Fin m) L)))
    (pick : MonomialDiagram.EssentialVariables α → Fin s)
    (β : MonomialDiagram.EssentialVariables α → Fin n →₀ ℕ)
    (H : Hypotheses D α f J Q pick β) :
    (∑ t ∈ Finset.range (Q + 1), minor f t (rank D t + 1)) = lowerIdeal α f ∧
    (∀ (s' t : ℕ) (h : Fin s' → MvPowerSeries (Fin n) (MvPowerSeries (Fin m) L)),
      Ideal.span (Set.range h) = J →
      minor h t (rank D t + 1) = minor f t (rank D t + 1)) ∧
    (∀ (A' : Type v) [CommRing A'] [IsLocalRing A']
      [IsAdicComplete (IsLocalRing.maximalIdeal A') A']
      (φ : MvPowerSeries (Fin m) L →+* A') [IsLocalHom φ] (t : ℕ),
      Ideal.map (MvPowerSeries.map φ) (minor f t (rank D t + 1)) =
        minor (fun i ↦ MvPowerSeries.map φ (f i)) t (rank D t + 1)) ∧
    GeometricCompatibility.{v, w} := by
  sorry

end RelativeSupportedJets
