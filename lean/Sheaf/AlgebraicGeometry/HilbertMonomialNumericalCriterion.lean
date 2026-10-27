module

public import Sheaf.AlgebraicGeometry.HilbertPluckerPGLLinearization
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Data.Finset.Max
import Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis

/-! # The monomial numerical criterion for Hilbert stability

Source: Morrison, arXiv:0810.2340, §2.2, Proposition 1 and proof, pp.6--7.
(blueprint: lem-sfb-hilbert-monomial-numerical-criterion)

The supplied Hilbert embedding presentation is the one furnished in every degree above
its field-independent bound. We use its actual universal sections and determinant action.
Writing E in coordinates k^(n+2) loses no vector space or ordered basis: an identification
with this space transports the embedding, and the test ranges over every basis.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.HilbertPlucker

variable {k : Type u} [Field k] {n : ℕ} {P : NumericalHilbertPolynomial}
variable {D : Hilbert k n P} {m : ℕ}

/-- The actual space of sections at a rational Hilbert point, using the base-change
identification supplied by the Hilbert embedding presentation.
Source: Morrison §2.2 (blueprint: lem-sfb-hilbert-monomial-numerical-criterion). -/
abbrev pointSections (x : PGLLinearization.fieldTest k k ⟶ D.H) :=
  Γ((Scheme.Modules.pullback x.left).obj (sections D m), ⊤)

/-- Expand a monomial in an arbitrary ordered basis into the fixed coordinate monomials.
Source: Morrison §2.2, Proposition 1
(blueprint: lem-sfb-hilbert-monomial-numerical-criterion). -/
def basisMonomial (b : Module.Basis (Fin (n + 2)) k (Fin (n + 2) → k))
    (a : RelativeProjectiveSpace.monomials.{u} (n + 1) m) :
    MvPolynomial (Fin (n + 2)) k :=
  ∏ i : Fin (n + 2),
    (∑ j : Fin (n + 2), MvPolynomial.C (b i j) * MvPolynomial.X j) ^ a.down.val i

/-- Restrict an expanded basis monomial by the recorded, section-normalized restriction
map. Scalars are transported by the canonical Γ(Spec k) = k isomorphism.
Source: Morrison §2.2, Proposition 1
(blueprint: lem-sfb-hilbert-monomial-numerical-criterion). -/
def basisMonomialRestriction (E : Presentation D m)
    (x : PGLLinearization.fieldTest k k ⟶ D.H)
    (b : Module.Basis (Fin (n + 2)) k (Fin (n + 2) → k))
    (a : RelativeProjectiveSpace.monomials.{u} (n + 1) m) : pointSections (m := m) x :=
  ∑ j : Fin E.N,
    (Scheme.ΓSpecIso (.of k)).inv.hom
      (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm
        (E.monomials (ULift.up j)).down.val) (basisMonomial b a)) •
      pullbackΓ x.left (sections D m) (monomialRestriction D m (E.monomials (ULift.up j)))

/-- Exactly those finite sets of degree-m monomials whose restrictions are a basis.
The coefficient ring Γ(Spec k) is canonically k. The empty set is allowed in rank zero.
Source: Morrison §2.2, Proposition 1
(blueprint: lem-sfb-hilbert-monomial-numerical-criterion). -/
def IsMonomialBasis (E : Presentation D m)
    (x : PGLLinearization.fieldTest k k ⟶ D.H)
    (b : Module.Basis (Fin (n + 2)) k (Fin (n + 2) → k)) (I : Finset (Fin E.N)) : Prop :=
  ∃ B : Module.Basis I Γ(Spec (.of k), ⊤) (pointSections (m := m) x),
    ∀ j : I, B j = basisMonomialRestriction E x b (E.monomials (ULift.up j.val))

/-- The rational weight of a degree-m monomial is the exponent-weight dot product.
Source: Morrison §2.2, equation (1)
(blueprint: lem-sfb-hilbert-monomial-numerical-criterion). -/
def monomialWeight (w : Fin (n + 2) → ℚ)
    (a : RelativeProjectiveSpace.monomials.{u} (n + 1) m) : ℚ :=
  ∑ i : Fin (n + 2), (a.down.val i : ℚ) * w i

/-- All sums of weights of monomial bases, as a finite set of rational numbers.
Source: Morrison §2.2, Proposition 1
(blueprint: lem-sfb-hilbert-monomial-numerical-criterion). -/
def basisWeights (E : Presentation D m) (x : PGLLinearization.fieldTest k k ⟶ D.H)
    (b : Module.Basis (Fin (n + 2)) k (Fin (n + 2) → k)) (w : Fin (n + 2) → ℚ) :
    Finset ℚ := by
  classical
  exact ((Finset.univ.powerset).filter (IsMonomialBasis E x b)).image
    (fun I ↦ ∑ j ∈ I, monomialWeight w (E.monomials (ULift.up j)))

/-- W is the minimum of the sums of monomial-basis weights. The fallback only makes
this real-data definition total; surjectivity in Presentation guarantees nonemptiness.
Source: Morrison §2.2, Proposition 1
(blueprint: lem-sfb-hilbert-monomial-numerical-criterion). -/
def minimumBasisWeight (E : Presentation D m) (x : PGLLinearization.fieldTest k k ⟶ D.H)
    (b : Module.Basis (Fin (n + 2)) k (Fin (n + 2) → k)) (w : Fin (n + 2) → ℚ) : ℚ :=
  if h : (basisWeights E x b w).Nonempty then (basisWeights E x b w).min' h else 0

/-- Geometric stability is equivalent to the strict monomial-weight inequality for
all ordered bases and all nonconstant rational weights, in any characteristic.
Source: Morrison §2.2, Proposition 1(1)--(2), pp.6--7.

Proof, following the four DAG steps:
1. The restriction Sym^m E → Q is onto, dim Q = P(m), and the quotient Plücker
point has determinant line det Q by lem-sfb-hilbert-plucker-pgl-linearization.
Apply lem-sfb-hilbert-mumford-projective-representation to its dual wedge functional.
2. By lem-sfb-gm-representation-weight-basis every one-parameter subgroup has an
integral weight basis. Its determinant character is t^(sum a_i), so SL means sum a_i=0
as an integer in every characteristic. Nontriviality means the tuple is nonzero.
Conversely each such weighted basis defines a subgroup on every test algebra.
3. A wedge coordinate is nonzero exactly when its monomials restrict to a basis.
Dualizing and inverting the subgroup give this coordinate its monomial weight sum.
Hilbert--Mumford therefore says that the minimum is negative for every nonzero
integral sum-zero tuple. Surjectivity makes the collection of bases nonempty.
For rank zero, the empty wedge has coordinate 1 and weight 0, so strict stability fails.
4. For nonconstant rational w, put mean=(sum w_i)/r and clear denominators with c>0.
The integral tuple a_i=c(w_i-mean) is nonzero and sum-zero. Every basis has P(m)
monomials of degree m, hence W(a)=c(W(w)-m*P(m)*mean). Positivity of c gives the
claimed strict inequality. Conversely integral sum-zero tuples are among the tests.
Constant tuples give equality and are excluded. No smoothness, reducedness, dimension,
or characteristic restriction enters the argument.
(blueprint: lem-sfb-hilbert-monomial-numerical-criterion). -/
theorem stable_iff_monomial_numerical [IsAlgClosed k] (E : Presentation D m)
    (x : PGLLinearization.fieldTest k k ⟶ D.H) :
    E.sl_line.IsStable k x ↔
      ∀ (b : Module.Basis (Fin (n + 2)) k (Fin (n + 2) → k)) (w : Fin (n + 2) → ℚ),
        (∃ i j : Fin (n + 2), w i ≠ w j) →
          minimumBasisWeight E x b w <
            ((∑ i : Fin (n + 2), w i) / (n + 2 : ℚ)) * (m : ℚ) * P.1.eval (m : ℚ) := by
  sorry

end AlgebraicGeometry.HilbertPlucker
