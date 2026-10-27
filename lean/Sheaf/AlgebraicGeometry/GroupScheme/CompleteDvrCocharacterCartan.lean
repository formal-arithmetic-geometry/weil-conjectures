module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Sheaf.AlgebraicGeometry.ExistsSchemeOfZariskiCocycle
import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions

/-! # Cocharacter Cartan decomposition over a complete DVR

Source: Alper--Halpern-Leistner--Heinloth, Cartan--Iwahori--Matsumoto decompositions
for reductive groups, Theorem 1.3 (1) implies (3), Definition 3.4 and Lemma 3.6,
printed pp.1, 5--6 (blueprint: lem-sfb-complete-dvr-cocharacter-cartan).

The multiplicative group uses Mathlib's Laurent Hopf algebra over the actual DVR.
The evaluation point is specified by its exact coordinate ring map; it is not an
arbitrary point of the multiplicative group. No residue-field or splitness hypothesis
is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Every rational point of a reductive group over a complete DVR is an integral
point times a cocharacter evaluated at the uniformizer times an integral point.
Source: Alper--Halpern-Leistner--Heinloth, Theorem 1.3 (1) implies (3),
Definition 3.4 and Lemma 3.6, pp.1, 5--6
(blueprint: lem-sfb-complete-dvr-cocharacter-cartan).

Proof:
1. Form X = Spec A[s,t]/(st-pi), with weights (1,-1), and U = D(s) union D(t).
Glue trivial right H-torsors by h_t = g h_s, using lem-galois-glue and the
right-torsor convention of def-sfb-split-solvable-right-torsors. The constant
transition commutes with the right H-action and with scaling on the base.
2. Apply lem-sfb-reductive-nodal-equivariant-torsor-extension. On the branch
Spec k[s], apply lem-sfb-contracting-line-equivariant-torsor-rigidity to compare
the extension with the constant torsor given by its fibre T at the node.
The fibre at s=1 lies in D(s), so it is trivial; hence T has a k-point p.
3. Define lambda_0 by z.p = p lambda_0(z). Commutation with the right action
and the action identity make this a group homomorphism. Lift it by
lem-sfb-complete-dvr-cocharacter-lifting. The equivariant product torsor
P_lambda = X times H has the same fibre at the node; apply
lem-sfb-nodal-equivariant-torsor-rigidity to identify it with the extension.
4. Use invariant coordinates q_s = lambda(s)^(-1) h and q_t = lambda(t) h.
Their transition is q_t = lambda(pi) q_s. An equivariant chart isomorphism
from P_g is multiplication by a constant c_s or c_t in H(A), since scaling
invariance is evaluated at s=1 or t=1. Compatibility gives
c_t g = lambda(pi) c_s, so take a = c_t^(-1), b = c_s.
The Laurent evaluation map sends the coordinate to pi in K, as required by
Remark 1.2 and Definition 3.4. -/
theorem completeDvr_cocharacter_cartan
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (pi : A) (hpi : Irreducible pi)
    [IsAdicComplete (Ideal.span ({pi} : Set A)) A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (H : Grp (Over (Spec (.of A))))
    [IsAffine H.X.left] [Smooth H.X.hom]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (hred : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (f : A →+* Ω),
      ReductiveTorusCentralizer.IsReductive
        ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.obj H))
    (g : (Spec (.of K)).asOver (Spec (.of A)) ⟶ H.X) :
    ∃ (a b : 𝟙_ (Over (Spec (.of A))) ⟶ H.X)
      (lambda : Grp.mk ((Spec (.of (LaurentPolynomial A))).asOver (Spec (.of A))) ⟶ H)
      (t : (Spec (.of K)).asOver (Spec (.of A)) ⟶
        (Spec (.of (LaurentPolynomial A))).asOver (Spec (.of A))),
      t.left = Spec.map (CommRingCat.ofHom
        (LaurentPolynomial.eval₂ (algebraMap A K)
          (Units.mk0 (algebraMap A K pi)
            ((map_ne_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mpr
              hpi.ne_zero)))) ∧
      g = (toUnit ((Spec (.of K)).asOver (Spec (.of A))) ≫ a) *
        (t ≫ lambda.hom.hom) *
        (toUnit ((Spec (.of K)).asOver (Spec (.of A))) ≫ b) := by
  sorry

end AlgebraicGeometry
