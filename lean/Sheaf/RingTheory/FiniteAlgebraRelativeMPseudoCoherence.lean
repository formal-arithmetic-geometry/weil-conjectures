module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.RingTheory.RelativeMPseudoCoherent
import WeilConjectures.RingTheory.MPseudoCoherent
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.RingTheory.AdjoinRoot

/-! # Relative degreewise pseudo-coherence under a finite algebra map

Source: Stacks Project, More on Algebra, Tag 0673,
lemma-finite-extension-pseudo-coherent, fixed-m clause
(blueprint: lem-sfb-finite-algebra-relative-m-pseudocoherence).
-/

@[expose] public section

set_option autoImplicit false

universe u wA wB wP

open CategoryTheory

namespace DerivedCategory

/-- A finite map of finite type algebras preserves and reflects relative
`m`-pseudo-coherence under ordinary derived restriction of scalars. The restriction
keeps the additive groups and differentials and acts through `algebraMap A B`.
The relative predicates use the given algebra structures over `R`.

Source: Stacks Project, More on Algebra, Tag 0673,
lemma-finite-extension-pseudo-coherent, fixed-m clause
(blueprint: lem-sfb-finite-algebra-relative-m-pseudocoherence).

Proof:
1. If R is the zero ring, unitality makes A, B and all their modules zero, and the
   zero finite free approximation witnesses both predicates for every m. Otherwise
   choose a finite polynomial presentation alpha : P = R[x] -> A and generators y_j
   of B as an A-module. They also generate B as an A-algebra, giving a surjective
   polynomial presentation gamma : T = P[Y] -> B.
   This uses def-sfb-ring-relative-m-pseudocoherent, def-pc-ring-m-pseudo-coherent
   and def-weil-pbc-mv-polynomial-ring.
2. By lem-weil-pbc-finite-algebra-is-integral, each y_j satisfies a monic equation.
   Lift its coefficients through alpha to a monic f_j over P of positive degree;
   a constant equation 1 may first be multiplied by its variable. Then gamma
   factors through C = T/(f_j(Y_j)), compatibly with P -> A -> B.
3. Quotient T successively by the f_j(Y_j). At each step, the preceding ring is a
   polynomial ring in Y_j over the ring of the remaining variables and previous
   quotients. Multiplication by the positive-degree monic f_j is injective, by
   its leading coefficient. Its cokernel is the next quotient. The resulting
   two-term finite free resolution makes that quotient pseudo-coherent over the
   preceding ring (def-pc-ring-pseudo-coherent-complex).
4. By lem-weil-pbc-monic-quotient-free, each successive monic quotient has the
   power basis of exponents below its degree. Induction gives a finite P-basis
   of C consisting of products of these powers. Thus C[0] is pseudo-coherent
   over P. The empty generator list gives C = P.
5. Apply lem-sfb-m-pseudocoherent-algebra-scalar-restriction to each successive
   quotient in step 3, and to P -> C in step 4. This identifies m-pseudo-coherence
   of gamma_*M over T with that of M restricted to C, and with that of M
   restricted to P through A. All scalar actions agree by the commuting maps;
   no tensor product or flatness is used.
6. By lem-sfb-polynomial-presentation-m-pseudocoherence-invariance and
   def-sfb-ring-relative-m-pseudocoherent, the relative predicates are equivalent
   to the absolute predicates on the chosen presentations alpha and gamma.
   These are exactly the two predicates compared in step 5. -/
theorem isMPseudoCoherentRelativeTo_restrictScalars_finite_iff
    (R : Type u) {A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Algebra.FiniteType R B] [Module.Finite A B]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} B)]
    [∀ n : ℕ, HasDerivedCategory.{wP} (ModuleCat.{u} (MvPolynomial (Fin n) R))]
    (m : ℤ) (M : DerivedCategory (ModuleCat.{u} B)) :
    IsMPseudoCoherentRelativeTo R m M ↔
      IsMPseudoCoherentRelativeTo R m
        ((RingDerivedScalarExtension.moduleDerivedRestriction (algebraMap A B)).obj M) := by
  sorry

end DerivedCategory
