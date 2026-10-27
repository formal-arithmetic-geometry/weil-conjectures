module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.NormalScheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Universal openness of finite dominant morphisms to a normal base

Source: Stacks Project, Tags 0F32 and 0BQ3, finite dominant integral specialization;
Tags 0F31, 00H8 and 00I1 for the affine polynomial-test proof.
(blueprint: lem-sfb-finite-dominant-normal-base-universally-open)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite dominant morphism of integral schemes to a normal locally Noetherian
scheme is universally open. The hypothesis `hB` includes the integrality of `B`.

Source: Stacks Project, Tags 0F32 and 0BQ3, finite dominant integral specialization.
(blueprint: lem-sfb-finite-dominant-normal-base-universally-open)

Proof:
1. Choose nonempty affine Noetherian charts `Spec A` of `B` using pqf-def-locnoeth.
   Their inverse images are affine `Spec C`, with `C` finite over `A`, by
   def-weil-finite-integral-morphism. Dominance makes each inverse image nonempty
   and its image dense. Integrality (def-pc-integral-scheme) makes `A` and `C`
   domains. The image lies in the zero locus of the kernel of `A -> C`, so density
   and the zero prime of `A` make the kernel zero. The stalk-localization statement
   lem-weil-pbc-affine-open-stalk-localization and normality of `B` identify all
   maximal localizations of `A` as normal domains. Apply
   lem-weil-pbc-normal-domain-of-local-normal to make `A` integrally closed.
2. For every natural number `n`, the coefficient map on the polynomial rings
   `A[t_1,...,t_n] -> C[t_1,...,t_n]` is injective coefficientwise. Finite module
   generators of `C` over `A` generate the polynomial ring over the polynomial
   ring in `A`: expand each coefficient in those generators and regroup the
   finitely many monomials. They also generate the polynomial algebra. This uses
   def-weil-pbc-mv-polynomial-ring and includes `n = 0`.
3. By lem-weil-pbc-polynomial-ring-domain the polynomial ring in `C` is a domain.
   Iterating lem-weil-pbc-polynomial-ring-normal-domain makes the polynomial ring
   in `A` normal. By lem-weil-pbc-finite-type-algebra-noetherian it is Noetherian.
   Apply lem-weil-pbc-finite-type-noetherian-finite-presentation to the polynomial
   algebra in `C`, and lem-weil-pbc-finite-algebra-is-integral to its finite module
   generators, obtaining finite presentation and integrality over the ring in `A`.
4. Apply lem-weil-pbc-going-down-normal-integral to these inclusions of domains.
   The prime-chain lifting it supplies is exactly the hypothesis of
   lem-sfb-going-down-finitely-presented-open. Thus every polynomial spectral map
   is open, including the map with no variables.
5. The polynomial test lem-sfb-polynomial-test-universally-open (Stacks 0F31)
   makes each affine chart map universally open. Auxiliary schemes in this test
   are arbitrary; no normality, reducedness or Noetherianity is required of them.
6. For an arbitrary `B' -> B`, inverse images of the affine charts cover `B'`.
   By def-pc-fibre-product their restricted projections are the base changes of
   the affine chart maps, since their two projection equations agree. They are
   open by step 5. The image of an open subset under the full projection is open
   on this cover, hence open. This is universal openness of `q`. -/
theorem universallyOpen_of_finite_dominant_normal
    {V B : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian B]
    (q : V ⟶ B) [IsFinite q] [IsDominant q] (hB : IsNormalScheme B) :
    UniversallyOpen q := by
  sorry

end AlgebraicGeometry
