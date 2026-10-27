module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import WeilConjectures.AlgebraicGeometry.FormallySmooth

/-! # Geometric fibres of a binomial plane curve

Source: agent two-axis and Laurent-coordinate calculation, Stacks algebra.tex Tags 00T6/00T7
and more-morphisms.tex Tags 02H0/02H6
(blueprint: lem-sfb-binomial-geometric-fibres).

The auxiliary definitions name the explicit rings, coordinates, quotient inclusions and opens
in this one calculation. No smoothness or geometric property is built into their data.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.BinomialPlaneCurve

noncomputable section

/-- The coordinate ring F[x,y]/(xy-a). Source: the explicit calculation in algebra.tex,
Tags 00T6/00T7 (blueprint: lem-sfb-binomial-geometric-fibres). -/
abbrev Ring (F : Type u) [CommRing F] (a : F) :=
  MvPolynomial (Fin 2) F ⧸ Ideal.span
    {MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C a}

/-- A coordinate class, with indices 0=x and 1=y. Source: algebra.tex, two-axis calculation
(blueprint: lem-sfb-binomial-geometric-fibres). -/
def coord (F : Type u) [CommRing F] (a : F) (i : Fin 2) : Ring F a :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- The binomial affine scheme. Source: algebra.tex, explicit two-axis calculation
(blueprint: lem-sfb-binomial-geometric-fibres). -/
abbrev curve (F : Type u) [CommRing F] (a : F) : Scheme.{u} := Spec (.of (Ring F a))

/-- The structural morphism to Spec F. Source: algebra.tex, two-axis calculation
(blueprint: lem-sfb-binomial-geometric-fibres). -/
def toField (F : Type u) [CommRing F] (a : F) : curve F a ⟶ Spec (.of F) :=
  Spec.map (CommRingCat.ofHom (algebraMap F (Ring F a)))

/-- The ideal of an axis in the zero fibre. Source: algebra.tex, two-axis calculation
(blueprint: lem-sfb-binomial-geometric-fibres). -/
def axisIdeal (F : Type u) [CommRing F] (i : Fin 2) : Ideal (Ring F 0) :=
  Ideal.span {coord F 0 i}

/-- The quotient inclusion of an axis. Source: algebra.tex, two-axis calculation
(blueprint: lem-sfb-binomial-geometric-fibres). -/
def axisMap (F : Type u) [CommRing F] (i : Fin 2) :
    Spec (.of (Ring F 0 ⧸ axisIdeal F i)) ⟶ curve F 0 :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (axisIdeal F i)))

/-- The punctured axis D(x) or D(y). Source: algebra.tex, two-axis calculation
(blueprint: lem-sfb-binomial-geometric-fibres). -/
def puncturedAxis (F : Type u) [CommRing F] (i : Fin 2) : (curve F 0).Opens :=
  PrimeSpectrum.basicOpen (coord F 0 i)

/-- Pairs of polynomials agreeing at zero, as the equalizer of the two evaluation maps.
Source: algebra.tex, explicit restriction calculation
(blueprint: lem-sfb-binomial-geometric-fibres). -/
def axisPairs (F : Type u) [CommRing F] : Subalgebra F (Polynomial F × Polynomial F) :=
  AlgHom.equalizer
    ((Polynomial.aeval (0 : F)).comp (AlgHom.fst F (Polynomial F) (Polynomial F)))
    ((Polynomial.aeval (0 : F)).comp (AlgHom.snd F (Polynomial F) (Polynomial F)))

/-- Every binomial fibre is nonempty, connected, reduced and of pure dimension one;
its local rings have dimension at most one.
Source: algebra.tex, explicit two-axis/Laurent calculation (Tags 00T6/00T7)
(blueprint: lem-sfb-binomial-geometric-fibres).

Proof: for a nonzero scalar, send x to z and y to a/z, with inverse z to x and
z^{-1} to a^{-1}y. The Laurent ring is a domain. Localization of primes and
lem-sc-p1-polynomial-dimension-one bound its dimension by one, while (0)<(z-1)
gives equality even over F_2. Use lem-weil-pbc-spec-domain-stalks-function-field
and def-pc-integral-scheme for reducedness and connectedness. For a=0, restriction
to the axes has kernel (xy) and image the pairs with equal constant terms: lift
(f,g) with common constant c to f(x)+g(y)-c. This is a subring of a product of
domains, hence reduced; localizations remain reduced. Every prime contains x or y,
so the spectrum is the union of the two irreducible axes, each of dimension one.
They meet at (x,y), giving connectedness. Any prime chain lies over an axis and
has length at most one. Finally use lem-weil-pbc-localization-dimension-chains-below-prime
and the stalk-localization statement to bound all local dimensions. -/
theorem geometric_properties (F : Type u) [Field F] (a : F) :
    ConnectedSpace (curve F a) ∧ IsReduced (curve F a) ∧
    (curve F a).IsPureDimension 1 ∧
    ∀ p : curve F a, ringKrullDim ((curve F a).presheaf.stalk p) ≤ 1 := by
  sorry

/-- The specified Laurent-coordinate identification and smoothness for a nonzero scalar.
Source: algebra.tex, Tags 00T6/00T7
(blueprint: lem-sfb-binomial-geometric-fibres).

Proof: define the forward map by x↦z and y↦az^{-1}. Its inverse sends z to x and
z^{-1} to a^{-1}y; the relation xy=a verifies the products and both inverse identities.
The presentation xy-a has unit Jacobian entry y, whose inverse is a^{-1}x.
Apply lem-weil-pbc-standard-smooth-is-smooth and
lem-weil-pbc-smooth-ring-map-iff-smooth-affine. -/
theorem nonzero_fibre (F : Type u) [Field F] (a : F) (ha : a ≠ 0) :
    (∃ e : Ring F a ≃ₐ[F] LaurentPolynomial F,
      e (coord F a 0) = LaurentPolynomial.T 1 ∧
      e (coord F a 1) = LaurentPolynomial.C a * LaurentPolynomial.T (-1)) ∧
    Smooth (toField F a) := by
  sorry

/-- The two axes, their reduced intersection, punctured complement and local crossing.
Source: algebra.tex, explicit two-axis calculation, and more-morphisms.tex Tags 02H0/02H6
(blueprint: lem-sfb-binomial-geometric-fibres).

Proof: restriction has kernel (xy) and image axisPairs, with inverse (f,g)↦f(x)+g(y)-f(0).
The axis quotients are F[y] and F[x]. Every prime contains x or y; the two resulting
closed irreducible lines are incomparable and exhaust the irreducible components.
By lem-weil-pbc-fibre-product-affine-spectra their intersection is the spectrum of
A/(x) tensor_A A/(y)=A/(x,y)=F. Its image is the prime (x,y). The strict chain
(x)<(x,y) is the pullback of (0)<(y) in F[y], so the localization at the crossing
has dimension one by lem-weil-pbc-localization-dimension-chains-below-prime.
The maximality of (x,y) shows its complement is D(x) union D(y). These opens are
disjoint because xy=0; their rings are F[x,x^{-1}] and F[y,y^{-1}]. Use
lem-weil-pbc-principal-localization-open-immersion for these open identifications.
The presentation zw-1 has unit Jacobian entry z, so the opens and their union are
smooth by lem-weil-pbc-standard-smooth-is-smooth,
lem-weil-pbc-smooth-ring-map-iff-smooth-affine and lem-weil-pbc-smooth-local-on-source.
At the crossing take B=F[u,v]/(u^2,v^2), I=(uv). Then I^2=0 and uv≠0. The map
A→B/I sending x to u and y to v cannot lift: all lifts have product uv≠0.
Both test spectra have their unique point at the crossing, so any smooth neighbourhood
would give a lift by formal smoothness, a contradiction. This applies in particular
over every algebraically closed field, in every characteristic. -/
theorem zero_fibre (F : Type u) [Field F] :
    (∃ e : Ring F 0 ≃ₐ[F] axisPairs F,
      (e (coord F 0 0)).val = (Polynomial.X, 0) ∧
      (e (coord F 0 1)).val = (0, Polynomial.X)) ∧
    (∀ i : Fin 2, ∃ e : (Ring F 0 ⧸ axisIdeal F i) ≃ₐ[F] Polynomial F,
      e (Ideal.Quotient.mk (axisIdeal F i) (coord F 0 (1 - i))) = Polynomial.X) ∧
    (∀ i : Fin 2, IsClosedImmersion (axisMap F i)) ∧
    irreducibleComponents (curve F 0) =
      {PrimeSpectrum.zeroLocus {coord F 0 0}, PrimeSpectrum.zeroLocus {coord F 0 1}} ∧
    ∃ p : curve F 0,
      p.asIdeal = Ideal.span {coord F 0 0, coord F 0 1} ∧
      (axisIdeal F 0).IsPrime ∧ axisIdeal F 0 < p.asIdeal ∧
      ringKrullDim ((curve F 0).presheaf.stalk p) = 1 ∧
      (∃ e : pullback (axisMap F 0) (axisMap F 1) ≅ Spec (.of F),
        e.hom = pullback.fst (axisMap F 0) (axisMap F 1) ≫ axisMap F 0 ≫ toField F 0 ∧
        Set.range (pullback.fst (axisMap F 0) (axisMap F 1) ≫ axisMap F 0) = {p}) ∧
      IsReduced (pullback (axisMap F 0) (axisMap F 1)) ∧
      Disjoint (puncturedAxis F 0) (puncturedAxis F 1) ∧
      ((puncturedAxis F 0 : Set (curve F 0)) ∪ puncturedAxis F 1) = {p}ᶜ ∧
      (∀ i : Fin 2, ∃ e : (puncturedAxis F i).toScheme ≅ Spec (.of (LaurentPolynomial F)),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap F (LaurentPolynomial F))) =
          (puncturedAxis F i).ι ≫ toField F 0) ∧
      Smooth ((puncturedAxis F 0 ⊔ puncturedAxis F 1).ι ≫ toField F 0) ∧
      (IsAlgClosed F → ∀ q : curve F 0,
        (∃ U : (curve F 0).Opens, q ∈ U ∧ Smooth (U.ι ≫ toField F 0)) ↔ q ≠ p) := by
  sorry

/-- Extension of coefficients gives the same binomial equation, with the specified variables.
Source: algebra.tex, explicit coefficient-extension calculation
(blueprint: lem-sfb-binomial-geometric-fibres).

Proof: send e tensor h to e*h in E[x,y]/(xy-a_E). The inverse sends coefficients e
to e tensor 1 and the variables to 1 tensor x, 1 tensor y. The tensor relations and
xy=a verify well-definedness and the two inverse identities. Thus the same calculations
apply over every extension, without perfection or a characteristic restriction. -/
theorem coefficient_extension (F : Type u) [Field F] (a : F)
    (E : Type v) [Field E] [Algebra F E] :
    ∃ e : E ⊗[F] Ring F a ≃ₐ[E] Ring E (algebraMap F E a),
      e (1 ⊗ₜ[F] coord F a 0) = coord E (algebraMap F E a) 0 ∧
      e (1 ⊗ₜ[F] coord F a 1) = coord E (algebraMap F E a) 1 := by
  sorry

/-- Scheme base change is the binomial curve with extended coefficients, over the new field.
Source: algebra.tex, coefficient-extension calculation
(blueprint: lem-sfb-binomial-geometric-fibres).

Proof: lem-weil-pbc-fibre-product-affine-spectra identifies the pullback with the spectrum
of the tensor product. Swap its factors and apply coefficient_extension. The resulting
isomorphism respects the E-algebra structures, hence the second pullback projection.
Apply geometric_properties, nonzero_fibre and zero_fibre over E. Field embeddings preserve
zero and nonzero, so every preceding conclusion persists, including for algebraically
closed extensions. -/
theorem field_baseChange (F : Type u) [Field F] (a : F)
    (E : Type u) [Field E] [Algebra F E] :
    ∃ e : pullback (toField F a) (Spec.map (CommRingCat.ofHom (algebraMap F E))) ≅
        curve E (algebraMap F E a),
      e.hom ≫ toField E (algebraMap F E a) =
        pullback.snd (toField F a) (Spec.map (CommRingCat.ofHom (algebraMap F E))) := by
  sorry

end
end AlgebraicGeometry.BinomialPlaneCurve
