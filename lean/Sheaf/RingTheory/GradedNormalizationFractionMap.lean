module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Module.GradedModuleAwayRestriction

/-!
# Intrinsic homogeneous fractions in a normalization residue algebra

Source: Stacks Project, curves.tex, Tag 0CBT (remark-quadratic-extension),
omitted comparison of constructions (2) and (3)
(blueprint: lem-sfb-graded-normalization-fraction-map).

The scalar condition is expressed on representatives of A/m; consequently the
unique ring homomorphism below is precisely a homomorphism of A/m-algebras.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v u' v'

open CategoryTheory AlgebraicGeometry Ideal

namespace Ideal

variable {A : Type u} [CommRing A]

/-- The degree-n subgroup of the existing associated graded ring.
Source: Stacks Project, Algebra, Section 00JM
(blueprint: lem-sfb-graded-normalization-fraction-map). -/
def associatedGradedGrading (J : Ideal A) (n : ℕ) : AddSubgroup (associatedGraded J) :=
  (DirectSum.of (associatedGradedPiece J) n).range

/-- The component ranges respect the existing multiplication and unit.
Source: Stacks Project, Algebra, Section 00JM and Lemma 05GH
(blueprint: lem-sfb-graded-normalization-fraction-map).
Proof: the unit is the inclusion of the class of one in degree zero. For elements
in the ranges of degrees n and m, choose preimages under the inclusions. The
homogeneous product formula puts their product in the range of degree n+m. -/
theorem associatedGradedGrading_monoid (J : Ideal A) :
    SetLike.GradedMonoid (associatedGradedGrading J) := by
  sorry

/-- Recomposition of the component ranges is bijective.
Source: Stacks Project, Algebra, Section 00JM
(blueprint: lem-sfb-graded-normalization-fraction-map).
Proof: each range is identified with its original component by injectivity of
DirectSum.of. Under these identifications recomposition is the identity on the
original direct sum. Its inverse decomposes a finitely supported family into its
single-component families. Thus existence and uniqueness hold, including zero. -/
theorem associatedGradedGrading_isInternal (J : Ideal A) :
    DirectSum.IsInternal (associatedGradedGrading J) := by
  sorry

/-- The internal grading of the recorded direct sum, with its unique decomposition.
Source: Stacks Project, Algebra, Section 00JM
(blueprint: lem-sfb-graded-normalization-fraction-map). -/
instance associatedGradedGradingRing (J : Ideal A) : GradedRing (associatedGradedGrading J) where
  __ := associatedGradedGrading_monoid J
  __ := (associatedGradedGrading_isInternal J).chooseDecomposition

end Ideal

namespace Ideal

/-- The initial class of a representative in an ideal power.
Source: Stacks Project, Algebra, Section 00JM
(blueprint: lem-sfb-graded-normalization-fraction-map). -/
def associatedGradedClass {A : Type u} [CommRing A] (J : Ideal A) (n : ℕ)
    (a : ↥(J ^ n)) : associatedGraded J :=
  DirectSum.of (associatedGradedPiece J) n (Submodule.Quotient.mk a)

/-- The initial class, viewed in its homogeneous subgroup.
Source: Stacks Project, Algebra, Section 00JM
(blueprint: lem-sfb-graded-normalization-fraction-map). -/
def associatedGradedClassHomogeneous {A : Type u} [CommRing A] (J : Ideal A) (n : ℕ)
    (a : ↥(J ^ n)) : associatedGradedGrading J n :=
  ⟨associatedGradedClass J n a, ⟨Submodule.Quotient.mk a, rfl⟩⟩

end Ideal

namespace GradedNormalization

/-- The extended maximal ideal, with the actual structural ring homomorphism.
Source: Stacks Project, curves.tex, Tag 0CBT(2)
(blueprint: lem-sfb-graded-normalization-fraction-map). -/
def residueIdeal {A : Type u} {B : Type v} [CommRing A] [IsLocalRing A] [CommRing B]
    (φ : A →+* B) : Ideal B :=
  (IsLocalRing.maximalIdeal A).map φ

/-- The degree-one initial form, including its homogeneous membership.
Source: Stacks Project, curves.tex, Tag 0CBT(3)
(blueprint: lem-sfb-graded-normalization-fraction-map). -/
def linearForm {A : Type u} [CommRing A] [IsLocalRing A]
    (f : IsLocalRing.maximalIdeal A) :
    associatedGradedGrading (IsLocalRing.maximalIdeal A) 1 :=
  associatedGradedClassHomogeneous _ 1 ⟨f.val, by simp only [pow_one]; exact f.property⟩

/-- The actual degree-zero homogeneous localization chart at the initial form.
Source: Stacks Project, curves.tex, Tag 0CBT(3)
(blueprint: lem-sfb-graded-normalization-fraction-map). -/
abbrev Chart {A : Type u} [CommRing A] [IsLocalRing A]
    (f : IsLocalRing.maximalIdeal A) : Type u :=
  HomogeneousLocalization.Away (associatedGradedGrading (IsLocalRing.maximalIdeal A))
    (linearForm f).val

/-- The fraction in_n(d)/in_1(f)^n in the actual homogeneous localization.
Source: Stacks Project, curves.tex, Tag 0CBT, omitted comparison (2)-(3)
(blueprint: lem-sfb-graded-normalization-fraction-map). -/
def fraction {A : Type u} [CommRing A] [IsLocalRing A]
    (f : IsLocalRing.maximalIdeal A) (n : ℕ)
    (d : ↥((IsLocalRing.maximalIdeal A) ^ n)) : Chart f :=
  HomogeneousLocalization.Away.mk _ (d := (1 : ℕ)) (linearForm f).property n
    (associatedGradedClass _ n d) (by
      simp only [nsmul_eq_mul, mul_one]
      exact ⟨Submodule.Quotient.mk d, rfl⟩)

/-- The overlap coordinate in_1(g)/in_1(f) in the f-chart.
Source: Stacks Project, constructions.tex, Tag 01M4
(blueprint: lem-sfb-graded-normalization-fraction-map). -/
def overlapCoordinate {A : Type u} [CommRing A] [IsLocalRing A]
    (f g : IsLocalRing.maximalIdeal A) : Chart f :=
  fraction f 1 ⟨g.val, by simpa only [pow_one] using g.property⟩

/-- Characterization on all fractions, without a choice of division coefficients.
The existence and uniqueness of b are conclusions of the theorem below, rather
than assumptions of this predicate. Degree zero records the quotient scalar map.
Source: Stacks Project, curves.tex, Tag 0CBT, omitted comparison (2)-(3)
(blueprint: lem-sfb-graded-normalization-fraction-map). -/
def FractionFormula {A : Type u} {B : Type v} [CommRing A] [IsLocalRing A] [CommRing B]
    (φ : A →+* B) (f : IsLocalRing.maximalIdeal A)
    (θ : Chart f →+* B ⧸ residueIdeal φ) : Prop :=
  ∀ (n : ℕ) (d : ↥((IsLocalRing.maximalIdeal A) ^ n)) (b : B),
    φ f.val ^ n * b = φ d.val → θ (fraction f n d) = Ideal.Quotient.mk (residueIdeal φ) b

/-- Unique division and the unique residue-algebra homomorphism on the full localization.
In particular its formula is independent of both lifts and arbitrary localization
representatives, including extra-power torsion relations.
Source: Stacks Project, curves.tex, Tag 0CBT, omitted comparison (2)-(3)
(blueprint: lem-sfb-graded-normalization-fraction-map).
Proof: (1) m^n B=(mB)^n=f^n B, so coefficients exist; cancel f repeatedly for
uniqueness. (2) Changing d by m^(n+1) changes b by fB. (3) An equality of
fractions gives k with f^(k+m)d-f^(k+n)e in m^(k+n+m+1). Substitute the division
coefficients and cancel f^(k+n+m); their difference is in fB. This includes
relations needing k>0 and never cancels the initial form. (4) Addition uses
numerator f^m d+f^n e and multiplication uses de. Uniqueness of division proves
the ring laws and the degree-zero scalar formula. Every chart element is such
a fraction, so the homomorphism is unique. -/
theorem existsUnique_fractionMap {A : Type u} {B : Type v}
    [CommRing A] [IsLocalRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Injective φ) (f : IsLocalRing.maximalIdeal A)
    (hgen : residueIdeal φ = Ideal.span {φ f.val})
    (hreg : Function.Injective (fun b : B ↦ φ f.val * b)) :
    (∀ (n : ℕ) (d : ↥((IsLocalRing.maximalIdeal A) ^ n)),
      ∃! b : B, φ f.val ^ n * b = φ d.val) ∧
    ∃! θ : Chart f →+* B ⧸ residueIdeal φ, FractionFormula φ f θ := by
  sorry

/-- The uniquely characterized fraction map; only the proof of its characterization
is postponed, and no arbitrary ring homomorphism is chosen.
Source: Stacks Project, curves.tex, Tag 0CBT, omitted comparison (2)-(3)
(blueprint: lem-sfb-graded-normalization-fraction-map). -/
def fractionMap {A : Type u} {B : Type v} [CommRing A] [IsLocalRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Injective φ) (f : IsLocalRing.maximalIdeal A)
    (hgen : residueIdeal φ = Ideal.span {φ f.val})
    (hreg : Function.Injective (fun b : B ↦ φ f.val * b)) :
    Chart f →+* B ⧸ residueIdeal φ :=
  Classical.choose (existsUnique_fractionMap φ hφ f hgen hreg).2.exists

/-- Two regular generators differ by a unit, with the full residue fraction formula.
This algebraic statement allows different universes for A and B.
Source: Stacks Project, curves.tex, Tag 0CBT, omitted comparison (2)-(3)
(blueprint: lem-sfb-graded-normalization-fraction-map).
Proof: write g=fu and f=gv using unique division. Cancelling f gives uv=1,
so u is a unit with inverse v. Multiplying b_f(d) v^n by g^n gives d;
uniqueness of division gives b_g(d)=b_f(d) v^n. The fraction formula
then gives the residue identity, including degree zero. -/
theorem fractionMap_changeDenominator_formula {A : Type u} {B : Type v}
    [CommRing A] [IsLocalRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Injective φ)
    (f g : IsLocalRing.maximalIdeal A)
    (hfgen : residueIdeal φ = Ideal.span {φ f.val})
    (hfreg : Function.Injective (fun b : B ↦ φ f.val * b))
    (hggen : residueIdeal φ = Ideal.span {φ g.val})
    (hgreg : Function.Injective (fun b : B ↦ φ g.val * b)) :
    ∃ w : Bˣ, φ g.val = φ f.val * w.val ∧
      φ f.val = φ g.val * (↑w⁻¹ : B) ∧
      fractionMap φ hφ f hfgen hfreg (overlapCoordinate f g) =
        Ideal.Quotient.mk (residueIdeal φ) w.val ∧
      ∀ (n : ℕ) (d : ↥((IsLocalRing.maximalIdeal A) ^ n)) (b c : B),
        φ f.val ^ n * b = φ d.val → φ g.val ^ n * c = φ d.val →
        c = b * (↑w⁻¹ : B) ^ n ∧
        fractionMap φ hφ g hggen hgreg (fraction g n d) =
          fractionMap φ hφ f hfgen hfreg (fraction f n d) *
            Ideal.Quotient.mk (residueIdeal φ) ((↑w⁻¹ : B) ^ n) := by
  sorry

/-- Two denominators give the same map to Proj after the actual chart inclusions.
Source: Stacks Project, curves.tex, Tag 0CBT; constructions.tex, Tag 01M4
(blueprint: lem-sfb-graded-normalization-fraction-map).
Proof: the overlap is the chart at ell_f*ell_g, canonically the localization
of either chart at the other linear form divided by its own. Its coordinate
ell_g/ell_f is sent to the unit [g/f], and its inverse to [f/g]. The fraction
formula gives equality of the two extended maps. Spec reverses these maps,
so both composites with the standard chart inclusions agree. -/
theorem fractionMap_changeDenominator {A : Type u} {B : Type u}
    [CommRing A] [IsLocalRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Injective φ)
    (f g : IsLocalRing.maximalIdeal A)
    (hfgen : residueIdeal φ = Ideal.span {φ f.val})
    (hfreg : Function.Injective (fun b : B ↦ φ f.val * b))
    (hggen : residueIdeal φ = Ideal.span {φ g.val})
    (hgreg : Function.Injective (fun b : B ↦ φ g.val * b)) :
    (Spec.map (CommRingCat.ofHom (fractionMap φ hφ f hfgen hfreg)) ≫
      Proj.awayι _ (linearForm f).val (linearForm f).property (by decide)) =
    (Spec.map (CommRingCat.ofHom (fractionMap φ hφ g hggen hgreg)) ≫
      Proj.awayι _ (linearForm g).val (linearForm g).property (by decide)) := by
  sorry

/-- The overlap comparison and the common residue map, characterized on fractions.
The overlap is the ordinary localization of the f-chart at in_1(g)/in_1(f).
The comparison from the g-chart sends in_n(d)/in_1(g)^n to the f-fraction times
this coordinate to the power -n; the inverse coordinate is invSelf.
Source: Stacks Project, constructions.tex, Tag 01M4; curves.tex, Tag 0CBT
(blueprint: lem-sfb-graded-normalization-fraction-map).
Proof: step 6 identifies the common product chart with the localization of the
f-chart at t=in_1(g)/in_1(f), and of the g-chart at its inverse s. Restriction
preserves ordinary fractions, giving the displayed formula. By step 5 the
image of t is the unit [g/f], so the localization universal property supplies
ψ. Both composites agree on all homogeneous fractions by the division formula,
and hence agree everywhere. All fractions generate the g-chart, so ρ is unique. -/
theorem fractionMap_overlap {A : Type u} {B : Type v}
    [CommRing A] [IsLocalRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Injective φ)
    (f g : IsLocalRing.maximalIdeal A)
    (hfgen : residueIdeal φ = Ideal.span {φ f.val})
    (hfreg : Function.Injective (fun b : B ↦ φ f.val * b))
    (hggen : residueIdeal φ = Ideal.span {φ g.val})
    (hgreg : Function.Injective (fun b : B ↦ φ g.val * b)) :
    ∃! ρ : Chart g →+* Localization.Away (overlapCoordinate f g),
      (∀ (n : ℕ) (d : ↥((IsLocalRing.maximalIdeal A) ^ n)),
        ρ (fraction g n d) =
          algebraMap (Chart f) (Localization.Away (overlapCoordinate f g)) (fraction f n d) *
            IsLocalization.Away.invSelf (overlapCoordinate f g) ^ n) ∧
      ∃ ψ : Localization.Away (overlapCoordinate f g) →+* B ⧸ residueIdeal φ,
        ψ.comp (algebraMap (Chart f) (Localization.Away (overlapCoordinate f g))) =
          fractionMap φ hφ f hfgen hfreg ∧
        ψ.comp ρ = fractionMap φ hφ g hggen hgreg := by
  sorry

/-- Local ring and compatible algebra isomorphisms induce the graded and residue
isomorphisms and intertwine the uniquely characterized fraction maps.
The maps are conclusions, with their action on every representative specified;
there is no hypothesis supplying an arbitrary comparison map.
Source: Stacks Project, curves.tex, Tag 0CBT, omitted comparison (2)-(3)
(blueprint: lem-sfb-graded-normalization-fraction-map).
Proof: step 7 transports ideal powers along α and its inverse. It therefore
induces a unique graded ring isomorphism on the classes of representatives,
and a unique chart isomorphism on all fractions. Compatibility with β sends
mB onto m'B', giving the unique quotient isomorphism. The transported generator
still generates m'B', and its multiplication is injective by conjugating the
old multiplier by β. Applying β to f^n b=φ(d) proves that the transported
coefficient is the unique coefficient for α(d). The square thus commutes on
every homogeneous fraction. These fractions exhaust the chart. -/
theorem fractionMap_natural {A : Type u} {B : Type v} {A' : Type u'} {B' : Type v'}
    [CommRing A] [IsLocalRing A] [CommRing B]
    [CommRing A'] [IsLocalRing A'] [CommRing B']
    (φ : A →+* B) (hφ : Function.Injective φ) (φ' : A' →+* B')
    (α : A ≃+* A') (β : B ≃+* B')
    (hcompat : ∀ a : A, β (φ a) = φ' (α a))
    (f : IsLocalRing.maximalIdeal A)
    (hgen : residueIdeal φ = Ideal.span {φ f.val})
    (hreg : Function.Injective (fun b : B ↦ φ f.val * b)) :
    ∃ (f' : IsLocalRing.maximalIdeal A') (hφ' : Function.Injective φ')
      (hgen' : residueIdeal φ' = Ideal.span {φ' f'.val})
      (hreg' : Function.Injective (fun b : B' ↦ φ' f'.val * b)),
      f'.val = α f.val ∧
      (∃! κ : (A ⧸ IsLocalRing.maximalIdeal A) ≃+* (A' ⧸ IsLocalRing.maximalIdeal A'),
        ∀ a : A, κ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal A') (α a)) ∧
      (∃! U : associatedGraded (IsLocalRing.maximalIdeal A) ≃+*
          associatedGraded (IsLocalRing.maximalIdeal A'),
        ∀ (n : ℕ) (d : ↥((IsLocalRing.maximalIdeal A) ^ n))
          (d' : ↥((IsLocalRing.maximalIdeal A') ^ n)),
          α d.val = d'.val →
          U (associatedGradedClass _ n d) = associatedGradedClass _ n d') ∧
      (∃! p : (Chart f ≃+* Chart f') ×
          ((B ⧸ residueIdeal φ) ≃+* (B' ⧸ residueIdeal φ')),
        (∀ (n : ℕ) (d : ↥((IsLocalRing.maximalIdeal A) ^ n))
          (d' : ↥((IsLocalRing.maximalIdeal A') ^ n)),
          α d.val = d'.val → p.1 (fraction f n d) = fraction f' n d') ∧
        (∀ b : B, p.2 (Ideal.Quotient.mk (residueIdeal φ) b) =
          Ideal.Quotient.mk (residueIdeal φ') (β b))) ∧
      ∀ p : (Chart f ≃+* Chart f') ×
          ((B ⧸ residueIdeal φ) ≃+* (B' ⧸ residueIdeal φ')),
        ((∀ (n : ℕ) (d : ↥((IsLocalRing.maximalIdeal A) ^ n))
          (d' : ↥((IsLocalRing.maximalIdeal A') ^ n)),
          α d.val = d'.val → p.1 (fraction f n d) = fraction f' n d') ∧
        (∀ b : B, p.2 (Ideal.Quotient.mk (residueIdeal φ) b) =
          Ideal.Quotient.mk (residueIdeal φ') (β b))) →
        p.2.toRingHom.comp (fractionMap φ hφ f hgen hreg) =
          (fractionMap φ' hφ' f' hgen' hreg').comp p.1.toRingHom := by
  sorry

/-- An isomorphism of reduced local rings extends canonically to their integral
closures in the total fraction rings by the actual Mathlib fraction isomorphism.
Compatibility with α supplies the β required by fractionMap_natural.
Source: Stacks Project, curves.tex, Tag 0CBT, construction (2)
(blueprint: lem-sfb-graded-normalization-fraction-map).
Proof: step 8 transports non-zero-divisors by α and its inverse, so localization
sends a/r to α(a)/α(r); this is IsFractionRing.ringEquivOfRingEquiv. Transporting
the coefficients of a monic polynomial preserves its root equation, so this
isomorphism restricts to the integral closures, with inverse obtained from
α.symm. The formula in the total fraction ring specifies every value, proving
uniqueness. On elements of A it is α, so the compatibility needed in step 7
holds. Thus the preceding naturality theorem applies to normalization. -/
theorem normalization_extension {A : Type u} {A' : Type u'}
    [CommRing A] [IsLocalRing A] [IsReduced A]
    [CommRing A'] [IsLocalRing A'] [IsReduced A'] (α : A ≃+* A') :
    ∃! β : integralClosure A (FractionRing A) ≃+* integralClosure A' (FractionRing A'),
      (∀ b : integralClosure A (FractionRing A),
        (β b).val =
          (IsFractionRing.ringEquivOfRingEquiv α : FractionRing A ≃+* FractionRing A') b.val) ∧
      ∀ a : A, β (algebraMap A (integralClosure A (FractionRing A)) a) =
        algebraMap A' (integralClosure A' (FractionRing A')) (α a) := by
  sorry

end GradedNormalization
