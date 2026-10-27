/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.RealizedPullbackComparisons
public import Sheaf.Paper.SimultaneousIntegralPullbackComparisons
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.SixFunctors.FrobeniusPointTransport

/-! # Rational pullback and geometric point fibres

Source: blueprint sec-deligne-laumon-a1/sk-p-dl-a1-some-weight,
lem-fd-realified-kernel-real.proof.md, Step 2 (pullback along the first projection);
Deligne, Weil II (1.1.7)--(1.1.10).
(blueprint: lem-fd-rational-pullback-fibre-comparison).

The comparison is the fibre of the inverse specified rational compositor. Scalar
comparisons use the inverse sections comparison followed by the specified pullback
comparison. All categories are the published raw rational and common-stage categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
namespace RationalPullbackFibre

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The point restriction followed by the recorded rational sections fibre.
Source: blueprint Step 2, J_z (blueprint: lem-fd-rational-pullback-fibre-comparison). -/
def fibre {X : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    (z : Spec (.of D.k) ⟶ X) :
    sfRationalConstructibleCategory l E X ⥤
      (DerivedCategory.pointFiniteDimensional E).FullSubcategory :=
  @rationalDerivedPullback l _ E _ _ _ _ _ z
    (frobeniusPointPrimeInvertible D l hl) inferInstance ⋙ pointRationalFibre D l hl E

/-- The published rational coefficient extension, with its proof-only parameter zero.
Source: blueprint Step 2, T (blueprint: lem-fd-rational-pullback-fibre-comparison). -/
abbrev scalar (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{u}) :=
  sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι

variable (C : IntegralComparisonSystem.{u} l)
  {X Y : Scheme.{u}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The actual component: fibre of the inverse specified compositor, then transport
along the chosen equality of geometric points.
Source: blueprint Step 2, c^E (blueprint: lem-fd-rational-pullback-fibre-comparison). -/
def component (f : X ⟶ Y) (z : Spec (.of D.k) ⟶ X) (x : Spec (.of D.k) ⟶ Y)
    (h : z ≫ f = x) (M : sfRationalConstructibleCategory l E Y) :
    (fibre D l hl E z).obj ((rationalDerivedPullback l E f).obj M) ≅
      (fibre D l hl E x).obj M :=
  letI := frobeniusPointPrimeInvertible D l hl
  (pointRationalFibre D l hl E).mapIso
    ((integralComparisonRationalComposition l E C z f M).symm ≪≫
      eqToIso (congrArg (fun g ↦ (rationalDerivedPullback l E g).obj M) h))

/-- The specified fibre scalar comparison b_z: beta followed by Fib(a_z).
Source: blueprint Step 2, b (blueprint: lem-fd-rational-pullback-fibre-comparison). -/
def scalarComparison (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)
    (z : Spec (.of D.k) ⟶ X) (M : sfRationalConstructibleCategory l E X) :
    (DerivedCategory.pointFdScalarExtension ι.toRingHom).obj ((fibre D l hl E z).obj M) ≅
      (fibre D l hl L z).obj ((scalar l E L ι X).obj M) :=
  letI := frobeniusPointPrimeInvertible D l hl
  (pointRationalFibreScalarIso D l hl E L ι).symm.app
      ((rationalDerivedPullback l E z).obj M) ≪≫
    (pointRationalFibre D l hl L).mapIso
      ((integralComparisonRationalScalar l E C L ι z).app M)

/-- Identity coefficient extensions use the actual multiplication and completeness units.
Source: blueprint Step 2, identity law
(blueprint: lem-fd-rational-pullback-fibre-comparison). -/
def scalarUnit (z : Spec (.of D.k) ⟶ X) : Prop :=
  ∀ M : sfRationalConstructibleCategory l E X,
    ((scalarComparison D l hl E C E (AlgHom.id ℚ_[l] E) z M).hom).hom ≫
      ((fibre D l hl E z).map
        ((sfRationalScalarUnit l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app M)).hom =
      (DerivedCategory.fieldScalarUnit E).hom.app ((fibre D l hl E z).obj M).obj

/-- The b comparisons commute with the specified completed scalar associator and the
ordinary module tensor associator, including repeated fields.
Source: blueprint Step 2, tower law
(blueprint: lem-fd-rational-pullback-fibre-comparison). -/
def scalarTower (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (H : Type u) [Field H] [Algebra ℚ_[l] H]
    [FiniteDimensional ℚ_[l] H] (j : L →ₐ[ℚ_[l]] H) (z : Spec (.of D.k) ⟶ X) : Prop :=
  ∀ M : sfRationalConstructibleCategory l E X,
    (DerivedCategory.pointFdScalarExtension j.toRingHom).map
        (scalarComparison D l hl E C L ι z M).hom ≫
      (scalarComparison D l hl L C H j z ((scalar l E L ι X).obj M)).hom ≫
      (fibre D l hl H z).map
        ((sfRationalScalarComp l E L ι X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
          H j).hom.app M) =
      (pointFibreFdTensorTower ι.toRingHom j.toRingHom).hom.app
        ((fibre D l hl E z).obj M) ≫
      (scalarComparison D l hl E C H (j.comp ι) z M).hom

variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Common-stage point restriction followed by the recorded common-stage sections fibre.
Source: blueprint Step 2, J_z over Qbar
(blueprint: lem-fd-rational-pullback-fibre-comparison). -/
def commonFibre (z : Spec (.of D.k) ⟶ X) :
    generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤ DerivedCategory.PointFdQbar l Ω :=
  letI := frobeniusPointPrimeInvertible D l hl
  commonStageDerivedPullback l Ω z ⋙ pointQbarFibre D l hl Ω

/-- The class of the prescribed finite-stage component, including the existing Shrink
coefficient identification used by pointStageFibre. No representative is chosen.
Source: blueprint Step 2, descent (blueprint: lem-fd-rational-pullback-fibre-comparison). -/
def commonRepresentative (f : X ⟶ Y) (z : Spec (.of D.k) ⟶ X)
    (x : Spec (.of D.k) ⟶ Y) (h : z ≫ f = x)
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :=
  (DerivedCategory.pointFdQbarStage l Ω P.stage).map
    ((DerivedCategory.pointFdScalarExtension
      (Shrink.algEquiv ℚ_[l] P.stage.val).toRingHom).map
      (component D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)
        C f z x h P.obj).hom)

/-- The finite-stage natural-isomorphism family, indexed by the existing finite subfields.
Source: blueprint Step 2, finite-stage assertion
(blueprint: lem-fd-rational-pullback-fibre-comparison). -/
def Family (f : X ⟶ Y) (z : Spec (.of D.k) ⟶ X) (x : Spec (.of D.k) ⟶ Y) :=
  ∀ F : AlgebraicallyClosedCoefficients.Index l Ω,
    rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) f ⋙
      fibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) z ≅
    fibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) x

/-- All clauses of the comparison: prescribed components, the derived scalar square,
identity and tower laws at both points, and descent with the prescribed component class.
The common-stage arrows are morphisms in the derived category of Qbar-modules and
therefore are Qbar-linear, before taking cohomology.
Source: blueprint Step 2 (blueprint: lem-fd-rational-pullback-fibre-comparison). -/
def ComparisonStatement (f : X ⟶ Y) (z : Spec (.of D.k) ⟶ X)
    (x : Spec (.of D.k) ⟶ Y) (h : z ≫ f = x) : Prop :=
  ∃ c : Family D l hl Ω f z x,
    (∀ (F : AlgebraicallyClosedCoefficients.Index l Ω)
      (M : sfRationalConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) Y),
      (c F).app M = component D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) C f z x h M) ∧
    (∀ (F G : AlgebraicallyClosedCoefficients.Index l Ω) (i : F ≤ G)
      (M : sfRationalConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) Y),
      (scalarComparison D l hl _ C _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω F G i) z
        ((rationalDerivedPullback l _ f).obj M)).hom ≫
      (fibre D l hl _ z).map
        ((integralComparisonRationalScalar l _ C _
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω F G i) f).hom.app M) ≫
      (c G).hom.app ((scalar l _ _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω F G i) Y).obj M) =
      (DerivedCategory.pointFdScalarExtension
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω F G i).toRingHom).map
        ((c F).hom.app M) ≫
      (scalarComparison D l hl _ C _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω F G i) x M).hom) ∧
    (∀ F : AlgebraicallyClosedCoefficients.Index l Ω,
      scalarUnit D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) C z ∧
      scalarUnit D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) C x) ∧
    (∀ (F G H : AlgebraicallyClosedCoefficients.Index l Ω) (i : F ≤ G) (j : G ≤ H),
      scalarTower D l hl _ C _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω F G i) _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω G H j) z ∧
      scalarTower D l hl _ C _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω F G i) _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω G H j) x) ∧
    ∃ γ : commonStageDerivedPullback l Ω f ⋙ commonFibre D l hl Ω z ≅
        commonFibre D l hl Ω x,
      ∀ P : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
        HEq (γ.hom.app P) (commonRepresentative D l hl C Ω f z x h P)

/-- The actual geometric base change of a morphism over the finite field.
Source: blueprint Step 2, f=f_0 base-changed to k
(blueprint: lem-fd-rational-pullback-fibre-comparison). -/
def geometricMap {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber Y₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

/-- The comparison on the given finite-type models, with prime invertibility supplied
by the finite-field datum rather than imposed as an additional geometric assumption.
Source: blueprint Step 2 (blueprint: lem-fd-rational-pullback-fibre-comparison). -/
def ModelStatement (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (h : z ≫ geometricMap D f₀ = x) : Prop :=
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl Y₀
  ComparisonStatement D l hl C Ω (geometricMap D f₀) z x h

end RationalPullbackFibre

/-- The canonical rational pullback fibre comparison, scalar square and common-stage
natural isomorphism for every constructible complex.
Source: blueprint sec-deligne-laumon-a1/sk-p-dl-a1-some-weight,
lem-fd-realified-kernel-real.proof.md, Step 2; Deligne Weil II (1.1.7)--(1.1.10).
(blueprint: lem-fd-rational-pullback-fibre-comparison).

Proof (the DAG plan):
1. Use the single normalized comparison system of
lem-trf-integral-pullback-comparison-realization. For h=z and k=f its rationalized
compositor is d_E. Apply the point fibre to its inverse. Naturality and functoriality
produce c^E, with inverse Fib(d_E), on the full constructible category.
2. Write beta for the inverse rational sections comparison of
lem-weil-point-sections-scalar-extension. The specified b_z is Fib(a_z) beta.
The mixed compositor/scalar equation specializes to
P_z(a_f) a_z T(d_E) = d_L a_x. Multiply by inverse d_L and inverse T(d_E).
3. Apply Fib_L and precompose with beta. Naturality of beta moves T(d_E inverse)
past beta, giving exactly c_L J_z(a_f) b_z = b_x (c_E tensor L) as a derived
morphism equality, before taking any cohomology.
4. For identity fields the two unit identifications are multiplication and completeness.
For a tower, beta-naturality moves the inner a_z across the outer beta; the tower
laws for a and beta combine the two extensions into the direct one. The tensor
associator is the specified one, conjugated by completion chi. The same holds at x;
substitution proves that the scalar square also respects the unit and tower laws.
5. Represent objects and arrows over common finite fields using
def-weil-algebraically-closed-coefficients. Conjugation by A=J_z(a_f)b_z and B=b_x
is the prescribed action of the two composite functors. The scalar square is
c_L A = B(c_E tensor L), so the class of c_E and its inverse are unchanged by
extension. For a common-stage arrow, conjugate its finite-stage naturality square
by A and B. Eventual equality of representatives and the tower law make the result
independent of the common field and representative. Each component is a derived
module morphism; after realization it is Qbar-linear. A scalar belongs to a finite
extension, so all scalar relations follow at a common finite stage. No Weil structure,
Weil-stable integral lattice, or finite Tor-amplitude assumption enters this argument. -/
theorem rationalPullbackFibreComparison (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (h : z ≫ RationalPullbackFibre.geometricMap D f₀ = x) :
    ∃ C : IntegralComparisonSystem.{u} l,
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
        (ι : E →ₐ[ℚ_[l]] L), IntegralComparisonRealizationCoherence l E L ι C) ∧
      RationalPullbackFibre.ModelStatement D l hl C Ω X₀ Y₀ f₀ z x h := by
  sorry

end WeilConjectures
