module
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.IntegralRationalQbarCompactSupport
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.SfIntegralDirectImageConstructible
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.Paper.FiniteCompactSupportConstructibility
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.Paper.SfIntegralCompactSupportConstructible
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction

/-!
# Direct images preserve bounded constructibility

Source: Weil blueprint, `def-weil-ordinary-compact-cohomology` (blueprint:
lem-weil-structure-direct-images-constructible).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Coefficient)

/-- The coefficient prime is a unit in the finite-field fibre.
Source: blueprint `def-weil-ordinary-compact-cohomology`, finite-field hypotheses
(blueprint: lem-weil-structure-direct-images-constructible).
Proof: the cardinality of the base field gives characteristic D.p, and its algebraic
closure has the same characteristic. If the image of l vanished, D.p would divide l.
Since both are prime, this would force l = D.p, contrary to hl. Thus l is nonzero
in the field D.k, and hence is a unit. -/
theorem finiteFieldDatumPrimeUnit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) :
    IsUnit (l : D.k) := by
  sorry

/-- For the finite-field datum and separated finite-type structure morphism, ordinary and
compact-support direct images of bounded constructible objects remain in the corresponding
bounded constructible categories at all four coefficient levels.  The statement records the
finite level with the intrinsic constructibility predicate, the integral level with the
specified derived-limit direct image and compact-support value, and the rational and
common-stage levels by the scalar-localization and finite-stage constructions.
Source: blueprint node `def-weil-ordinary-compact-cohomology`, order 1510
(blueprint: lem-weil-structure-direct-images-constructible).
Proof:
1. The finite-field datum makes k algebraically closed of characteristic p; l ≠ p
makes l invertible (finiteFieldDatumPrimeUnit). The structure morphism is separated
and finite type, so the finite-type constructibility theorems apply.
2. By lem-sf-proetale-constructible-origin, the finite-level input has etale origin.
Apply thm-dg-finite-type-constructibility on the etale site, then
prop-weil-pbc-comparison-direct-image and the origin equivalence to obtain the first clause.
3. Apply prop-finite-compact-support-constructibility to the same finite input and
compactification, obtaining the second clause.
4. The object L is the Roos derived limit of the restricted finite-image tower in
def-weil-derived-direct-image. Apply lem-sf-integral-direct-image-constructible:
L.obj is complete, has constructible reductions, and their supports have a common
finite interval. This proves clause three for every such L.
5. Apply lem-sf-integral-compact-support-constructible to the compact-support tower
used by def-weil-integral-rational-qbar-compact-support, proving clause four.
6. By def-weil-rationalization-karoubi, raw rationalization has the same objects.
Regard the two integral outputs of steps 4 and 5 as rational objects, giving clauses
five and six with the displayed underlying-object equalities.
7. By def-weil-algebraically-closed-coefficients, retain the stage E₀ and pair it
with each rational output. This gives clauses seven and eight, including the stage
and underlying-object identifications, for every representative stage.
8. The resulting constructible objects belong to the four domains specified by
def-weil-finite-coefficient-point, so the fibre functors can be applied. No new
fibre-equivalence assertion is needed here. -/
theorem directImages_constructible
    (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (E₀ : Padic.FiniteCoefficientFields l Ω)
    (n : ℕ) (hn : 1 ≤ n)
    (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    (c : Compactification (Y ↘ Spec (CommRingCat.of D.k)))
    {Kₙ : proEtaleDerivedCategory Y
      (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)}
    (hKₙ : intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀)
      n hn Y Kₙ)
    {K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E₀) Y}
    (L : @SfIntegralDirectImage l inferInstance (Coefficient.{u} l Ω E₀)
      inferInstance inferInstance inferInstance
      Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
        let : HasCountableProducts
            (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
              (Spec (CommRingCat.of D.k)))) :=
          integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
            (Spec (CommRingCat.of D.k))
        infer_instance))
    : intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
          (Spec (CommRingCat.of D.k))
          ((proEtaleConstantDerivedDirectImage (Y ↘ Spec (CommRingCat.of D.k))
            (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)).obj Kₙ) ∧
      intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
          (Spec (CommRingCat.of D.k))
          ((@AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport Y (Spec (CommRingCat.of D.k))
            (Y ↘ Spec (CommRingCat.of D.k)) c
            (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n) _
            (Padic.finite_coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n hn)).obj Kₙ) ∧
      sfIntegralConstructible l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k))
        (@SfIntegralDirectImage.obj l inferInstance (Coefficient.{u} l Ω E₀)
          inferInstance inferInstance inferInstance
          Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
            let : HasCountableProducts
                (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
                  (Spec (CommRingCat.of D.k)))) :=
              integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
                (Spec (CommRingCat.of D.k))
            infer_instance) L) ∧
      sfIntegralConstructible l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k))
        (sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k (by
          exact finiteFieldDatumPrimeUnit D l hl) c K).obj ∧
      ∃ M : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k)),
        M.obj.obj = (@SfIntegralDirectImage.obj l inferInstance (Coefficient.{u} l Ω E₀)
          inferInstance inferInstance inferInstance
          Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
            let : HasCountableProducts
                (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
                  (Spec (CommRingCat.of D.k)))) :=
              integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
                (Spec (CommRingCat.of D.k))
            infer_instance) L) ∧
      ∃ M : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E₀) (Spec (CommRingCat.of D.k)),
        M.obj.obj = (sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
          (finiteFieldDatumPrimeUnit D l hl) c K).obj ∧
      ∃ M : generalAlgebraicallyClosedConstructibleCategory l Ω
          (Spec (CommRingCat.of D.k)),
        M.stage = E₀ ∧ HEq M.obj.obj
          (@SfIntegralDirectImage.obj l inferInstance (Coefficient.{u} l Ω E₀)
          inferInstance inferInstance inferInstance
          Y (Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) K.obj (by
            let : HasCountableProducts
                (DerivedCategory (scalarReductionSource.{u, u} l (Coefficient.{u} l Ω E₀)
                  (Spec (CommRingCat.of D.k)))) :=
              integralOperationsDerivedCountableProducts l (Coefficient.{u} l Ω E₀)
                (Spec (CommRingCat.of D.k))
            infer_instance) L) ∧
      ∃ M : generalAlgebraicallyClosedConstructibleCategory l Ω
          (Spec (CommRingCat.of D.k)),
        M.stage = E₀ ∧ HEq M.obj.obj
          ((sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
            (finiteFieldDatumPrimeUnit D l hl) c K).obj) := by
  sorry

end WeilConjectures
