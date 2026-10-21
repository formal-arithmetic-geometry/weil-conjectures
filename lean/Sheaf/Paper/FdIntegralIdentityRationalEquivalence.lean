/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.FdCoefficientComparison
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.IntegralCoefficientPresentationComparison
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.Paper.SfIntegralConstructibleLinear
import Sheaf.Paper.PbcUniformCompleteTriangulated
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
import Sheaf.CategoryTheory.ScalarLocalization
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The integral identity and its raw rationalization

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence; Bhatt--Scholze, Section 6.5,
Definition 6.5.1 and Proposition 6.8.11(3); Stacks Tag 05R6
(blueprint: lem-fd-integral-identity-rational-equivalence).

The comparison uses the existing finite-stage datum, strengthened explicitly by
integral linearity, exactness, inverse formulas and normalized finite reductions.
The fields of `FdRationalStageComparison` retain its forward object, tensor and shift pins.
The coefficient field's canonical small model permits an algebraic closure in any universe.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe d u w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The common integral identity induces inverse exact linear equivalences on the
integral categories and their raw rationalizations, with the prescribed finite reductions.
Source: trace-definition final sentence, auxiliary subclaim from comparison proof steps 1--2;
Bhatt--Scholze, Section 6.5, Definition 6.5.1 and Proposition 6.8.11(3); Stacks Tag 05R6
(blueprint: lem-fd-integral-identity-rational-equivalence).

Proof (the four steps of the DAG node):
1. Apply lem-weil-pbc-integral-coefficient-presentation-comparison. Its unique quotient
isomorphisms send [x] to [x.down].up. Their inverse-limit isomorphism is fixed by every
finite projection. Scalar restriction along it and its inverse are exact inverse functors,
with their normalized finite reductions and transitions. By
lem-weil-pbc-integral-stratified-perfect-characterization, these restrictions preserve and
reflect precisely the two integral predicates, including compatible etale-origin witnesses.
Restrict the ambient functors to the full subcategories. In their common realization both
are identity on objects and arrows.
2. By lem-weil-integral-constructible-triangulated and
lem-weil-pbc-uniform-complete-triangulated, shifts and triangles are inherited.
lem-weil-pbc-exact-functor-derived-factorization supplies the shift comparisons induced
by the degreewise identity: coefficient restriction does not change differentials,
shift signs or the cone matrix. Consequently the two restrictions preserve triangles.
lem-weil-integral-constructible-linear identifies the Hom action with constant sections;
the coefficient projection equations fix every constant scalar, proving linearity in
both directions.
3. Use def-weil-rationalization-karoubi, def-weil-pbc-rational-category and
def-weil-linear-scalar-localization. Send K to I(K) and f tensor a to I(f) tensor a.
Integral linearity gives balancedness; additivity extends the map from pure tensors.
On pure tensors the identity and composition equations are the integral functor equations
and multiplication of scalars. The inverse restriction gives the same construction in
reverse. Both composites fix integral objects and pure tensors, hence all morphisms.
Thus these are equivalences with the displayed inverse formulas and field linearity.
The raw categories have exactly the original integral objects: no retract is adjoined.
4. By lem-weil-linear-scalar-localization-triangulated, a distinguished rational triangle
is isomorphic to the localization of an integral distinguished triangle. The localized
identity-induced shift comparison intertwines the two localization functors. Step 2
therefore makes its image distinguished; use the same argument for the inverse.
This proves rational exactness with precisely the shift pins in the comparison datum. -/
theorem fdIntegralIdentityRationalEquivalence
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (E : Padic.FiniteCoefficientFields l Ω) :
    ∃ c : FdRationalStageComparison l Ω T E,
    ∃ si : c.integral.inverse.CommShift ℤ,
    (fun [_si : c.integral.inverse.CommShift ℤ] ↦
      c.integral.functor.Additive ∧ c.integral.inverse.Additive ∧
      c.integral.functor.IsTriangulated ∧
      c.integral.inverse.IsTriangulated ∧
      (∀ (K H : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
        (a : Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E)) (f : K ⟶ H),
        c.integral.functor.map (a • f) = ULift.up a • c.integral.functor.map f) ∧
      (∀ (K H : pbcIntegralStage l Ω T E)
        (a : PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) (f : K ⟶ H),
        c.integral.inverse.map (a • f) = a.down • c.integral.inverse.map f) ∧
      (∀ K : pbcStageCategory l Ω T E,
        c.rational.inverse.obj K = ⟨c.integral.inverse.obj K.obj⟩) ∧
      (∀ (K H : pbcIntegralStage l Ω T E)
        (a : Localization.Away (pbcStageUniformizer.{u} l Ω E)) (f : K ⟶ H),
        HEq (c.rational.inverse.map (fdRawTensor (pbcStageUniformizer.{u} l Ω E) a f))
          (fdRawTensor
            (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E))
            ((sfRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E)).symm
              (pbcRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E) a))
            (c.integral.inverse.map f))) ∧
      (∀ (K H : sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
        (a : Localization.Away
          (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E))) (f : K ⟶ H),
        c.rational.functor.map
            (fdRawScale (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E))
              a f) =
          fdRawScale (pbcStageUniformizer.{u} l Ω E)
            ((pbcRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E)).symm
              (sfRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E) a))
            (c.rational.functor.map f)) ∧
      (∀ (K H : pbcStageCategory l Ω T E)
        (a : Localization.Away (pbcStageUniformizer.{u} l Ω E)) (f : K ⟶ H),
        c.rational.inverse.map (fdRawScale (pbcStageUniformizer.{u} l Ω E) a f) =
          fdRawScale
            (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E))
            ((sfRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E)).symm
              (pbcRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E) a))
            (c.rational.inverse.map f)) ∧
      (fun [_s : c.rational.inverse.CommShift ℤ] ↦
        ∀ (n : ℤ) (K : pbcIntegralStage l Ω T E),
          HEq (c.rational.inverse.map
              (((pbcStageLocalization l Ω T E).commShiftIso n).hom.app K) ≫
            (c.rational.inverse.commShiftIso n).hom.app
              ((pbcStageLocalization l Ω T E).obj K))
            ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).map
                ((c.integral.inverse.commShiftIso n).hom.app K) ≫
              ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).commShiftIso
                n).hom.app (c.integral.inverse.obj K)))
        (_s := c.inverse_exact) ∧
      ∃ e : pbcAdicCompletion T (pbcStageDatum.{u} l Ω E) ≅
          completedIntegralCommRingSheafUnrestricted l (pbcFiniteField.{u} l Ω E) T,
        (adicLisseForget T).mapIso e =
          integralDetailedCoefficientComparison T l (pbcFiniteField.{u} l Ω E) ∧
        c.integral.inverse ⋙ (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι =
          pbcStageInclusion l Ω T E ⋙ pbcDerivedRestrict e.inv ∧
        (∀ (n : ℤ) (K : pbcIntegralStage l Ω T E),
          HEq ((sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι.map
                ((c.integral.inverse.commShiftIso n).hom.app K) ≫
              ((sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι.commShiftIso
                n).hom.app (c.integral.inverse.obj K))
            ((pbcDerivedRestrict e.inv).map
                (((pbcStageInclusion l Ω T E).commShiftIso n).hom.app K) ≫
              (((pbcRestrict e.inv).mapDerivedCategory).commShiftIso n).hom.app K.obj)) ∧
        ∃ r : ∀ n : ℕ,
            pbcRestrict (IntegralCoefficientPresentation.level l (pbcFiniteField.{u} l Ω E) T
                (integralCoefficientULift l (pbcFiniteField.{u} l Ω E)) n).hom ⋙
              pbcRestrict (pbcAdicProjection T (pbcStageDatum.{u} l Ω E) n) ≅
            pbcRestrict (completedIntegralCommRingProjectionUnrestricted l
                (pbcFiniteField.{u} l Ω E) T n) ⋙ pbcRestrict e.hom,
          (∀ (n : ℕ)
            (M : pbcModules T
              (integralCoefficientCommRingSheaf l (pbcFiniteField.{u} l Ω E) T n))
            (U : T.ProEtᵒᵖ) (x : M.val.obj U), ((r n).hom.app M).val.app U x = x) ∧
          ∃ α : ∀ n : ℕ, pbcDerivedRestrict e.hom ⋙
                pbcDerivedExtend (pbcAdicProjection T (pbcStageDatum.{u} l Ω E) n) ≅
              pbcDerivedExtend (completedIntegralCommRingProjectionUnrestricted l
                (pbcFiniteField.{u} l Ω E) T n) ⋙
                pbcDerivedRestrict
                  (IntegralCoefficientPresentation.level l (pbcFiniteField.{u} l Ω E) T
                    (integralCoefficientULift l (pbcFiniteField.{u} l Ω E)) n).hom,
            ∀ (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) (n : ℕ),
              (pbcDerivedScalarAdjunction
                  (pbcAdicProjection T (pbcStageDatum.{u} l Ω E) n)).unit.app
                    ((pbcDerivedRestrict e.hom).obj K.obj) ≫
                (IntegralCoefficientPresentation.restrictedComparison e
                  (IntegralCoefficientPresentation.level l (pbcFiniteField.{u} l Ω E) T
                    (integralCoefficientULift l (pbcFiniteField.{u} l Ω E)) n)
                  (pbcAdicProjection T (pbcStageDatum.{u} l Ω E) n)
                  (completedIntegralCommRingProjectionUnrestricted l
                    (pbcFiniteField.{u} l Ω E) T n) (r n) (α n) K.obj).hom =
                (pbcDerivedRestrict e.hom).map
                  ((pbcDerivedScalarAdjunction
                    (completedIntegralCommRingProjectionUnrestricted l
                      (pbcFiniteField.{u} l Ω E) T n)).unit.app K.obj)) (_si := si) := by
  sorry

end WeilConjectures
