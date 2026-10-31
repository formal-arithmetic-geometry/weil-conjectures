/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FixedFinitePositiveCoefficientTwist
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceLinearTraceInvariance
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorMateEtalePrecomp
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Data for the canonical smooth dualizing-object comparison

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-prop-sp-orientation/thm-pur-diagonal-dualizing-object.md
(blueprint: thm-pur-diagonal-dualizing-object).
Data extraction: (blueprint: def-pur-diagonal-dualizing-data).

The comparison lives on the small pro-etale site, at the fixed positive coefficient
level. Its normalization is specified on every etale coordinate chart by the actual
ordered affine-space counit, whose rank-one factor is the Kummer-normalized trace.
The ordinary-etale objects below are presentations under nu*, with an explicit
comparison-unit equation. The final comparison is selected from a unique normalized
isomorphism, rather than from bare existence of an isomorphism.

## Main declarations

- `DiagonalOrientationNormalization`: the coordinate counit normalization.
- `DiagonalDualizingConclusion`: the full-domain pro-etale assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The ordinary-etale presentation of the relative dualizing object, applied to
A_Y in degree zero. Source: blueprint exceptional inverse image, finite stage
(blueprint: thm-pur-diagonal-dualizing-object). -/
def diagonalOrdinaryDualizing (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :=
  (Etale.rightDerivedUpperShriek P.Coefficient f).obj
    (Etale.ordinaryFiniteUnit P.Coefficient Y)

/-- The finite transported exceptional inverse image of the coefficient unit.
This uses the recorded sfFiniteExceptionalAt at its specified compactification;
it is an object of D(X_proet,A), not of D(X_et,A).
Source: blueprint def-weil-exceptional-inverse-image, displayed finite definition
(blueprint: thm-pur-diagonal-dualizing-object). -/
def diagonalDualizing (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriek P.Coefficient f
  letI : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient)
      (HasCompactification.compactification f)).IsLeftAdjoint :=
    inferInstanceAs (Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} P.Coefficient) f).IsLeftAdjoint
  (ProEtale.sfFiniteExceptionalAt P.Coefficient
    (HasCompactification.compactification f)).obj
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit P.Coefficient Y))

/-- The actual degree-zero coefficient object is bounded below.
Source: blueprint coefficient unit, A_Y[0]
(blueprint: thm-pur-diagonal-dualizing-object).
Proof: the single complex has cohomology A in degree zero and zero in every other
degree, so zero is a lower bound in the standard t-structure. -/
theorem diagonalUnitPlus (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    _root_.DerivedCategory.TStructure.t.plus (Etale.ordinaryFiniteUnit P.Coefficient Y) := by
  exact ⟨0, inferInstance⟩

/-- The canonical identification with nu_X* f^times A_Y, by the inverse of the
comparison adjunction unit at the bounded-below coefficient object.
Source: blueprint exceptional inverse image and finite comparison
(blueprint: thm-pur-diagonal-dualizing-object). -/
def diagonalDualizingComparison (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    P.diagonalDualizing f ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
          (P.diagonalOrdinaryDualizing f) :=
  letI := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} P.Coefficient) Y
      (Etale.ordinaryFiniteUnit P.Coefficient Y) (P.diagonalUnitPlus Y)
  letI : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient)
      (HasCompactification.compactification f)).IsLeftAdjoint :=
    inferInstanceAs (Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} P.Coefficient) f).IsLeftAdjoint
  (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
      (((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient)
          (HasCompactification.compactification f))).rightAdjointUniq
        (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f)).app _ ≪≫
      (Etale.rightDerivedUpperShriek P.Coefficient f).mapIso
        (asIso ((ProEtale.derivedComparisonAdjunction
          (ModuleCat.{u + 1} P.Coefficient) Y).unit.app
            (Etale.ordinaryFiniteUnit P.Coefficient Y))).symm)

/-- Canonical source-etale locality, with the specified sum-extension counit.
The normalized compact-support comparison N fixes the mate completely.
Source: blueprint etale locality of the exceptional adjoint
(blueprint: thm-pur-diagonal-dualizing-object). -/
def diagonalEtaleLocality (P : PurityFiniteSetting.{u})
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {U X Y : Scheme.{u}} (j : U ⟶ X) (f : X ⟶ Y)
    [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian Y]
    [HasCompactification f] [HasCompactification (j ≫ f)] :
    (Etale.ordinaryFinitePullback P.Coefficient j).obj (P.diagonalOrdinaryDualizing f) ≅
      P.diagonalOrdinaryDualizing (j ≫ f) :=
  (Etale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} P.Coefficient) j).app _ ≪≫
    (Etale.tensorMateEtalePrecompLocalityIso P.Coefficient N j f).app
      (Etale.ordinaryFiniteUnit P.Coefficient Y)

/-- The actual affine-space trace, transposed under the ordinary exceptional
adjunction. It is a map from the ordered shifted-root-line coefficient object;
no arbitrary affine-space orientation is an input.
Source: blueprint affine-space trace and its normalized counit
(blueprint: thm-pur-diagonal-dualizing-object). -/
def diagonalAffineMate (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (P.diagonalExponent : Γ(Y, ⊤))) (d : ℕ) :
    P.diagonalTwistEtale (affineTraceTower Y d) d ⟶
      P.diagonalOrdinaryDualizing (affineTraceProjection Y d) :=
  letI := affineTraceNoetherian Y d
  let hN := pow_pos P.coefficients.prime.out.pos P.level
  ((Etale.affineLinearCoefficientDescent P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t Y hY d) ≪≫
    Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t (affineTraceProjection Y d) hY d).inv ≫
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient
      (affineTraceProjection Y d)).homEquiv _ _
        ((Etale.affineLinearCompactComparison P.diagonalExponent hN P.Coefficient
          P.diagonalExponent_annihilates Y hY d).inv ≫
          Etale.affineTraceCounit P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t D Y hY d)

/-- Changing only the displayed composite uses the equality-induced isomorphism.
The compactification witnesses are propositions, hence proof irrelevant.
Source: blueprint canonical functor comparisons
(blueprint: thm-pur-diagonal-dualizing-object). -/
def diagonalDualizingCongr (P : PurityFiniteSetting.{u})
    {U Y : Scheme.{u}} {f g : U ⟶ Y} [HasCompactification f] [HasCompactification g]
    (w : f = g) : P.diagonalOrdinaryDualizing f ≅ P.diagonalOrdinaryDualizing g :=
  eqToIso (by cases w; rfl)

/-- The coordinate normalization of the inverse orientation. It compares the two
source-etale locality maps on every chart U -> X, U -> A^d_Y over Y. The affine
map is the actual Kummer-normalized counit mate. All normalized coefficient and
compact-support presentations are universally quantified, so none is an extra
hypothesis or an independent choice of orientation.
Source: blueprint canonical diagonal/DNC/vector-bundle orientation
(blueprint: thm-pur-diagonal-dualizing-object). -/
def DiagonalOrientationNormalization (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y) [HasCompactification f]
    [IsNoetherian X] [IsNoetherian Y]
    (aY : Y ⟶ Spec (.of P.field.k))
    (e : P.diagonalOrdinaryDualizing f ≅ P.diagonalTwistEtale X d) : Prop :=
  letI := affineTraceNoetherian Y d
  ∀ (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (U : Scheme.{u}) [IsNoetherian U]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (v : U ⟶ affineTraceTower Y d) [Etale v] [IsSeparated v]
    [LocallyOfFiniteType v] [QuasiCompact v]
    (w : v ≫ affineTraceProjection Y d = j ≫ f)
    [HasCompactification (j ≫ f)] [HasCompactification (v ≫ affineTraceProjection Y d)],
    (Etale.ordinaryFinitePullback P.Coefficient j).map e.inv ≫
        (P.diagonalEtaleLocality N j f).hom =
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) d).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t v
          (affineTraceInvertible P.diagonalExponent Y (P.diagonalExponent_isUnit aY) d)
            d).inv ≫
      (Etale.ordinaryFinitePullback P.Coefficient v).map
        (P.diagonalAffineMate t D Y (P.diagonalExponent_isUnit aY) d) ≫
      (P.diagonalEtaleLocality N v (affineTraceProjection Y d)).hom ≫
      (P.diagonalDualizingCongr w).hom

/-- The full-domain canonical pro-etale comparison. No absolute separatedness is
assumed. Noetherianity, quasi-compactness and compactifiability are consequences
of the finite-type field domain. The comparison equation explicitly identifies
the pro-etale arrow with its normalized ordinary presentation.
Source: blueprint smooth purity and its finite exceptional-inverse-image domain
(blueprint: thm-pur-diagonal-dualizing-object). -/
def DiagonalDualizingConclusion (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] : Prop :=
  letI := isNoetherian_of_locallyOfFiniteType aY
  letI := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  letI : HasCompactification f := inferInstance
  ∃! θ : P.diagonalDualizing f ≅ P.diagonalTwist X d,
    ∃ e : P.diagonalOrdinaryDualizing f ≅ P.diagonalTwistEtale X d,
      P.DiagonalOrientationNormalization d f aY e ∧
      θ = P.diagonalDualizingComparison f ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso e

end WeilConjectures.PurityFiniteSetting
