/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry
public import Sheaf.Paper.KummerAdditivity
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.Paper.RingedTopoiDerivedTensorPullback
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.Paper.PurityRankOneLocalCalculation
import Sheaf.AlgebraicGeometry.GeometricPointCohomology
import Sheaf.Paper.SupportedCup
import Sheaf.Paper.SfOpenClosedTriangleAllStages
import Sheaf.Paper.PbcQbarStandardCohomology
import Sheaf.AlgebraicGeometry.ProEtaleStalkConservative
import Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.AlgebraicGeometry.TorsionSheafProperBaseChange
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.GeometricFiberFinite
import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.Paper.PurityDivisorClass
import Sheaf.Paper.SfCommonStageWeilCohomology
import Sheaf.Paper.SupportedCupFunctoriality
import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
import Sheaf.Paper.CompactProductProperSupportCompatibility

/-!
# The finite-coefficient projective-bundle formula

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
`thm-pur-projective-bundle-formula` (blueprint: thm-pur-projective-bundle-formula).

The negative shifted coefficient is the derived dual of the published ordered positive
shifted Tate power. Since the Tate sheaf is locally free of rank one, this is precisely
A(-a)[-2a], with evaluation as its canonical pairing. All arrows below are constructions:
tensor powers of the Kummer class, evaluation, and the ordinary pullback adjunction.

## Main definitions

* `projectiveBundleOrderedCup`: ordered tensor powers of one class.
* `PurityFiniteSetting.projectiveBundleSummand`: the negative shifted Tate coefficient.
* `PurityFiniteSetting.projectiveBundleComponent`: the adjunct of an evaluated cup power.
* `PurityFiniteSetting.projectiveBundleMap`: the specified finite coproduct morphism.
* `PurityFiniteSetting.projectiveBundleTargetBaseChange`: the canonical exchange map.
* `PurityFiniteSetting.projectiveBundleFormula`: invertibility and base-change compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures

/-- Tensor the same class repeatedly in a specified ordered power presentation.
The zero and successor comparisons merely identify that presentation; no power object
is chosen. Source: blueprint sk-prop-an, cup powers before adjunction
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleOrderedCup {C : Type v} [Category.{w} C]
    (T : C ⥤ C ⥤ C) (U L : C) (K : ℕ → C) (k0 : U ≅ K 0)
    (ks : ∀ a : ℕ, (T.obj (K a)).obj L ≅ K (a + 1))
    (delta : U ⟶ (T.obj U).obj U) (h : U ⟶ L) : (a : ℕ) → U ⟶ K a
  | 0 => k0.hom
  | a + 1 => delta ≫ (T.map (projectiveBundleOrderedCup T U L K k0 ks delta h a)).app U ≫
      (T.obj (K a)).map h ≫ (ks a).hom

/-- The diagonal of the coefficient unit, expressed in the same tensor coordinates
as the recorded Tate powers. Source: blueprint sk-prop-an, tensoring cup powers
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleUnitDiagonal (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Etale.ordinaryFiniteUnit A T ⟶
      ((Etale.ordinaryFiniteTensor A T).obj (Etale.ordinaryFiniteUnit A T)).obj
        (Etale.ordinaryFiniteUnit A T) :=
  (Etale.derivedTensorSingleUnitIso
    (Λ := A) (X := T) (Etale.ordinaryFiniteUnit A T)).inv

/-- Ordered cup powers in the published positive shifted Tate model, for any finite
coefficient ring. The zero power is the identity and the successor tensors with h.
Source: blueprint sk-prop-an, cup powers (blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleCupPowerRaw (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit A T ⟶
      (Etale.ordinaryFiniteLine A m
        hA T)⟦(2 : ℤ)⟧) :
    (a : ℕ) → Etale.ordinaryFiniteUnit A T ⟶ (Etale.affineLinearBaseCoefficient A m hA) T a
  := WeilConjectures.projectiveBundleOrderedCup
    (Etale.ordinaryFiniteTensor A T)
    (Etale.ordinaryFiniteUnit A T)
    ((Etale.ordinaryFiniteLine A m
      hA T)⟦(2 : ℤ)⟧)
    ((Etale.affineLinearBaseCoefficient A m hA) T) (Iso.refl _) (fun _ ↦ Iso.refl _)
    (WeilConjectures.projectiveBundleUnitDiagonal A T) h

/-- The derived dual of a positive shifted Tate power, in ordinary etale coefficients.
Source: blueprint sk-prop-an, A(-a)[-2a] (blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleSummandEtaleRaw (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) (a : ℕ) :=
  ((Etale.derivedHom (ModuleCat.{u + 1} A) T).obj
    (op ((Etale.affineLinearBaseCoefficient A m hA) T a))).obj (Etale.ordinaryFiniteUnit A T)

/-- Evaluation of a positive-power class against its derived dual, using tensor
symmetry and the tensor-Hom counit. Source: blueprint sk-prop-an, component construction
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleCupEvaluationRaw (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) (a : ℕ)
    (h : Etale.ordinaryFiniteUnit A T ⟶ (Etale.affineLinearBaseCoefficient A m hA) T a) :
    projectiveBundleSummandEtaleRaw A m hA T a ⟶ Etale.ordinaryFiniteUnit A T :=
  (Etale.derivedTensorSingleUnitIso _).inv ≫
    ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app _).app _ ≫
    Etale.derivedTensorHom (ModuleCat.{u + 1} A) h (𝟙 _) ≫
    (Etale.derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
      ((Etale.affineLinearBaseCoefficient A m hA) T a)).counit.app (Etale.ordinaryFiniteUnit A T)

/-- Pullback of ordered positive powers using the unit, tensor comparison and the
root-normalized shifted-line comparison. Source: blueprint sk-prop-an, base change
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundlePositivePullbackRaw (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A m
      hA) {T T' : Scheme.{u}} (f : T' ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) :
    (a : ℕ) → (Etale.ordinaryFinitePullback A f).obj
      ((Etale.affineLinearBaseCoefficient A m hA) T a) ≅
      (Etale.affineLinearBaseCoefficient A m hA) T' a
  | 0 => Etale.ordinaryFiniteUnitPullback A f
  | a + 1 => Etale.ordinaryFiniteTensorPullback A f
      ((Etale.affineLinearBaseCoefficient A m hA) T a)
      ((Etale.ordinaryFiniteLine A m
        hA T)⟦(2 : ℤ)⟧) ≪≫
      Etale.ordinaryFiniteTensorRightMapIso A T'
        (projectiveBundlePositivePullbackRaw A m hA t f hT a)
        (Etale.ordinaryFiniteShiftedLinePullback A m
          hA t f hT)

/-- Pullback of the negative shifted coefficient, transposed from pulled-back
evaluation and the positive-power comparison. Source: blueprint sk-prop-an, base change
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleSummandPullbackEtaleRaw (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A m
      hA) {T T' : Scheme.{u}} (f : T' ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (a : ℕ) :
    (Etale.ordinaryFinitePullback A f).obj
      (projectiveBundleSummandEtaleRaw A m hA T a) ⟶ projectiveBundleSummandEtaleRaw A m hA T' a :=
  (Etale.derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
    ((Etale.affineLinearBaseCoefficient A m hA) T' a)).homEquiv _ _
      (Etale.derivedTensorHom (ModuleCat.{u + 1} A)
          (projectiveBundlePositivePullbackRaw A m hA t f hT a).inv (𝟙 _) ≫
        (Etale.ordinaryFiniteTensorPullback A f
          ((Etale.affineLinearBaseCoefficient A m hA) T a)
          (projectiveBundleSummandEtaleRaw A m hA T a)).inv ≫
        (Etale.ordinaryFinitePullback A f).map
          ((Etale.derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
            ((Etale.affineLinearBaseCoefficient A m hA) T a)).counit.app
              (Etale.ordinaryFiniteUnit A T)) ≫
        (Etale.ordinaryFiniteUnitPullback A f).hom)
/-- The negative shifted coefficient on the pro-etale site via exact comparison.
Source: blueprint sk-prop-an, finite coefficients
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleSummandRaw (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u}) (a : ℕ) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
    (projectiveBundleSummandEtaleRaw A m hA T a)

/-- Pro-etale pullback of the negative shifted coefficient through the canonical
comparison square and the evaluation transpose. Source: blueprint sk-prop-an, base change
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleSummandPullbackRaw (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A m
      hA) {T T' : Scheme.{u}} (f : T' ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (a : ℕ) :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
      (projectiveBundleSummandRaw A m hA T a) ⟶ projectiveBundleSummandRaw A m hA T' a :=
  (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} A) f).hom.app _ ≫
    (ProEtale.kummerComparisonPullback A f).hom.app _ ≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T').mapDerivedCategory.map
      (projectiveBundleSummandPullbackEtaleRaw A m hA t f hT a)

end WeilConjectures

namespace WeilConjectures.PurityFiniteSetting

/-- The cup powers of a specified Kummer class in the recorded ordered tensor-power
presentation. Degree zero is the identity, and the successor tensors with the same class.
Source: blueprint sk-prop-an, construction before taking fibres
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleCupPower (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧) :
    (a : ℕ) → Etale.ordinaryFiniteUnit P.Coefficient T ⟶ P.diagonalTwistEtale T a :=
  WeilConjectures.projectiveBundleCupPowerRaw P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates T h

/-- A(-a)[-2a], as the derived dual of A(a)[2a]. This uses the actual recorded Tate
line, and the usual sheaf dual because that line is locally free of rank one.
Source: blueprint coefficient twists, negative-power clause, and sk-prop-an
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleSummandEtale (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (a : ℕ) :=
  WeilConjectures.projectiveBundleSummandEtaleRaw P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates T a

/-- Evaluate a cup power on its opposite shifted twist. No inverse to the projective
bundle formula is used. Source: blueprint sk-prop-an, definition of the components
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleCupEvaluation (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (a : ℕ)
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶ P.diagonalTwistEtale T a) :
    P.projectiveBundleSummandEtale T a ⟶ Etale.ordinaryFiniteUnit P.Coefficient T :=
  WeilConjectures.projectiveBundleCupEvaluationRaw P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates T a h

/-- Pullback of the positive shifted Tate powers: the unit comparison, followed
recursively by tensor pullback and the root-normalized line comparison.
Source: blueprint sk-prop-an, base-change clause; Stacks Tag 03PK
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundlePositivePullback (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T T' : Scheme.{u}} (f : T' ⟶ T)
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) :
    (a : ℕ) → (Etale.ordinaryFinitePullback P.Coefficient f).obj
      (P.diagonalTwistEtale T a) ≅ P.diagonalTwistEtale T' a :=
  WeilConjectures.projectiveBundlePositivePullbackRaw P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t f hT

/-- The canonical pullback of the negative shifted coefficient, defined by transposing
pullback of evaluation. Its positive-factor comparison is the normalized Tate map.
Source: blueprint sk-prop-an, evaluation and base change
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleSummandPullbackEtale (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T T' : Scheme.{u}} (f : T' ⟶ T)
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) (a : ℕ) :
    (Etale.ordinaryFinitePullback P.Coefficient f).obj
      (P.projectiveBundleSummandEtale T a) ⟶ P.projectiveBundleSummandEtale T' a :=
  WeilConjectures.projectiveBundleSummandPullbackEtaleRaw P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t f hT a

/-- The same negative shifted coefficient on the small pro-etale site, via the exact
comparison inverse image. Source: blueprint sk-prop-an, finite-coefficient interpretation
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleSummand (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (a : ℕ) :=
  WeilConjectures.projectiveBundleSummandRaw P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates T a

/-- Canonical inverse image of the negative shifted coefficient on the pro-etale site.
Source: blueprint sk-prop-an, base-change clause
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleSummandPullback (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T T' : Scheme.{u}} (f : T' ⟶ T)
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) (a : ℕ) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj
      (P.projectiveBundleSummand T a) ⟶ P.projectiveBundleSummand T' a :=
  WeilConjectures.projectiveBundleSummandPullbackRaw P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t f hT a

/-- The constant finite coefficient complex in comparison coordinates on the actual
small pro-etale site. Source: blueprint sk-prop-an, A_P
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleUnit (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
    (Etale.ordinaryFiniteUnit P.Coefficient T)

/-- The specified global Kummer class of the actual tautological degree-one twist.
Source: blueprint sk-prop-an, h_F=c_1(O(1))
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleChern (P : PurityFiniteSetting.{u}) {B : Scheme.{u}}
    {F : B.Modules} (b : B ⟶ Spec (.of P.field.k))
    (D : ProjectiveBundleRealization B F) (hL : D.L.IsInvertible) :=
  letI := hL
  Etale.kummerFirstChern P.Coefficient P.diagonalExponent P.diagonalExponent_annihilates
    D.A.data.relProj (P.diagonalExponent_isUnit (D.A.data.relProjHom ≫ b))
      (Scheme.Pic.ofIsInvertible D.L)

/-- The component adjoint to h_F^a after evaluating opposite twists. Exact comparison
inverse image gives the specified pro-etale Chern class of lem-pur-kummer-additivity.
Source: blueprint sk-prop-an, construction of Phi_F
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleComponent (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {B : Scheme.{u}} {F : B.Modules}
    (b : B ⟶ Spec (.of P.field.k)) (D : ProjectiveBundleRealization B F)
    (hL : D.L.IsInvertible) (a : ℕ) :
    P.projectiveBundleSummand B a ⟶
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        D.A.data.relProjHom).rightDerivedFunctor.obj (P.projectiveBundleUnit D.A.data.relProj) :=
  (ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} P.Coefficient) D.A.data.relProjHom).homEquiv _ _
      (P.projectiveBundleSummandPullback t D.A.data.relProjHom
          (P.diagonalExponent_isUnit b) a ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
          D.A.data.relProj).mapDerivedCategory.map
            (P.projectiveBundleCupEvaluation D.A.data.relProj a
              (P.projectiveBundleCupPower D.A.data.relProj (P.projectiveBundleChern b D hL) a)))

/-- The displayed finite direct-sum morphism (1,h_F,...,h_F^n). The summand injections
are the actual coproduct injections, and its components are the specified adjuncts.
Source: blueprint sk-prop-an, displayed projective-bundle morphism
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleMap (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) (n : ℕ) {B : Scheme.{u}} {F : B.Modules}
    (b : B ⟶ Spec (.of P.field.k)) (D : ProjectiveBundleRealization B F)
    (hL : D.L.IsInvertible) :
    (∐ fun a : Fin (n + 1) ↦ P.projectiveBundleSummand B a.val) ⟶
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        D.A.data.relProjHom).rightDerivedFunctor.obj (P.projectiveBundleUnit D.A.data.relProj) :=
  Sigma.desc (fun a : Fin (n + 1) ↦ P.projectiveBundleComponent t b D hL a.val)

/-- Constant-coefficient pullback, using the canonical site-comparison square and the
ordinary unit comparison. Source: blueprint sk-prop-an, proper base-change target
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleUnitPullback (P : PurityFiniteSetting.{u})
    {T T' : Scheme.{u}} (f : T' ⟶ T) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj
      (P.projectiveBundleUnit T) ≅ P.projectiveBundleUnit T' :=
  (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} P.Coefficient) f).app _ ≪≫
    ProEtale.kummerCoefficientPullback P.Coefficient f _ _
      (Etale.ordinaryFiniteUnitPullback P.Coefficient f)

/-- Proper base change followed by the canonical constant-coefficient identification.
The exchange is the mate of the inverse-image square, with no arbitrary target isomorphism.
Source: blueprint sk-prop-an, base-change clause
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleTargetBaseChange (P : PurityFiniteSetting.{u})
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    {D : ProjectiveBundleRealization B F} {D' : ProjectiveBundleRealization B' F'}
    {g : B' ⟶ B} {e : F' ≅ (Scheme.Modules.tensorPullback g).obj F}
    (c : ProjectiveBundleBaseChangeDatum D D' g e) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          D.A.data.relProjHom).rightDerivedFunctor.obj
            (P.projectiveBundleUnit D.A.data.relProj)) ⟶
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        D'.A.data.relProjHom).rightDerivedFunctor.obj
          (P.projectiveBundleUnit D'.A.data.relProj) :=
  (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
    (⟨c.over⟩ : CommSq c.map D'.A.data.relProjHom D.A.data.relProjHom g)).app _ ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      D'.A.data.relProjHom).rightDerivedFunctor.map
        (P.projectiveBundleUnitPullback c.map).hom

/-- The finite-coefficient projective-bundle formula, including equality of its specified
components after every base change. The positive tensor powers are the published Tate
powers; their derived duals are A(-a)[-2a]. The component equalities determine equality of
the direct-sum maps because inverse image preserves finite coproducts. The normalized
geometry system represents Proj(Sym F) and its tautological line for every base.

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
thm-pur-projective-bundle-formula (blueprint: thm-pur-projective-bundle-formula).

Proof:
1. Use lem-pur-projective-bundle-tautological-geometry for properness, the actual O(1),
   and its pullback identifications. Form the global Kummer class using
   lem-pur-kummer-additivity. Tensor its powers and evaluate opposite twists, which are
   invertible by lem-pur-twist-sheaf-locally-free. Transpose under the ordinary adjunction
   of def-weil-pbc-proetale-operations and take the finite coproduct.
2. Work on the ordinary etale site. The counit equality of
   lem-weil-pbc-comparison-direct-image-canonical-mate identifies the same adjuncts after
   exact comparison pullback. Use lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
   lem-weil-pbc-comparison-pullback and lem-asd-etale-finite-twist-pullback for tensor,
   evaluation and pullback. Full faithfulness of thm-weil-pbc-site-comparison reflects
   isomorphisms. The supported and compact comparisons are those of
   lem-pur-compact-product-proper-support-compatibility.
3. Over k, thm-pur-rank-one-thom gives RΓ_c(A¹,A)=A(-1)[-2]. The zero-section class is
   the coordinate Kummer boundary by lem-pur-divisor-class, with residue one by
   thm-pur-rank-one-local-calculation. Use lem-weil-pbc-geometric-point-cohomology for
   the point. Iterate the compact product comparison: RΓ_c(A^n,A)=A(-n)[-2n].
   The cup clause, def-pur-supported-cup, def-pur-supported-exterior-product and
   lem-pur-supported-cup-functoriality identify the coordinate product with the compact
   generator via the proper point support. Every degree is even.
4. On P^n use the n coordinate hyperplanes through the affine origin. Their localized
   divisor classes forget to h. Their supported product restricts to the coordinate
   product by lem-pur-divisor-class and supported cup functoriality. Excision and the
   proper-support comparison identify its ordinary image with h^n, the top generator.
5. Apply prop-sf-open-closed-triangle-all-stages to A^n in P^n and push forward properly.
   By def-compact-support-direct-image-detailed its first term is RΓ_c(A^n,A).
   The long exact sequence of lem-sf-derived-homology-long-exact and induction on n
   identify the lower even groups with those on P^(n-1), and the top group with the
   compact generator. Kummer naturality gives the lower generators. All other groups
   vanish, so the map is an isomorphism; n=0 is the identity. Use the cohomology of
   def-weil-derived-cohomology-sheaves and lem-cbc-proetale-stalk-conservative, clause 3.
6. For any algebraically closed extension Ω/k, pullback of frames is the pulled-back
   frame torsor by lem-sc-etale-torsor-h1-functoriality. Apply lem-amb-kummer-any-base
   and lem-weil-pbc-site-cohomology-pullback to the Kummer boundary, then insert the
   coefficient one. This proves Chern naturality without finite type on Ω. Proper
   base change prop-weil-proet-finite-proper-base-change and the A-linear exchange of
   lem-weil-pbc-exchange-forget-coefficients transport the field calculation to Ω.
7. For B, cor-weil-pbc-geometric-fiber-finite identifies the target stalk with the
   cohomology of P^n_Ω. The tautological geometry and step 6 identify the stalk map
   with the preceding isomorphism. Clause 3 of lem-cbc-proetale-stalk-conservative
   detects this etale-origin map. No detector for arbitrary pro-etale sheaves is used.
8. For g:B'→B, the normalized tautological theta identifies the pulled-back O(1).
   Kummer naturality and finite twist pullback identify each pulled adjunct with h'^a,
   including a=0. The exchange of lem-weil-pbc-exchange-forget-coefficients is the
   transpose of the pulled counit, hence the component maps are equal. Proper base
   change makes exchange invertible. The comparison pullback and direct-image counit
   equality transport the same equation to pro-etale coefficients. No higher-rank or
   higher-codimension purity is used.
-/
theorem projectiveBundleFormula (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) (n : ℕ) (G : ProjectiveBundleTautologicalSystem.{u} n)
    (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F)
    (b : B ⟶ Spec (.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b] :
    IsIso (P.projectiveBundleMap t n b (G.bundle B F hF) (G.invertible B F hF)) ∧
    ∀ (B' : Scheme.{u}) (b' : B' ⟶ Spec (.of P.field.k))
      (_hs : IsSeparated b') (_hft : LocallyOfFiniteType b') (_hqc : QuasiCompact b')
      (g : B' ⟶ B) (_hg : g ≫ b = b') (F' : B'.Modules)
      (hF' : projectiveBundleRank B' n F') (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F),
      IsIso (P.projectiveBundleTargetBaseChange (G.baseChange hF hF' g e)) ∧
      ∀ a : Fin (n + 1),
        IsIso (P.projectiveBundleSummandPullback t g (P.diagonalExponent_isUnit b) a.val) ∧
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) g).leftDerivedFunctor.map
            (P.projectiveBundleComponent t b (G.bundle B F hF) (G.invertible B F hF) a.val) ≫
          P.projectiveBundleTargetBaseChange (G.baseChange hF hF' g e) =
        P.projectiveBundleSummandPullback t g (P.diagonalExponent_isUnit b) a.val ≫
          P.projectiveBundleComponent t b' (G.bundle B' F' hF') (G.invertible B' F' hF') a.val := by
  sorry

end WeilConjectures.PurityFiniteSetting
