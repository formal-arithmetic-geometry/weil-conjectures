/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.IntegralCoefficientPresentationComparison
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-! # The actual comparison counit at the finite coefficient point

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
lem-pod-point-dualizing-complex.proof.md, opening sentence; Stacks Tags 099V and 00YV
(blueprint: lem-coef-finite-point-counit-unit-normalization).

Fixed-scalar module sheaves are the existing presentation of modules over the constant
ring sheaf. The constant comparison below uses the actual Kan-extension adjunction.
Positive exponent n+1 ranges over exactly the levels n >= 1 in the node.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FinitePointCounit

/-- The regular constant etale module in degree zero.
Source: blueprint opening sentence (blueprint: lem-coef-finite-point-counit-unit-normalization).
-/
abbrev etaleConstant (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))

/-- The regular constant pro-etale module in degree zero.
Source: blueprint opening sentence (blueprint: lem-coef-finite-point-counit-unit-normalization).
-/
abbrev proEtaleConstant (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).obj
    ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))

/-- The constant-ring comparison, fixed by the constant-sheaf adjunctions and comparison
adjunction, then passed to degree-zero complexes. Thus constants retain their scalars.
Source: Stacks 00YV (blueprint: lem-coef-finite-point-counit-unit-normalization). -/
def constantComparison (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
      (etaleConstant X A) ≅ proEtaleConstant X A :=
  ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategorySingleFunctor
    0).app ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ≪≫
  (DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    0).mapIso
      (((((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).comp
          (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X)).ofNatIsoRight
            ((Scheme.toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso
            (ModuleCat.{u + 1} A) X.smallEtaleTopology (Scheme.ProEt.topology X)
            (Opposite.op (⊤_ X.Etale)))).leftAdjointUniq
              (constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
                (terminalIsTerminal.isTerminalObj (Scheme.toProEt X) (⊤_ X.Etale)))).app
                  (ModuleCat.of A A))

/-- Ordinary etale compact support for the identity compactification is canonically
isomorphic to the identity, using exact open extension and the derived identity image.
Source: blueprint opening sentence (blueprint: lem-coef-finite-point-counit-unit-normalization).
-/
def compactSupportIdentity (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A] :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (Compactification.ofIsProper (𝟙 X)) ≅ 𝟭 _ :=
  Functor.isoWhiskerRight
    (Etale.mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) X) _ ≪≫
    Functor.leftUnitor _ ≪≫ Etale.rightDerivedLowerStarIdIso A X

/-- The stipulated identity right adjoint of identity compact support, with its transported
adjunction. Source: blueprint opening sentence
(blueprint: lem-coef-finite-point-counit-unit-normalization). -/
def identityRightAdjunction (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A] :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (Compactification.ofIsProper (𝟙 X)) ⊣ 𝟭 _ :=
  Adjunction.id.ofNatIsoLeft (compactSupportIdentity X A).symm

/-- The finite exceptional object with the stipulated identity right adjoint substituted
in the recorded formula nu^* f^times R nu_*. This is nu^* R nu_* B on the nose.
Source: blueprint opening sentence, finite exceptional construction
(blueprint: lem-coef-finite-point-counit-unit-normalization). -/
abbrev omega (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
    ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) X).rightDerivedFunctor.obj
      (proEtaleConstant X A))

/-- The recorded finite exceptional functor has precisely the stipulated presentation:
uniqueness of the ordinary etale right adjoint compares its chosen representative with
identityRightAdjunction, before applying the two comparison functors.
Source: finite exceptional construction
(blueprint: lem-coef-finite-point-counit-unit-normalization).
-/
def chosenPresentation (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    [(Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (Compactification.ofIsProper (𝟙 X))).IsLeftAdjoint] :
    (ProEtale.sfFiniteExceptionalAt A (Compactification.ofIsProper (𝟙 X))).obj
      (proEtaleConstant X A) ≅ omega X A :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.mapIso
    (((Adjunction.ofIsLeftAdjoint
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper (𝟙 X)))).rightAdjointUniq
          (identityRightAdjunction X A)).app
            ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) X).rightDerivedFunctor.obj
              (proEtaleConstant X A)))

/-- The normalization is the actual derived comparison counit at B.
Source: Stacks 099V (blueprint: lem-coef-finite-point-counit-unit-normalization). -/
def alpha (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    omega X A ⟶ proEtaleConstant X A :=
  (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).counit.app
    (proEtaleConstant X A)

/-- The asserted inverse is nu^*(eta_G), with the two endpoints transported by the
specified constant comparison. No arbitrary isomorphism or scalar rescaling occurs.
Source: Stacks 099V (blueprint: lem-coef-finite-point-counit-unit-normalization). -/
def beta (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    proEtaleConstant X A ⟶ omega X A :=
  (constantComparison X A).inv ≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app
        (etaleConstant X A)) ≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) X).rightDerivedFunctor.map
        (constantComparison X A).hom)

/-- At the geometric finite-field point the coefficient ring is finite and the actual
comparison counit is invertible, with inverse the pulled-back comparison unit.
Source: blueprint lem-pod-point-dualizing-complex.proof.md, opening sentence;
Stacks Tags 099V and 00YV (blueprint: lem-coef-finite-point-counit-unit-normalization).

Proof:
1. The extension absolute value is nonarchimedean; extension_integers_dvr makes its
valuation ring a DVR with finite residue field. The uniformizer generates the maximal
ideal. The valued-DVR finite-quotient lemma gives finiteness of A at every positive level.
2. The constant-left-module inverse-image comparison identifies nu^*G with B preserving
constant scalars. Exactness passes this comparison to degree-zero derived objects;
constantComparison writes this canonical comparison in the fixed-scalar presentation.
3. Identity compact support is naturally isomorphic to identity, via extension by zero
and the image of an injective resolution. Transport its adjunction with identity.
Substitute this right adjoint in the finite exceptional formula, obtaining omega.
chosenPresentation compares the recorded chosen adjoint with this stipulated one.
4. The integral-coefficient presentation comparison identifies the function-sheaf and
constant-ring encodings, including their exact module equivalence and adjunctions.
The finite site-comparison theorem makes eta_G invertible, since G is in degree zero.
Its pullback beta is therefore invertible. The left triangle identity, transported
through constantComparison and naturality of the counit, gives beta followed by alpha
as identity on B. Hence alpha is beta's inverse and the other composite is identity
on omega as well. This proves the required actual-counit normalization. -/
theorem finite_point_counit_unit_normalization (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) ∧
    IsIso (alpha (Spec (.of D.k)) (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) ∧
    beta (Spec (.of D.k)) (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) ≫
      alpha (Spec (.of D.k)) (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) =
        𝟙 _ ∧
    alpha (Spec (.of D.k)) (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) ≫
      beta (Spec (.of D.k)) (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) =
        𝟙 _ := by
  sorry

end WeilConjectures.FinitePointCounit
