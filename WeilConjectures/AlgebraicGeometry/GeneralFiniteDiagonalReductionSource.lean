/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GeneralFiniteDiagonalReductionSide

/-! # Canonical components of finite smooth-purity scalar reduction

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-setup/sec-the-purity-statement/
sk-thm-purity-transport/sk-thm-purity-transport.proof.md, Step 1
(blueprint: def-pur-general-source-comparison).

The Kummer root power fixes the Tate-line map independently of the orientations.
The source comparison composes the derived scalar/comparison isomorphism with
pullback, tensor, Kummer and shift comparisons. Its components are consumed on
constructible objects; unrestricted naturality on the pro-category is not asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

local instance proEtaleEssentiallySmallSource (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _

/-- The coefficient-root power map for a divisibility transition.
Source: `WeilConjectures/EtaleCohomology/TateTwist/KummerLevelIndependence.lean`;
(blueprint: def-pur-general-source-comparison). -/
noncomputable def kummerRootPower
    {X : Scheme.{u}} (N M : ℕ) (hMN : M ∣ N) :
    X.rootsOfUnitySheaf N ⟶ X.rootsOfUnitySheaf M :=
  Scheme.rootsOfUnityPow (X := X) M (N / M) N
    (Nat.mul_div_cancel' hMN).symm

/-- Data fixing the Kummer reduction independently of the orientation isomorphisms.
Source: `sk-lem-sp-reduction`, coefficient-line compatibility (3);
(blueprint: def-pur-general-source-comparison).

The coefficient-line comparison supplies the generator-normalized scalar map and all
ordered tensor powers; the extra equation identifies its root arrow with the literal
Kummer power map `z ↦ z ^ (N / M)`. -/
structure KummerTateLineReductionData
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X : Scheme.{u}} (φ : A →+* B) (N M d : ℕ)
    (hMN : M ∣ N) (hA : (N : A) = 0) (hB : (M : B) = 0) where
  comparison : Etale.FiniteSmoothPurity.CoefficientLineComparison φ N M hA hB X
  rootMap_spec : comparison.roots = kummerRootPower N M hMN

/-- The canonical compact-support reduction induced by the live derived scalar extension.
Source: `sk-lem-sp-reduction`, equation (10.15), transported through the finite
coefficient framework; (blueprint: def-pur-general-source-comparison). -/
noncomputable def canonicalCompactReduction
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (φ : A →+* B)
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ X)]
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ Y)]
    (K : Etale.FiniteSmoothPurity.proCategory A Y) :
    (sideScalar φ Y).obj ((Etale.FiniteSmoothPurity.proCompact A f).obj
      ((Etale.FiniteSmoothPurity.exceptional A f).obj K)) ⟶
    (Etale.FiniteSmoothPurity.proCompact B f).obj
      ((sideScalar φ X).obj ((Etale.FiniteSmoothPurity.exceptional A f).obj K)) := by
  letI : Algebra A B := φ.toAlgebra
  change ((sheafExtendScalars (algebraMap A B) Y).leftDerivedFunctor).obj
      ((Etale.FiniteSmoothPurity.proCompact A f).obj
        ((Etale.FiniteSmoothPurity.exceptional A f).obj K)) ⟶
    (Etale.FiniteSmoothPurity.proCompact B f).obj
      (((sheafExtendScalars (algebraMap A B) X).leftDerivedFunctor).obj
        ((Etale.FiniteSmoothPurity.exceptional A f).obj K))
  exact (rightDerivedLowerShriekOfCompactificationExtendScalarsMap A B
    (HasCompactification.compactification f)).app
    ((Etale.FiniteSmoothPurity.exceptional A f).obj K)

/-- The canonical Tate-line reduction is the generator-normalized ordered tensor
comparison, including the Kummer power map and the zero-fold scalar unit.
Source: `sk-thm-purity-transport`, Step 1 (finite-level Kummer boundary);
(blueprint: def-pur-general-source-comparison). -/
noncomputable def canonicalTateLineReduction
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X : Scheme.{u}} (φ : A →+* B) (N M d : ℕ) (hMN : M ∣ N)
    (hA : (N : A) = 0) (hB : (M : B) = 0)
    (data : KummerTateLineReductionData (X := X) φ N M d hMN hA hB) :
    (Etale.scalarExtension φ X).obj
        (Etale.FiniteSmoothPurity.line A N hA X d) ⟶
      Etale.FiniteSmoothPurity.line B M hB X d :=
  data.comparison.tensorPower d |>.hom

/-- The concrete side origin reduction, obtained by transposing the inverse
of the canonical side comparison square through the comparison adjunction.
Source: Stacks 07A4, scalar restriction and its adjunction mate;
(blueprint: def-pur-general-source-comparison). -/
noncomputable def sideOriginReduction
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {T : Scheme.{u}} (φ : A →+* B)
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ T)]
    (K : Etale.FiniteSmoothPurity.proCategory A T) :
    (Etale.scalarExtension φ T).obj ((Etale.FiniteSmoothPurity.origin A T).obj K) ⟶
      (Etale.FiniteSmoothPurity.origin B T).obj ((sideScalar φ T).obj K) :=
  (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) T).homEquiv _ _
    ((sideComparisonReductionIso (T := T) φ).inv.app
      ((Etale.FiniteSmoothPurity.origin A T).obj K) ≫
      (sideScalar φ T).map
        ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.app K))

/-- The source comparison is the explicit composite: source-to-origin, live derived
scalar/pullback comparison, the ordinary tensor/Kummer/shift map, origin reduction,
and origin-to-source.  Source: Stacks 06YY and 07A4, `sk-lem-sp-reduction`,
compatibility (3); (blueprint: def-pur-general-source-comparison). -/
noncomputable def canonicalSourceComparisonApp
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} (φ : A →+* B) (f : X ⟶ Y) (N M d : ℕ)
    (hMN : M ∣ N) (hA : (N : A) = 0) (hB : (M : B) = 0)
    (tateData : KummerTateLineReductionData (X := X) φ N M d hMN hA hB)
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ X)]
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ Y)]
    (K : Etale.FiniteSmoothPurity.proCategory A Y) :
    (Etale.FiniteSmoothPurity.proSource A f
        (Etale.FiniteSmoothPurity.line A N hA X d) ⋙ sideScalar φ X).obj K ⟶
      (sideScalar φ Y ⋙ Etale.FiniteSmoothPurity.proSource B f
        (Etale.FiniteSmoothPurity.line B M hB X d)).obj K := by
  let Lₐ := Etale.FiniteSmoothPurity.line A N hA X d
  let Lᵦ := Etale.FiniteSmoothPurity.line B M hB X d
  exact
      (sideScalar φ X).map
          (Etale.FiniteSmoothPurity.sourceToOrigin A f Lₐ K) ≫
        (sideComparisonReductionIso (T := X) φ).hom.app
          ((Etale.FiniteSmoothPurity.puritySource A f Lₐ).obj
            ((Etale.FiniteSmoothPurity.origin A Y).obj K)) ≫
        (Etale.FiniteSmoothPurity.comparison B X).map
          ((Etale.FiniteSmoothPurity.pullbackTwistComparison f d
              tateData.comparison ((Etale.FiniteSmoothPurity.origin A Y).obj K)).hom ≫
            (Etale.FiniteSmoothPurity.puritySource B f Lᵦ).map
              (sideOriginReduction φ K)) ≫
        Etale.FiniteSmoothPurity.sourceFromOrigin B f Lᵦ
          ((sideScalar φ Y).obj K)

/-- The fixed source-comparison component family.

The family is used only on constructible objects, the scope of the finite reduction theorem.
It deliberately carries components rather than a natural-transformation field: the displayed
source-to-origin maps are zero off the counit-isomorphism locus, so unrestricted naturality in
the whole pro-category would be false.
Source: `sk-thm-purity-transport`, Step 1, finite constructible reduction;
(blueprint: def-pur-general-source-comparison). -/
structure CanonicalSourceComparisonData
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} (φ : A →+* B) (f : X ⟶ Y) (N M d : ℕ)
    (hMN : M ∣ N) (hA : (N : A) = 0) (hB : (M : B) = 0)
    (tateData : KummerTateLineReductionData (X := X) φ N M d hMN hA hB)
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ X)]
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ Y)] where
  app : ∀ K : Etale.FiniteSmoothPurity.proCategory A Y,
    (Etale.FiniteSmoothPurity.proSource A f
        (Etale.FiniteSmoothPurity.line A N hA X d) ⋙ sideScalar φ X).obj K ⟶
      (sideScalar φ Y ⋙ Etale.FiniteSmoothPurity.proSource B f
        (Etale.FiniteSmoothPurity.line B M hB X d)).obj K

/-- Package the fixed component formula for constructible finite reduction.
Source: `sk-thm-purity-transport`, Step 1;
(blueprint: def-pur-general-source-comparison). -/
noncomputable def canonicalSourceComparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} (φ : A →+* B) (f : X ⟶ Y) (N M d : ℕ)
    (hMN : M ∣ N) (hA : (N : A) = 0) (hB : (M : B) = 0)
    (tateData : KummerTateLineReductionData (X := X) φ N M d hMN hA hB)
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ X)]
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ Y)] :
    CanonicalSourceComparisonData φ f N M d hMN hA hB tateData :=
  { app := canonicalSourceComparisonApp φ f N M d hMN hA hB tateData }

end AlgebraicGeometry.ProEtale
