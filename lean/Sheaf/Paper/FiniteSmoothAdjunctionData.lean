/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.FiniteSmoothCoefficientArrows

/-! # Finite-level smooth adjunction data

Source: main-20261015, sk-thm-smooth-purity, sk-prop-sp-orientation,
sk-lem-sp-reduction and its compatibility proof
(blueprint: def-pur-finite-smooth-adjunction-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The degree-zero identification of the empty shifted tensor with the derived unit.
Source: sk-thm-smooth-purity, d=0
(blueprint: def-pur-finite-smooth-adjunction-data). -/
def zeroLineIso (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (X : Scheme.{u}) (d : ℕ) (hd : d = 0) : line A N hA X d ≅ 𝟙_ _ :=
  eqToIso (congrArg (line A N hA X) hd) ≪≫
    singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X

/-- The source identification with f^*K in relative dimension zero.
Source: sk-thm-smooth-purity, d=0
(blueprint: def-pur-finite-smooth-adjunction-data). -/
def zeroSourceMap (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) (hd : d = 0)
    (K : DerivedCategoryModule A Y) :
    (puritySource A f (line A N hA X d)).obj K ⟶
      (ordinaryFinitePullback A f).obj K :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((ordinaryFinitePullback A f).obj K)).map
        (zeroLineIso A N hA X d hd).hom ≫
    (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X
      ((ordinaryFinitePullback A f).obj K)).hom

/-- All finite-level assertions for the specified diagonal orientation and tensor mate.
The non-proof fields are normalized comparisons; no operation is an arbitrary functor.
Source: sk-thm-smooth-purity and sk-prop-sp-orientation
(blueprint: def-pur-finite-smooth-adjunction-data). -/
structure SmoothLevel (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f] (d : ℕ) where
  geometry : FiniteRingSectionDeformation.Geometry d (pullback.fst f f) (pullback.diagonal f)
  invertible : IsUnit (N : Γ(X, ⊤))
  alpha : dualizingComplex (ModuleCat.{u + 1} A) f ≅ line A N hA X d
  orientation : OrientationNormalized A N hN hA f d geometry invertible alpha
  ordinary_isIso : ∀ K : DerivedCategoryModule A Y,
    DerivedCategory.boundedConstructibleFiniteTor A Y K →
    IsIso (gamma A f (line A N hA X d) alpha K)
  ordinary_natural : ∀ (K L : DerivedCategoryModule A Y) (a : K ⟶ L),
    (puritySource A f (line A N hA X d)).map a ≫ gamma A f (line A N hA X d) alpha L =
      gamma A f (line A N hA X d) alpha K ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).map a
  origin_ctf : ∀ K : proCategory A Y, IsCtf A Y K →
    DerivedCategory.boundedConstructibleFiniteTor A Y ((origin A Y).obj K)
  origin_counit : ∀ K : proCategory A Y, IsCtf A Y K →
    IsIso ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app K)
  pro_purity : ∀ K : proCategory A Y, IsCtf A Y K →
    IsCtf A X ((proSource A f (line A N hA X d)).obj K) ∧
    IsCtf A X ((exceptional A f).obj K) ∧
    IsIso (proGamma A f (line A N hA X d) alpha K)
  pro_natural : ∀ (K L : proCategory A Y), IsCtf A Y K → IsCtf A Y L → ∀ a : K ⟶ L,
    (proSource A f (line A N hA X d)).map a ≫
        proGamma A f (line A N hA X d) alpha L =
      proGamma A f (line A N hA X d) alpha K ≫ (exceptional A f).map a
  any_origin : ∀ (K₀ : DerivedCategoryModule A Y),
    DerivedCategory.boundedConstructibleFiniteTor A Y K₀ → ∀ (K : proCategory A Y),
    IsCtf A Y K → ∀ e : (comparison A Y).obj K₀ ≅ K,
    (sourceAtOriginIso A f (line A N hA X d) K₀).hom ≫
        (proSource A f (line A N hA X d)).map e.hom ≫
        proGamma A f (line A N hA X d) alpha K =
      (comparison A X).map (gamma A f (line A N hA X d) alpha K₀) ≫
        (comparison A X).map
          ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).map
            ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app K₀ ≫
              (origin A Y).map e.hom))
  trace_transport : ∀ (K₀ : DerivedCategoryModule A Y),
    DerivedCategory.boundedConstructibleFiniteTor A Y K₀ → ∀ (K : proCategory A Y),
    IsCtf A Y K → ∀ e : (comparison A Y).obj K₀ ≅ K,
    (proCompact A f).map
        ((sourceAtOriginIso A f (line A N hA X d) K₀).hom ≫
          (proSource A f (line A N hA X d)).map e.hom) ≫
        proTrace A f (line A N hA X d) alpha K =
      compactSiteMap A f ((puritySource A f (line A N hA X d)).obj K₀) ≫
        (comparison A Y).map (trace A f (line A N hA X d) alpha K₀) ≫ e.hom
  etale_sum : d = 0 → ∃ C : FiniteSmoothCompactSupportComparisons A,
    FiniteSmoothComparisonNormalized A C
  dimension_zero : ∀ hd : d = 0, ∀ [Etale f],
    ∀ C : FiniteSmoothCompactSupportComparisons A, FiniteSmoothComparisonNormalized A C →
    ∀ K : DerivedCategoryModule A Y,
      gamma A f (line A N hA X d) alpha K ≫
          (finiteSmoothAdjointCoordinates A C f).hom.app K = zeroSourceMap A N hA f d hd K ∧
      trace A f (line A N hA X d) alpha K =
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
            (zeroSourceMap A N hA f d hd K) ≫
          (finiteSmoothSumComparison A C f).hom.app _ ≫
          (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory.map
            ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K) ≫
          ((etaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategoryAdjunction).counit.app K
  unit_ctf : IsCtf A Y (𝟙_ _) ∧
    IsCtf A X ((proSource A f (line A N hA X d)).obj (𝟙_ _)) ∧
    IsCtf A X ((exceptional A f).obj (𝟙_ _))
  unit_degree : ∀ i : ℤ, i ≠ -(2 * (d : ℤ)) →
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) i).obj
        ((proSource A f (line A N hA X d)).obj (𝟙_ _))) ∧
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) i).obj
        ((exceptional A f).obj (𝟙_ _)))

/-- All two-level reduction assertions, with the actual b, c, lambda and their traces.
Source: sk-lem-sp-reduction and its compatibility proof
(blueprint: def-pur-finite-smooth-adjunction-data). -/
structure ReductionData {A B : Type (u + 1)} [CommRing A] [Finite A] [CommRing B] [Finite B]
    (phi : A →+* B) {N M : ℕ} {hN : 0 < N} {hM : 0 < M}
    {hA : (N : A) = 0} {hB : (M : B) = 0}
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f] (d : ℕ)
    (a : SmoothLevel A N hN hA f d) (b : SmoothLevel B M hM hB f d) where
  twist : CoefficientLineComparison phi N M hA hB X
  ordinary_compact : ∀ Q : DerivedCategoryModule A X,
    DerivedCategory.boundedConstructibleFiniteTor A X Q →
    IsIso (ExceptionalCoefficients.compactSupportMap phi
      (HasCompactification.compactification f) Q)
  ordinary_counit : ∀ K : DerivedCategoryModule A Y,
    DerivedCategory.boundedConstructibleFiniteTor A Y K →
    IsIso (ExceptionalCoefficients.mateMap phi f K) ∧
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map
        (ExceptionalCoefficients.mateMap phi f K) ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f).counit.app
        ((ordinaryScalar phi Y).obj K) =
    ExceptionalCoefficients.comparisonInverse phi (HasCompactification.compactification f)
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K) ≫
      (ordinaryScalar phi Y).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).counit.app K)
  ordinary_purity : ∀ K : DerivedCategoryModule A Y,
    DerivedCategory.boundedConstructibleFiniteTor A Y K →
    (ordinaryScalar phi X).map (gamma A f (line A N hA X d) a.alpha K) ≫
        ExceptionalCoefficients.mateMap phi f K =
      (pullbackTwistComparison f d twist K).hom ≫
        gamma B f (line B M hB X d) b.alpha ((ordinaryScalar phi Y).obj K)
  reduction_ctf : ∀ (T : Scheme.{u}) (K : proCategory A T), IsCtf A T K →
    IsCtf B T ((proScalar phi T).obj K)
  pro_compact : ∀ Q : proCategory A X, IsCtf A X Q →
    IsIso (proCompactCoefficientMap phi f Q)
  pro_counit : ∀ K : proCategory A Y, IsCtf A Y K →
    IsIso (proCoefficientMap phi f K) ∧
    (proCompact B f).map (proCoefficientMap phi f K) ≫
        proCounit B f ((proScalar phi Y).obj K) =
      proCompactCoefficientInverse phi f ((exceptional A f).obj K) ≫
        (proScalar phi Y).map (proCounit A f K)
  pro_natural : ∀ (K L : proCategory A Y), IsCtf A Y K → IsCtf A Y L → ∀ v : K ⟶ L,
    (proScalar phi X).map ((exceptional A f).map v) ≫ proCoefficientMap phi f L =
      proCoefficientMap phi f K ≫ (exceptional B f).map ((proScalar phi Y).map v)
  pro_pullback : ∀ K : proCategory A Y, IsCtf A Y K → IsIso (proPullbackMap phi f K)
  pro_purity : ∀ K : proCategory A Y, IsCtf A Y K →
    IsIso (proLambda f d twist K) ∧
    (proScalar phi X).map (proGamma A f (line A N hA X d) a.alpha K) ≫
        proCoefficientMap phi f K =
      proLambda f d twist K ≫
        proGamma B f (line B M hB X d) b.alpha ((proScalar phi Y).obj K)

/-- A positive finite level of the asserted system. The annihilator and the roots
are literally ell^n; the coefficient type is its harmless universe lift.
Source: sk-thm-smooth-purity (blueprint: def-pur-finite-smooth-adjunction-data). -/
def Level (ell n : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [HasCompactification f]
    [QuasiCompact f] [IsSeparated f] (d : ℕ) :=
  SmoothLevel (coefficient ell n) (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
    (CharP.cast_eq_zero _ _) f d

end AlgebraicGeometry.Etale.FiniteSmoothPurity
