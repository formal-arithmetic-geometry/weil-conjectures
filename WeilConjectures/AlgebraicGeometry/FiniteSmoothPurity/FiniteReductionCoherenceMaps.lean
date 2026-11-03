/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionComparisons
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Trace
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal

/-! # Canonical geometric comparisons for finite reduction

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/thm-pur-finite-reduction-of-purity.md, the composition,
base-change and affine-orientation clauses
(blueprint: def-pur-finite-reduction-coherence-maps).

These are actual composites in the ordinary pro-etale module derived categories.
The ordered-power, tensor and pullback comparisons retain their existing owners.
The exceptional compositor is the counit mate, with the site unit inserted at Y.
The smooth exchange is conjugation by the normalized purity maps; its total inverse
is extended by zero away from the isomorphism locus, as for originInverse.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- A coordinate presentation of the canonical diagonal/DNC orientation, retaining its
full existing normalization. Source: the unit-orientation step of finite reduction
(blueprint: def-pur-finite-reduction-coherence-maps). -/
structure NormalizedSmoothDatum (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d : ℕ) (hX : IsUnit (N : Γ(X, ⊤))) where
  geometry : FiniteRingSectionDeformation.Geometry d (pullback.fst f f) (pullback.diagonal f)
  alpha : dualizingComplex A f ≅ line A N hA X d
  normalized : OrientationNormalized A N hN hA f d geometry hX alpha

/-- Pullback of the concrete ordered shifted Tate tensor, through the site comparison
and the restriction-of-roots comparison. Source: composition and base-change sources
(blueprint: def-pur-finite-reduction-coherence-maps). -/
def proLinePullback (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    (proPullback A f).obj ((comparison A Y).obj (line A N hA Y d)) ≅
      (comparison A X).obj (line A N hA X d) :=
  (sitePullbackIso A f).app _ ≪≫ (comparison A X).mapIso
    (vectorIntegrationBaseCoefficientPullback A N hA
      (projectiveLineTraceTransport N hN A hA) f hY d)

/-- Source compositor: pullback composition, ordered Tate-power concatenation (with
symmetry), inverse associator, inverse Tate pullback, inverse tensor pullback.
Shifts are already inside line, so no extra shift coordinates are chosen.
Source: def-pur-composition-comparisons, the eight factors in fixed module coordinates
(blueprint: def-pur-finite-reduction-coherence-maps). -/
def proCompositionSource (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hY : IsUnit (N : Γ(Y, ⊤))) (d e : ℕ) (K : proCategory A Z) :
    (proSource A (f ≫ g) (line A N hA X (d + e))).obj K ≅
      (proSource A f (line A N hA X d)).obj
        ((proSource A g (line A N hA Y e)).obj K) :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  let T := ProEtale.derivedTensor (ModuleCat.{u + 1} A) X
  let F := proPullback A f
  let G := proPullback A g
  let LX := (comparison A X).obj (line A N hA X d)
  let LY := (comparison A Y).obj (line A N hA Y e)
  WeilConjectures.PurityFiniteSetting.compositionTensorMapIso T
      ((ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).app K)
      (WeilConjectures.PurityFiniteSetting.compositionComparisonPowerAdd A N hA X d e) ≪≫
    (show (T.obj ((T.obj (F.obj (G.obj K))).obj
        ((comparison A X).obj (line A N hA X e)))).obj LX ≅
      (T.obj (F.obj (G.obj K))).obj
        ((T.obj ((comparison A X).obj (line A N hA X e))).obj LX) from
      α_ _ _ _).symm ≪≫
    (T.flip.obj LX).mapIso
      ((T.obj (F.obj (G.obj K))).mapIso (proLinePullback A N hN hA f hY e).symm) ≪≫
    (T.flip.obj LX).mapIso
      (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f (G.obj K) LY).symm

/-- The exceptional compositor is the inverse of the conjugate of the actual compact
support compositor, followed by the site adjunction unit at the intermediate scheme.
Source: def-pur-composition-comparisons, standing counit mate
(blueprint: def-pur-finite-reduction-coherence-maps). -/
def proCompositionExceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] (K : proCategory A Z) :
    (exceptional A (f ≫ g)).obj K ⟶ (exceptional A f).obj ((exceptional A g).obj K) :=
  (comparison A X).map
    ((rightDerivedUpperShriekCompIsoOfLowerShriek A f g
      (rightDerivedLowerShriekCompIso A f g)).inv.app ((origin A Z).obj K) ≫
      (rightDerivedUpperShriek A f).map
        ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app
          ((rightDerivedUpperShriek A g).obj ((origin A Z).obj K))))

/-- The Cartesian purity-source comparison, from the actual pullback compositors,
tensor comparison and roots restriction. No base-change isomorphism is supplied.
Source: thm-pur-smooth-base-change-coherence, left vertical arrow
(blueprint: def-pur-finite-reduction-coherence-maps). -/
def proBaseChangeSource (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (sq : IsPullback a f' f b)
    (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) (K : proCategory A Y) :
    (proPullback A a).obj ((proSource A f (line A N hA X d)).obj K) ≅
      (proSource A f' (line A N hA X' d)).obj ((proPullback A b).obj K) :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) a
      ((proPullback A f).obj K) ((comparison A X).obj (line A N hA X d)) ≪≫
    WeilConjectures.PurityFiniteSetting.compositionTensorMapIso
      (ProEtale.derivedTensor (ModuleCat.{u + 1} A) X')
      (((ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a f).app K).symm ≪≫
        (ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) sq.w).app K ≪≫
        (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f' b).app K)
      (proLinePullback A N hN hA a hX d)

/-- Pro-etale realization of the exceptional adjunct of the uniquely normalized
supported Cartier Kummer boundary. For the coordinate zero divisor this is pur_s.
The site unit is inserted on its target, as in exceptional.
Source: thm-pur-affine-line-orientation and Stacks 03PL, 0A45
(blueprint: def-pur-finite-reduction-coherence-maps). -/
def proKummerOrientation (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (N : Γ(T, ⊤))) :
    (comparison A D).obj (ordinaryFiniteUnit A D) ⟶
      (exceptional A i).obj ((comparison A T).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)) :=
  let L := (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧
  let kappa := (ordinary_supported_kummer_uniqueBoundary T N hN A hA hT i hI).choose
  let orientation := (rightDerivedUpperShriekAdjunction A i).homEquiv _ _
    (((rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) i).app (ordinaryFiniteUnit A D)).hom ≫
      supportedExactDerivedMap (lowerStar (ModuleCat.{u + 1} A) i)
        (ordinaryFiniteConstant A D) (Scheme.finiteEtaleTateLine T N A hA) kappa)
  (comparison A D).map (orientation ≫ (rightDerivedUpperShriek A i).map
    ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app L))

/-- Reduction of the shifted rank-one Kummer input, using the shift comparison and
its generator-normalized coefficient-line map. Source: finite affine orientation
(blueprint: def-pur-finite-reduction-coherence-maps). -/
def proKummerInputMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (phi : A →+* B) (N M : ℕ) (hA : (N : A) = 0) (hB : (M : B) = 0)
    (T : Scheme.{u}) (e : CoefficientLineComparison phi N M hA hB T) :
    (proScalar phi T).obj ((comparison A T).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)) ⟶
      (comparison B T).obj ((ordinaryFiniteLine B M hB T)⟦(2 : ℤ)⟧) :=
  (ProEtale.pbcComparisonReduction T phi).hom.app _ ≫
    (comparison B T).map ((scalarShiftIso phi T (2 : ℤ)).hom.app _ ≫
      (shiftFunctor _ (2 : ℤ)).map e.derivedIso.hom)

end AlgebraicGeometry.Etale.FiniteSmoothPurity
