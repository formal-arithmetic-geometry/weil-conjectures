/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import Sheaf.Paper.ExceptionalCoefficientComparison
public import Sheaf.Paper.FiniteSmoothCanonicalInterfaces
public import Sheaf.Paper.FiniteRingSectionDeformation
public import Sheaf.Paper.FiniteSmoothGammaNormalization
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude

/-! # Finite smooth adjunction over an arbitrary field

Source: main-20261015 blueprint, sec-smooth-purity/sk-thm-smooth-purity,
sk-prop-sp-orientation and sk-lem-sp-reduction/compatibilities
(blueprint: def-pur-finite-smooth-canonical-maps).

The ordinary maps below have fixed adjunction-mate formulas. Their pro-etale realizations
are specified on every etale-origin representative, including the comparison counit.
The coefficient rings in the final assertion are exactly Z/(ell^n), with n positive.

## Main definitions

* `IsCtf`: the intrinsic bounded constructible finite-Tor domain.
* `OrientationNormalized`: the diagonal/deformation/Kummer equation fixing alpha.
* `gamma`, `proGamma`: the specified tensor counit mate and its site transport.
* `proCounit`, `proTrace`: the transported actual counit and the adjoint trace.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The module-universe presentation of Z/(ell^n). Source: sk-lem-sp-reduction
(blueprint: def-pur-finite-smooth-canonical-maps). -/
abbrev coefficient (ell n : ℕ) : Type (u + 1) := FiniteReduction.Coeff.{u} ell n

/-- The actual comparison image of the degree-one finite root line.
Source: sk-thm-smooth-purity and Stacks 03PK
(blueprint: def-pur-finite-smooth-canonical-maps). -/
def proRootLine (ell n : ℕ) (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (coefficient ell n)) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (coefficient ell n)) T).obj
    (Scheme.finiteEtaleTateLine T (ell ^ n) (coefficient ell n) (CharP.cast_eq_zero _ _))

/-- The same sheaf after forgetting its canonical Z/(ell^n)-action.
Source: Stacks 03PK (blueprint: def-pur-finite-smooth-canonical-maps). -/
def proRootUnderlying (ell n : ℕ) (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} (coefficient ell n)) AddCommGrpCat.{u + 1})).obj
      (proRootLine ell n T)

set_option genSizeOf false in
set_option genInjectivity false in
/-- Identification with the actual pro-etale kernel of the power map. Its value on
all roots from all etale tests is prescribed after inclusion in units. These generators
and the sheafification adjunction determine the map, including its scalar action.
Source: Stacks 03PK, 099R (blueprint: def-pur-finite-smooth-canonical-maps). -/
structure RootSiteTransport (ell n : ℕ) (T : Scheme.{u}) where
  iso : proRootUnderlying ell n T ≅ Scheme.proEtaleRootsOfUnitySheaf T (ell ^ n)
  normalized : ∀ (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (v : W.unop ⟶ (Scheme.toProEt T).obj U.unop)
    (z : (T.rootsOfUnitySheaf (ell ^ n)).obj.obj U),
    (Scheme.proEtaleRootsOfUnityInclusion T (ell ^ n)).hom.app W
        (iso.hom.hom.app W
          ((proRootLine ell n T).obj.map v.op
            (((ProEtale.comparisonAdjunction
              (ModuleCat.{u + 1} (coefficient ell n)) T).unit.app
                (Scheme.finiteEtaleTateLine T (ell ^ n) (coefficient ell n)
                  (CharP.cast_eq_zero _ _))).hom.app U
              (Scheme.finiteEtaleTateOneGenerator (coefficient ell n) (ell ^ n) T
                (CharP.cast_eq_zero _ _) U 1 z)))) =
      ULift.up (Additive.ofMul
        (Units.map v.left.appTop.hom.toMonoidHom
          (Additive.toMul (((kernel.ι ((ell ^ n) • 𝟙 T.gmSheaf)).hom.app U z).down))))

variable (A : Type (u + 1)) [CommRing A]

/-- The fixed-coefficient presentation of the small pro-etale derived category.
Source: sk-thm-smooth-purity (blueprint: def-pur-finite-smooth-canonical-maps). -/
abbrev proCategory (T : Scheme.{u}) : Type (u + 2) :=
  _root_.DerivedCategory.{u + 1, u + 1, u + 2}
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- The actual comparison inverse image. Source: Stacks 099R
(blueprint: def-pur-finite-smooth-canonical-maps). -/
def comparison (T : Scheme.{u}) : DerivedCategoryModule A T ⥤ proCategory A T :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory

/-- The actual Rnu_*. It is used on the bounded constructible essential image only.
Source: Stacks 099R (blueprint: def-pur-finite-smooth-canonical-maps). -/
def origin (T : Scheme.{u}) : proCategory A T ⥤ DerivedCategoryModule A T :=
  (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctor

/-- Intrinsic finite-stratification constructibility, boundedness, and finite Tor amplitude.
The Tor interval tests every pro-etale module sheaf, and is ordered explicitly.
Source: the two recorded pro-etale finiteness definitions and sk-thm-smooth-purity
(blueprint: def-pur-finite-smooth-canonical-maps). -/
def IsCtf [Finite A] (T : Scheme.{u}) (K : proCategory A T) : Prop :=
  (∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf T A
    ((_root_.DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) i).obj K)) ∧
  (∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) i).obj K)) ∧
  ∃ a b : ℤ, a ≤ b ∧
    ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) T a b K

/-- The recorded pro-etale derived inverse image, with its instances elaborated once.
Source: Stacks 099R (blueprint: def-pur-finite-smooth-canonical-maps). -/
def proPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proCategory A Y ⥤ proCategory A X :=
  (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor

/-- The specified nu^* f^times Rnu_* functor. Source: sk-thm-smooth-purity
(blueprint: def-pur-finite-smooth-canonical-maps). -/
def exceptional [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : proCategory A Y ⥤ proCategory A X :=
  origin A Y ⋙ rightDerivedUpperShriek (ModuleCat.{u + 1} A) f ⋙ comparison A X

/-- The ordered tensor model A_T(d)[2d], made of the actual finite root line.
The zero-fold tensor is the ordinary constant coefficient complex.
Source: sk-prop-sp-orientation and def-pur-roots-of-unity-sheaf
(blueprint: def-pur-finite-smooth-canonical-maps). -/
def line (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) (d : ℕ) :
    DerivedCategoryModule A T :=
  affineLinearBaseCoefficient A N hA T d

/-- Inverse image tensored with the indicated orientation line.
Source: sk-thm-smooth-purity (blueprint: def-pur-finite-smooth-canonical-maps). -/
def puritySource {X Y : Scheme.{u}} (f : X ⟶ Y) (L : DerivedCategoryModule A X) :
    DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X :=
  (ordinaryFinitePullback A f) ⋙
    (derivedTensor (ModuleCat.{u + 1} A) X).flip.obj L

/-- The specified three-factor gamma: the tensor model supplies reassociation, then
1 tensor alpha inverse, then the canonical projection-formula/counit transpose phi.
Source: sk-thm-smooth-purity (blueprint: def-pur-finite-smooth-canonical-maps). -/
def gamma [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : DerivedCategoryModule A X)
    (alpha : dualizingComplex (ModuleCat.{u + 1} A) f ≅ L)
    (K : DerivedCategoryModule A Y) :
    (puritySource A f L).obj K ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((ordinaryFinitePullback A f).obj K)).map alpha.inv ≫
    smoothTensorDualityMap (ModuleCat.{u + 1} A) f
      (isIso_projectionMap_of_finite A f) K

/-- The actual adjunct of gamma. Normalization comes from alpha, rather than from a
separate unconstrained trace. Source: sk-thm-smooth-purity
(blueprint: def-pur-finite-smooth-canonical-maps). -/
def trace [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : DerivedCategoryModule A X)
    (alpha : dualizingComplex (ModuleCat.{u + 1} A) f ≅ L)
    (K : DerivedCategoryModule A Y) :=
  (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map (gamma A f L alpha K) ≫
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).counit.app K

/-- The normal-cone to bundle exceptional mate, with the identity inverse-image
constraint. Source: sk-prop-sp-orientation
(blueprint: def-pur-finite-smooth-canonical-maps). -/
def normalSectionMap [Finite A] {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) (s : S ⟶ V) [IsClosedImmersion s]
    [FiniteRingSectionDeformation.Geometry d g s]
    (hs : s ≫ g = 𝟙 S)
    (sq : IsPullback
      (reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso d g s).hom
      (Scheme.Hom.normalConeProj g s)
      (VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)) (𝟙 S)) :
    (ordinaryFinitePullback A
        (VectorBundleZeroSection.zero S d (ConormalGradedAlgebra.piece s 1))).obj
      ((FiniteRingSectionDeformation.bundleRight A S d
        (ConormalGradedAlgebra.piece s 1)).obj (𝟙_ _)) ⟶
      sectionInvariant A (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection :=
  letI := (vectorBundlePurityCompactification S d
    (ConormalGradedAlgebra.piece s 1)).hasCompactification
  (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.app _ ≫
    NoetherianSectionSpecialization.sectionMap A
      (VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1))
      (Scheme.Hom.normalConeProj g s) (𝟙 S)
      (reesConeComparison s ≪≫ FiniteRingSectionDeformation.coneBundleIso d g s).hom sq
      (VectorBundleZeroSection.zero S d (ConormalGradedAlgebra.piece s 1))
      s.normalConeZeroSection (by
        rw [Iso.trans_hom, ← Category.assoc,
          (reesConeComparison_spec s).2.1,
          (FiniteRingSectionDeformation.coneBundleIso_spec d g s hs).2,
          Category.id_comp])

/-- The orientation equation, before inverting the bundle factor. The Rees comparison
is normalized by its t=1 mate, and the final factor is the adjoint of Kummer-normalized
bundle integration. This fixes alpha, including its scalar and sign.
Source: sk-prop-sp-orientation (blueprint: def-pur-finite-smooth-canonical-maps). -/
def OrientationNormalized [Finite A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f] [IsSeparated f] (d : ℕ)
    (G : FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (hX : IsUnit (N : Γ(X, ⊤)))
    (alpha : dualizingComplex (ModuleCat.{u + 1} A) f ≅ line A N hA X d) : Prop :=
  letI := G
  ∃ kappa : NoetherianSectionSpecialization.family A
      (pullback.fst f f) (pullback.diagonal f) ≅
    (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) X ↘ X)).obj
      (sectionInvariant A (pullback.fst f f) (pullback.diagonal f)),
  NoetherianSectionSpecialization.Normalized A (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f) kappa ∧
    ∃ (sq : IsPullback
      ((reesConeComparison (pullback.diagonal f) ≪≫
        FiniteRingSectionDeformation.coneBundleIso d (pullback.fst f f) (pullback.diagonal f)).hom)
      (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
      (VectorBundleZeroSection.π X d (ConormalGradedAlgebra.piece (pullback.diagonal f) 1))
      (𝟙 X)),
    finiteSmoothDiagonalFactor A f ≫
      NoetherianSectionSpecialization.specialization A
        (pullback.fst f f) (pullback.diagonal f) kappa =
    alpha.hom ≫
      FiniteRingSectionDeformation.bundleSectionAdjoint N hN A hA X hX d
        (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) ≫
      normalSectionMap A d (pullback.fst f f) (pullback.diagonal f)
        (pullback.diagonal_fst f) sq


/-- The canonical site/pullback identification, obtained by deriving the published
comparison square and identifying exact comparison with its total derived functor.
Source: Stacks 099R (blueprint: def-pur-finite-smooth-canonical-maps). -/
def sitePullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    comparison A Y ⋙ (proPullback A f) ≅
      (ordinaryFinitePullback A f) ⋙ comparison A X :=
  Functor.isoWhiskerRight
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} A) Y).leftDerivedFunctorIsoMapDerivedCategory).symm _ ≪≫
    Functor.leftDerivedFunctorCompNatIso (upperStar (ModuleCat.{u + 1} A) f)
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y)
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f)
      (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f) ≪≫
    Functor.isoWhiskerLeft _
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).leftDerivedFunctorIsoMapDerivedCategory

/-- The actual pro-etale pullback tensored with the comparison of the concrete line.
Source: sk-thm-smooth-purity (blueprint: def-pur-finite-smooth-canonical-maps). -/
def proSource {X Y : Scheme.{u}} (f : X ⟶ Y) (L : DerivedCategoryModule A X) :
    proCategory A Y ⥤ proCategory A X :=
  (proPullback A f) ⋙
    (ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).flip.obj ((comparison A X).obj L)

/-- The specified ordinary purity source at a literal positive-power coefficient level.
This specializes the existing source functor; it introduces no new tensor operation.
Source: sk-thm-smooth-purity (blueprint: def-pur-finite-smooth-canonical-maps). -/
def finiteSource (ell n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    DerivedCategoryModule (coefficient ell n) Y ⥤ DerivedCategoryModule (coefficient ell n) X :=
  puritySource (coefficient ell n) f
    (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d)

/-- The same literal-level specialization of the actual pro-etale purity source.
Source: sk-thm-smooth-purity (blueprint: def-pur-finite-smooth-canonical-maps). -/
def finiteProSource (ell n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    proCategory (coefficient ell n) Y ⥤ proCategory (coefficient ell n) X :=
  proSource (coefficient ell n) f
    (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d)

/-- The source identification on any ordinary origin, using the fixed tensor and
pullback comparisons. Source: sk-thm-smooth-purity, final transport
(blueprint: def-pur-finite-smooth-canonical-maps). -/
def sourceAtOriginIso [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : DerivedCategoryModule A X)
    (K : DerivedCategoryModule A Y) :
    (comparison A X).obj ((puritySource A f L).obj K) ≅
      (proSource A f L).obj ((comparison A Y).obj K) :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  letI : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} A)
    ((ordinaryFinitePullback A f).obj K)).app L ≪≫
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      ((sitePullbackIso A f).app K).symm).app ((comparison A X).obj L)

/-- Total inverse of the comparison counit, extended by zero off its isomorphism
locus. Every use in the assertion is on that locus, proved for intrinsic Dctf.
Source: Stacks 099R (blueprint: def-pur-finite-smooth-canonical-maps). -/
def originInverse (T : Scheme.{u}) (K : proCategory A T) :
    K ⟶ (comparison A T).obj ((origin A T).obj K) :=
  open Classical in
  if h : IsIso ((ProEtale.derivedComparisonAdjunction
      (ModuleCat.{u + 1} A) T).counit.app K) then
    @inv _ _ _ _ ((ProEtale.derivedComparisonAdjunction
      (ModuleCat.{u + 1} A) T).counit.app K) h
  else 0

/-- Pull back the inverse origin counit and then undo the canonical source comparison.
Source: sk-thm-smooth-purity (blueprint: def-pur-finite-smooth-canonical-maps). -/
def sourceToOrigin [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) (L : DerivedCategoryModule A X)
    (K : proCategory A Y) :
    (proSource A f L).obj K ⟶
      (comparison A X).obj ((puritySource A f L).obj ((origin A Y).obj K)) :=
  (proSource A f L).map (originInverse A Y K) ≫
    (sourceAtOriginIso A f L ((origin A Y).obj K)).inv

/-- The reverse source comparison, using the actual origin counit.
Source: sk-thm-smooth-purity (blueprint: def-pur-finite-smooth-canonical-maps). -/
def sourceFromOrigin [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) (L : DerivedCategoryModule A X)
    (K : proCategory A Y) :
    (comparison A X).obj ((puritySource A f L).obj ((origin A Y).obj K)) ⟶
      (proSource A f L).obj K :=
  (sourceAtOriginIso A f L ((origin A Y).obj K)).hom ≫
    (proSource A f L).map
      ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app K)

/-- The actual transported purity map on pro-etale complexes, with the actual derived
pullback/tensor source and nu^* f^times Rnu_* target.
Source: sk-thm-smooth-purity (blueprint: def-pur-finite-smooth-canonical-maps). -/
def proGamma [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : DerivedCategoryModule A X) (alpha : dualizingComplex (ModuleCat.{u + 1} A) f ≅ L)
    (K : proCategory A Y) :
    (proSource A f L).obj K ⟶ (exceptional A f).obj K :=
  sourceToOrigin A f L K ≫
    (comparison A X).map (gamma A f L alpha ((origin A Y).obj K))


/-- Compact support on the fixed pro-etale presentation, on the selected compactification.
Source: def-compact-support-direct-image-detailed
(blueprint: def-pur-finite-smooth-canonical-maps). -/
def proCompact {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    proCategory A X ⥤ proCategory A Y :=
  ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (HasCompactification.compactification f)

/-- The actual open/proper site comparison at a bounded-below representative. Its zero
extension only makes it total outside the asserted domain. The proper constituent is
explicitly the counit mate. Source: Stacks 09AF and 099R
(blueprint: def-pur-finite-smooth-canonical-maps). -/
def compactSiteMap [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) :
    (proCompact A f).obj ((comparison A X).obj M) ⟶
      (comparison A Y).obj ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) :=
  open Classical in
  if h : _root_.DerivedCategory.TStructure.t.plus M then
    (ProEtale.compactSupportSiteComparison A
      (HasCompactification.compactification f)).hom.app ⟨M, h⟩
  else 0

/-- The inverse of the same normalized site comparison, on the same bounded-below locus.
Source: Stacks 09AF and 099R
(blueprint: def-pur-finite-smooth-canonical-maps). -/
def compactSiteInverse [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) :
    (comparison A Y).obj ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ⟶
      (proCompact A f).obj ((comparison A X).obj M) :=
  open Classical in
  if h : _root_.DerivedCategory.TStructure.t.plus M then
    (ProEtale.compactSupportSiteComparison A
      (HasCompactification.compactification f)).inv.app ⟨M, h⟩
  else 0

/-- The transported compact-support/exceptional counit on the constructible domain.
Every arrow is the specified site mate or one of the two actual adjunction counits.
Source: sk-thm-smooth-purity (blueprint: def-pur-finite-smooth-canonical-maps). -/
def proCounit [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : proCategory A Y) : (proCompact A f).obj ((exceptional A f).obj K) ⟶ K :=
  compactSiteMap A f
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj ((origin A Y).obj K)) ≫
    (comparison A Y).map
      ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).counit.app
        ((origin A Y).obj K)) ≫
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app K

/-- The trace on pro-etale Dctf with its transported actual counit.
Source: sk-thm-smooth-purity (blueprint: def-pur-finite-smooth-canonical-maps). -/
def proTrace [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : DerivedCategoryModule A X) (alpha : dualizingComplex (ModuleCat.{u + 1} A) f ≅ L)
    (K : proCategory A Y) :
    (proCompact A f).obj ((proSource A f L).obj K) ⟶ K :=
  (proCompact A f).map (proGamma A f L alpha K) ≫ proCounit A f K


end AlgebraicGeometry.Etale.FiniteSmoothPurity
