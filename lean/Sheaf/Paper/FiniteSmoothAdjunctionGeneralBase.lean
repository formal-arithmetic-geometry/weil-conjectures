/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.FiniteSmoothAdjunctionData
import WeilConjectures.Compactification.NagataCompactification
import Sheaf.Paper.FiniteSmoothLevelOfOrientation
import Sheaf.Paper.FiniteSmoothTwoLevelReduction
import Sheaf.Paper.FiniteSmoothQuotientCoherence
import Sheaf.Paper.FiniteSmoothSiteRealizations
import Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange

/-! # Finite smooth adjunction over an arbitrary field

Source: main-20261015, sk-thm-smooth-purity, sk-prop-sp-orientation,
sk-lem-sp-reduction and its compatibility proof
(blueprint: lem-pur-finite-smooth-adjunction-general-base).

## Main statements

* `FiniteSmoothSystem`: all positive levels and actual quotient cocycles.
* `FiniteSmoothAdjunctionDatum`: the system on a compactification.
* `finiteSmoothAdjunctionGeneralBase`: existence over any field of characteristic not ell.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The scalar associator on the pro-etale site, with the actual quotient composition.
Source: sk-lem-sp-reduction/compatibilities (2)
(blueprint: lem-pur-finite-smooth-adjunction-general-base). -/
def proAssociator (T : Scheme.{u}) (ell : ℕ) {r m n : ℕ}
    (hmr : m ≤ r) (hnm : n ≤ m) :
    proScalar (FiniteReduction.quotient ell hmr) T ⋙
      proScalar (FiniteReduction.quotient ell hnm) T ≅
        proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) T :=
  @ProEtale.pbcFixedScalarExtensionComp.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (Scheme.ProEt.topology T)
    (coefficient ell r) (coefficient ell m) (coefficient ell n)
    inferInstance inferInstance inferInstance
    (FiniteReduction.quotient.{u} ell hmr) (FiniteReduction.quotient ell hnm)
    (FiniteReduction.quotient ell (hnm.trans hmr))
    (RingHom.ext (fun x ↦
      congrArg (fun y : ZMod (ell ^ n) ↦ (⟨⟨y⟩⟩ : coefficient.{u} ell n))
        (DFunLike.congr_fun
          (Subsingleton.elim
            (ZMod.castHom (pow_dvd_pow ell (hnm.trans hmr)) (ZMod (ell ^ n)))
            ((ZMod.castHom (pow_dvd_pow ell hnm) (ZMod (ell ^ n))).comp
              (ZMod.castHom (pow_dvd_pow ell hmr) (ZMod (ell ^ m))))) x.down.down)))


/-- The exceptional cocycle equation for the specified canonical maps.
Source: sk-lem-sp-reduction/compatibilities (2)--(3)
(blueprint: lem-pur-finite-smooth-adjunction-general-base). -/
def HasExceptionalCocycle (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f] : Prop :=
  ∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : DerivedCategoryModule (coefficient ell r) Y),
    DerivedCategory.boundedConstructibleFiniteTor (coefficient ell r) Y K →
    QuotientCocycle
      (ordinaryScalar (FiniteReduction.quotient ell hmr) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) Y)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hmr) X)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) X)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (ordinaryAssociator Y ell hmr hnm)
      (ordinaryAssociator X ell hmr hnm)
      (rightDerivedUpperShriek (ModuleCat.{u + 1} (coefficient ell r)) f)
      (rightDerivedUpperShriek (ModuleCat.{u + 1} (coefficient ell m)) f)
      (rightDerivedUpperShriek (ModuleCat.{u + 1} (coefficient ell n)) f)
      (ExceptionalCoefficients.mateMap (FiniteReduction.quotient ell hmr) f)
      (ExceptionalCoefficients.mateMap (FiniteReduction.quotient ell hnm) f)
      (ExceptionalCoefficients.mateMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K


/-- The twist cocycle equation for the specified canonical maps.
Source: sk-lem-sp-reduction/compatibilities (2)--(3)
(blueprint: lem-pur-finite-smooth-adjunction-general-base). -/
def HasTwistCocycle (ell : ℕ) {X : Scheme.{u}} (d : ℕ)
    (twists : ∀ (r m : ℕ) (_hm : 1 ≤ m) (hmr : m ≤ r),
      CoefficientLineComparison (FiniteReduction.quotient ell hmr) (ell ^ r) (ell ^ m)
        (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X) : Prop :=
  ∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r),
    (ordinaryScalar (FiniteReduction.quotient ell hnm) X).map
        ((twists r m (hn.trans hnm) hmr).tensorPower d).hom ≫
      ((twists m n hn hnm).tensorPower d).hom =
    (ordinaryAssociator X ell hmr hnm).hom.app
        (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X d) ≫
      ((twists r n hn (hnm.trans hmr)).tensorPower d).hom


/-- The pullback cocycle equation for the specified canonical maps.
Source: sk-lem-sp-reduction/compatibilities (2)--(3)
(blueprint: lem-pur-finite-smooth-adjunction-general-base). -/
def HasPullbackCocycle (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f] : Prop :=
  ∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : DerivedCategoryModule (coefficient ell r) Y),
    QuotientCocycle
      (ordinaryScalar (FiniteReduction.quotient ell hmr) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) Y)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hmr) X)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) X)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (ordinaryAssociator Y ell hmr hnm)
      (ordinaryAssociator X ell hmr hnm)
      ((ordinaryFinitePullback (coefficient ell r) f))
      ((ordinaryFinitePullback (coefficient ell m) f))
      ((ordinaryFinitePullback (coefficient ell n) f))
      (ordinaryPullbackMap (FiniteReduction.quotient ell hmr) f)
      (ordinaryPullbackMap (FiniteReduction.quotient ell hnm) f)
      (ordinaryPullbackMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K


/-- The purity cocycle equation for the specified canonical maps.
Source: sk-lem-sp-reduction/compatibilities (2)--(3)
(blueprint: lem-pur-finite-smooth-adjunction-general-base). -/
def HasPurityCocycle (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f] (d : ℕ)
    (twists : ∀ (r m : ℕ) (_hm : 1 ≤ m) (hmr : m ≤ r),
      CoefficientLineComparison (FiniteReduction.quotient ell hmr) (ell ^ r) (ell ^ m)
        (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X) : Prop :=
  ∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : DerivedCategoryModule (coefficient ell r) Y),
    DerivedCategory.boundedConstructibleFiniteTor (coefficient ell r) Y K →
    QuotientCocycle
      (ordinaryScalar (FiniteReduction.quotient ell hmr) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) Y)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hmr) X)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) X)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (ordinaryAssociator Y ell hmr hnm)
      (ordinaryAssociator X ell hmr hnm)
      (finiteSource ell r f d)
      (finiteSource ell m f d)
      (finiteSource ell n f d)
      (finiteLambda ell hmr f d (twists r m (hn.trans hnm) hmr))
      (finiteLambda ell hnm f d (twists m n hn hnm))
      (finiteLambda ell (hnm.trans hmr) f d (twists r n hn (hnm.trans hmr))) K



/-- The pro twist cocycle equation for the specified canonical maps.
Source: sk-lem-sp-reduction/compatibilities (2)--(3)
(blueprint: lem-pur-finite-smooth-adjunction-general-base). -/
def HasProTwistCocycle (ell : ℕ) {X : Scheme.{u}} (d : ℕ)
    (twists : ∀ (r m : ℕ) (_hm : 1 ≤ m) (hmr : m ≤ r),
      CoefficientLineComparison (FiniteReduction.quotient ell hmr) (ell ^ r) (ell ^ m)
        (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X) : Prop :=
  ∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r),
    (proScalar (FiniteReduction.quotient ell hnm) X).map
        (proTwistMap d (twists r m (hn.trans hnm) hmr)) ≫
      proTwistMap d (twists m n hn hnm) =
    (proAssociator X ell hmr hnm).hom.app
        ((comparison (coefficient ell r) X).obj
          (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X d)) ≫
      proTwistMap d (twists r n hn (hnm.trans hmr))


/-- The pro pullback cocycle equation for the specified canonical maps.
Source: sk-lem-sp-reduction/compatibilities (2)--(3)
(blueprint: lem-pur-finite-smooth-adjunction-general-base). -/
def HasProPullbackCocycle (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f] : Prop :=
  ∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : proCategory (coefficient ell r) Y),
    IsCtf (coefficient ell r) Y K →
    QuotientCocycle
      (proScalar (FiniteReduction.quotient ell hmr) Y)
      (proScalar (FiniteReduction.quotient ell hnm) Y)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (proScalar (FiniteReduction.quotient ell hmr) X)
      (proScalar (FiniteReduction.quotient ell hnm) X)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (proAssociator Y ell hmr hnm)
      (proAssociator X ell hmr hnm)
      ((proPullback (coefficient ell r) f))
      ((proPullback (coefficient ell m) f))
      ((proPullback (coefficient ell n) f))
      (proPullbackMap (FiniteReduction.quotient ell hmr) f)
      (proPullbackMap (FiniteReduction.quotient ell hnm) f)
      (proPullbackMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K


/-- The pro compact cocycle equation for the specified canonical maps.
Source: sk-lem-sp-reduction/compatibilities (2)--(3)
(blueprint: lem-pur-finite-smooth-adjunction-general-base). -/
def HasProCompactCocycle (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f] : Prop :=
  ∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : proCategory (coefficient ell r) X),
    IsCtf (coefficient ell r) X K →
    QuotientCocycle
      (proScalar (FiniteReduction.quotient ell hmr) X)
      (proScalar (FiniteReduction.quotient ell hnm) X)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (proScalar (FiniteReduction.quotient ell hmr) Y)
      (proScalar (FiniteReduction.quotient ell hnm) Y)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (proAssociator X ell hmr hnm)
      (proAssociator Y ell hmr hnm)
      (proCompact (coefficient ell r) f)
      (proCompact (coefficient ell m) f)
      (proCompact (coefficient ell n) f)
      (proCompactCoefficientMap (FiniteReduction.quotient ell hmr) f)
      (proCompactCoefficientMap (FiniteReduction.quotient ell hnm) f)
      (proCompactCoefficientMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K


/-- The pro exceptional cocycle equation for the specified canonical maps.
Source: sk-lem-sp-reduction/compatibilities (2)--(3)
(blueprint: lem-pur-finite-smooth-adjunction-general-base). -/
def HasProExceptionalCocycle (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f] : Prop :=
  ∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : proCategory (coefficient ell r) Y),
    IsCtf (coefficient ell r) Y K →
    QuotientCocycle
      (proScalar (FiniteReduction.quotient ell hmr) Y)
      (proScalar (FiniteReduction.quotient ell hnm) Y)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (proScalar (FiniteReduction.quotient ell hmr) X)
      (proScalar (FiniteReduction.quotient ell hnm) X)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (proAssociator Y ell hmr hnm)
      (proAssociator X ell hmr hnm)
      (exceptional (coefficient ell r) f)
      (exceptional (coefficient ell m) f)
      (exceptional (coefficient ell n) f)
      (proCoefficientMap (FiniteReduction.quotient ell hmr) f)
      (proCoefficientMap (FiniteReduction.quotient ell hnm) f)
      (proCoefficientMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K


/-- The pro purity cocycle equation for the specified canonical maps.
Source: sk-lem-sp-reduction/compatibilities (2)--(3)
(blueprint: lem-pur-finite-smooth-adjunction-general-base). -/
def HasProPurityCocycle (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f] (d : ℕ)
    (twists : ∀ (r m : ℕ) (_hm : 1 ≤ m) (hmr : m ≤ r),
      CoefficientLineComparison (FiniteReduction.quotient ell hmr) (ell ^ r) (ell ^ m)
        (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X) : Prop :=
  ∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : proCategory (coefficient ell r) Y),
    IsCtf (coefficient ell r) Y K →
    QuotientCocycle
      (proScalar (FiniteReduction.quotient ell hmr) Y)
      (proScalar (FiniteReduction.quotient ell hnm) Y)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (proScalar (FiniteReduction.quotient ell hmr) X)
      (proScalar (FiniteReduction.quotient ell hnm) X)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (proAssociator Y ell hmr hnm)
      (proAssociator X ell hmr hnm)
      (finiteProSource ell r f d)
      (finiteProSource ell m f d)
      (finiteProSource ell n f d)
      (finiteProLambda ell hmr f d (twists r m (hn.trans hnm) hmr))
      (finiteProLambda ell hnm f d (twists m n hn hnm))
      (finiteProLambda ell (hnm.trans hmr) f d (twists r n hn (hnm.trans hmr))) K

/-- Simultaneous finite purity, actual coefficient comparisons and all quotient cocycles.
Each field retains the canonical maps and its full quotient cocycle equation.
Source: sk-thm-smooth-purity and sk-lem-sp-reduction/compatibilities
(blueprint: lem-pur-finite-smooth-adjunction-general-base). -/
def FiniteSmoothSystem (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f] (d : ℕ) : Prop :=
  ∃ (level : ∀ n : ℕ, 1 ≤ n → Level ell n f d),
  ∃ (reduction : ∀ (r m : ℕ) (hm : 1 ≤ m) (hmr : m ≤ r),
    ReductionData (FiniteReduction.quotient ell hmr) f d
      (level r (hm.trans hmr)) (level m hm)),
  /- intrinsic_compact -/
  (∀ (n : ℕ) (_hn : 1 ≤ n) (M : proCategory (coefficient ell n) X),
    IsCtf (coefficient ell n) X M →
    Nonempty ((FiniteReduction.realize Y ell n).obj ((proCompact (coefficient ell n) f).obj M) ≅
      (Scheme.sfIntrinsicCompactSupport (HasCompactification.compactification f)
        (FiniteReduction.Ring.{u} ell n)).obj ((FiniteReduction.realize X ell n).obj M))) ∧
  /- root_transport -/
  (∀ n : ℕ, 1 ≤ n →
    Nonempty (RootSiteTransport ell n X) ∧ Nonempty (RootSiteTransport ell n Y)) ∧
  /- compact_cocycle -/
  (ExceptionalCoefficients.CompactSupportCocycle ell f) ∧
  /- exceptional_cocycle -/
  (HasExceptionalCocycle ell f) ∧
  /- twist_cocycle -/
  (HasTwistCocycle ell d
    (fun r m hm hmr ↦ (reduction r m hm hmr).twist)) ∧
  /- pullback_cocycle -/
  (HasPullbackCocycle ell f) ∧
  /- purity_cocycle -/
  (HasPurityCocycle ell f d
    (fun r m hm hmr ↦ (reduction r m hm hmr).twist)) ∧
  /- pro_twist_cocycle -/
  (HasProTwistCocycle ell d
    (fun r m hm hmr ↦ (reduction r m hm hmr).twist)) ∧
  /- pro_pullback_cocycle -/
  (HasProPullbackCocycle ell f) ∧
  /- pro_compact_cocycle -/
  (HasProCompactCocycle ell f) ∧
  /- pro_exceptional_cocycle -/
  (HasProExceptionalCocycle ell f) ∧
  /- pro_purity_cocycle -/
  (HasProPurityCocycle ell f d
    (fun r m hm hmr ↦ (reduction r m hm hmr).twist))

/-- The system on a specified compactification, with Noetherian witnesses as conclusions.
Source: sk-thm-smooth-purity over a field
(blueprint: lem-pur-finite-smooth-adjunction-general-base). -/
def FiniteSmoothAdjunctionDatum (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsSeparated f] (d : ℕ)
    (c : Compactification f) (hX : IsNoetherian X) (hY : IsNoetherian Y) : Prop :=
  letI := c.hasCompactification
  letI := hX
  letI := hY
  FiniteSmoothSystem ell f d

private theorem normalizedOrientation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (hX : IsUnit (N : Γ(X, ⊤))) :
    ∃ (G : FiniteRingSectionDeformation.Geometry d
        (pullback.fst f f) (pullback.diagonal f))
      (alpha : dualizingComplex (ModuleCat.{u + 1} A) f ≅ line A N hA X d),
      OrientationNormalized A N hN hA f d G hX alpha := by
  let G := FiniteRingSectionDeformation.geometry d (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f)
  have := G
  obtain ⟨κ, hκ, _⟩ := FiniteRingSectionDeformation.existsUnique_normalized
    N hN A hA hX d (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)
  have : HasInvertibleExponent A X := ⟨N, hN, hA, hX⟩
  have : IsIso (dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f f).flip) := by
    have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension
      A f d (IsPullback.of_hasPullback f f).flip
    exact (isIso_dualizingComplexBaseChangeMap_iff A _).2 inferInstance
  have : IsIso (finiteSmoothDiagonalFactor A f) := by
    unfold finiteSmoothDiagonalFactor
    infer_instance
  have := FiniteRingSectionDeformation.isIso_specialization
    N hN A hA hX d (pullback.fst f f) (pullback.diagonal f)
      (pullback.diagonal_fst f) κ hκ
  let q := reesConeComparison (pullback.diagonal f) ≪≫
    FiniteRingSectionDeformation.coneBundleIso d (pullback.fst f f) (pullback.diagonal f)
  have hq : q.hom ≫ VectorBundleZeroSection.π X d
      (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) =
      Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f) := by
    dsimp [q]
    rw [Category.assoc,
      (FiniteRingSectionDeformation.coneBundleIso_spec d (pullback.fst f f)
        (pullback.diagonal f) (pullback.diagonal_fst f)).1,
      (reesConeComparison_spec (pullback.diagonal f)).1]
    exact Scheme.Hom.purityNormalProjection_eq _ _ (pullback.diagonal_fst f)
  have sq : IsPullback q.hom
      (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
      (VectorBundleZeroSection.π X d (ConormalGradedAlgebra.piece (pullback.diagonal f) 1))
      (𝟙 X) := IsPullback.of_horiz_isIso ⟨by simpa using hq⟩
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have : SmoothOfRelativeDimension d
      (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f)) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace
        (pullback.fst f f) (pullback.diagonal f)) inferInstance
  let π := VectorBundleZeroSection.π X d
    (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)
  have : SmoothOfRelativeDimension d π := by
    apply (MorphismProperty.cancel_left_of_respectsIso
      (@SmoothOfRelativeDimension d) q.hom π).mp
    rw [hq]
    infer_instance
  have : HasInvertibleExponent A (VectorBundleZeroSection.scheme X d
      (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)) :=
    HasInvertibleExponent.of_hom π
  let := (vectorBundlePurityCompactification X d
    (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)).hasCompactification
  have : IsIso (dualizingComplexBaseChangeMap A sq) := by
    have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension A π d sq
    exact (isIso_dualizingComplexBaseChangeMap_iff A sq).2 inferInstance
  have : IsIso (normalSectionMap A d (pullback.fst f f) (pullback.diagonal f)
      (pullback.diagonal_fst f) sq) := by
    unfold normalSectionMap NoetherianSectionSpecialization.sectionMap
    infer_instance
  have := (FiniteRingSectionDeformation.bundleAdjoint_isIso
    N hN A hA X hX d (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)).2
  let alpha : dualizingComplex (ModuleCat.{u + 1} A) f ≅ line A N hA X d :=
    asIso (finiteSmoothDiagonalFactor A f) ≪≫
      asIso (NoetherianSectionSpecialization.specialization A
        (pullback.fst f f) (pullback.diagonal f) κ) ≪≫
      (asIso (normalSectionMap A d (pullback.fst f f) (pullback.diagonal f)
        (pullback.diagonal_fst f) sq)).symm ≪≫
      FiniteRingSectionDeformation.bundleOrientation N hN A hA X hX d
        (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)
  refine ⟨G, alpha, κ, hκ, sq, ?_⟩
  dsimp [alpha, FiniteRingSectionDeformation.bundleOrientation]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]

/-- Finite smooth purity with Kummer/diagonal normalization, actual adjunction counits,
and coherent reduction for every positive quotient, over any ground field.
Source: main-20261015, sk-thm-smooth-purity, sk-prop-sp-orientation and
sk-lem-sp-reduction/compatibilities
(blueprint: lem-pur-finite-smooth-adjunction-general-base).

Proof:
1. Finite type over the ground field makes X and Y Noetherian. Nagata supplies the
   compactification. The characteristic hypothesis makes ell a global unit, hence
   makes every positive ell-power a global unit and gives the required stalk units.
2. Construct the orientation from the diagonal smooth-base-change isomorphism,
   normalized section specialization, the actual Rees/cone-to-bundle comparison and
   inverse bundle integration. The projection identities give the required pullback
   square. Cancellation proves the complete OrientationNormalized equation.
3. Apply finiteSmoothLevelOfOrientation at each positive level. Its only geometric
   remainder is the separate rank-zero normalization; it proves the tensor, origin,
   counit, trace, constructibility, Tor and degree assertions. Apply
   finiteSmoothTwoLevelReduction to each pair for the source's independent two-level
   argument: normalized root comparison, coefficient compatibility of the diagonal,
   deformation and bundle orientation, followed by tensor/counit and site transport.
4. The proved finiteSmoothSiteRealizations supplies normalized root transport on X
   and Y. The existing intrinsic compact-support comparison supplies the requested
   realization. Apply finiteSmoothQuotientCoherence to the resulting normalized
   twists for the compact-support cocycle and the eight other quotient equations.
   The existing exceptional coefficient comparison, using that compact-support
   cocycle, gives the remaining ordinary exceptional cocycle. Assemble the system.
   Witness selections occur only inside this existential proof.
-/
theorem finiteSmoothAdjunctionGeneralBase
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [Fact (ringChar k ≠ ell)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (d : ℕ) [SmoothOfRelativeDimension d f] :
    ∃ (c : Compactification f) (hX : IsNoetherian X) (hY : IsNoetherian Y),
      FiniteSmoothAdjunctionDatum ell f d c hX hY := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have hX : IsNoetherian X := {}
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have hY : IsNoetherian Y := {}
  let c := NagataCompactification f
  refine ⟨c, hX, hY, ?_⟩
  change FiniteSmoothSystem ell f d
  have hk : IsUnit (ell : k) :=
    (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ell.Prime)
      (Fact.out : ringChar k ≠ ell)).isUnit
  have hSpec : IsUnit (ell : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using hk.map (Scheme.ΓSpecIso (.of k)).inv.hom
  have hXu : IsUnit (ell : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hSpec.map (X ↘ Spec (.of k)).appTop.hom
  have hYu : IsUnit (ell : Γ(Y, ⊤)) := by
    simpa only [map_natCast] using hSpec.map (Y ↘ Spec (.of k)).appTop.hom
  have hYs : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y) := by
    intro y
    simpa only [map_natCast] using hYu.map (Y.presheaf.germ ⊤ y trivial).hom
  have hlevels : ∀ (n : ℕ) (_hn : 1 ≤ n), Nonempty (Level ell n f d) := by
    intro n hn
    have hXn : IsUnit ((ell ^ n : ℕ) : Γ(X, ⊤)) := by
      simpa only [Nat.cast_pow] using hXu.pow n
    obtain ⟨G, alpha, hAlpha⟩ := normalizedOrientation (coefficient ell n) (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) (CharP.cast_eq_zero _ _) f d hXn
    exact finiteSmoothLevelOfOrientation ell f d hYs n hn G hXn alpha hAlpha
  let level (n : ℕ) (hn : 1 ≤ n) := (hlevels n hn).some
  have hreductions : ∀ (r m : ℕ) (hm : 1 ≤ m) (hmr : m ≤ r),
      Nonempty (ReductionData (FiniteReduction.quotient ell hmr) f d
        (level r (hm.trans hmr)) (level m hm)) := by
    intro r m hm hmr
    exact finiteSmoothTwoLevelReduction ell f d hYs r m hm hmr
      (level r (hm.trans hmr)) (level m hm)
  let reduction (r m : ℕ) (hm : 1 ≤ m) (hmr : m ≤ r) :=
    (hreductions r m hm hmr).some
  have hRoots := finiteSmoothSiteRealizations ell f d hYs
  have hIntrinsic : ∀ (n : ℕ) (_hn : 1 ≤ n)
      (M : proCategory (coefficient ell n) X), IsCtf (coefficient ell n) X M →
      Nonempty ((FiniteReduction.realize Y ell n).obj
          ((proCompact (coefficient ell n) f).obj M) ≅
        (Scheme.sfIntrinsicCompactSupport (HasCompactification.compactification f)
          (FiniteReduction.Ring.{u} ell n)).obj ((FiniteReduction.realize X ell n).obj M)) := by
    intro n _ M _
    exact ⟨((ProEtale.sfIntrinsicCompactSupportComparison (FiniteReduction.Ring ell n)
      (HasCompactification.compactification f)).app M).symm⟩
  obtain ⟨hb, hCoherence⟩ := finiteSmoothQuotientCoherence ell f d hYs
    (fun r m hm hmr ↦ (reduction r m hm hmr).twist)
  have he : HasExceptionalCocycle ell f := by
    intro r m n hn hnm hmr K hK
    exact (exceptional_coefficient_comparison ell r m d hmr (hn.trans hnm) f hYs hb).2.2.2.1
      n hnm hn K hK
  exact ⟨level, reduction, hIntrinsic, hRoots, hb, he, hCoherence⟩

end AlgebraicGeometry.Etale.FiniteSmoothPurity
