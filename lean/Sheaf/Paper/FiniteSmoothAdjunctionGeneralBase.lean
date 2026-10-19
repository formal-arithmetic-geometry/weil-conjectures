/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.FiniteSmoothAdjunctionData
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.Paper.FiniteReductionConstructibility
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.Paper.EtaleUnboundedRestrictionComparison
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Sheaf.Paper.ExceptionalCoefficientComparison
import Sheaf.Targets.VectorBundlePurity
import Sheaf.AlgebraicGeometry.VectorBundleIntegration
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension
import Sheaf.Paper.NoetherianEtaleSectionSpecialization
import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
import Sheaf.Paper.PurityDiagonalOrientationCompatibility
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.FiniteRingSectionDeformation
import Sheaf.Paper.FiniteSmoothGammaNormalization
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin

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
set_option warn.sorry false
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

/-- Finite smooth purity with Kummer/diagonal normalization, actual adjunction counits,
and coherent reduction for every positive quotient, over any ground field.
Source: main-20261015, sk-thm-smooth-purity, sk-prop-sp-orientation and
sk-lem-sp-reduction/compatibilities
(blueprint: lem-pur-finite-smooth-adjunction-general-base).

Proof:
1. The characteristic hypothesis makes ell^n invertible, so its root scheme is finite
   etale. Comparison identifies it by its inclusion into units and hence identifies every
   tensor power. A field is Noetherian; finite type makes X and Y Noetherian. The graph
   factorization
   makes f separated finite type; Nagata gives a compactification and the ordinary
   compact-support adjunction. No ambient unbounded pro-etale adjoint is used.
2. Finite reduction on bounded flat K-flat models preserves intrinsic constructibility,
   the ordered Tor interval, and ordinary etale origin, without quotient flatness.
3. Form b on one compactification by identity/zero for the open factor and the proper
   projection/counit mate. Tensor associativity gives its quotient cocycle.
4. The exceptional coefficient comparison theorem gives the actual counit transpose c,
   its naturality, tensor-map equation and base-change compatibility before invertibility.
5. Kummer/projective-line integration defines the bundle orientation. Its unit and common
   Kummer Chern class commute with reduction. Iterate the ordered affine-line counits;
   trivializing covers and degree-zero full faithfulness glue the trace equality.
6. Apply normalized section specialization to the diagonal. The finite-ring section
   deformation theorem supplies its geometry and canonical symmetric-algebra comparison.
   Transport the Rees zero fibre by the uniquely specified homogeneous comparison, then
   by coneBundleIso; coneBundleIso_spec supplies its projection and zero-section identities.
   The unique comparison at t=1 and its value at zero, followed by inverse bundle
   integration, give alpha. Mate pasting and diagonal-orientation compatibility prove
   its coefficient equation.
7. Compose inverse alpha with the smooth tensor map phi. Each factor is invertible and
   natural. Pull back bounded flat models and tensor with the locally free root line;
   the Tor interval shifts by -2d. Pull back finite strata to obtain constructibility.
8. At d=0 the gamma-normalization theorem identifies all factors with the graph-normalized
   etale sum adjunction, including its specified counit, proving both displayed equations.
9. Transport through exact comparison using its normalized tensorator, pullback square,
   open/proper site comparison and actual origin counit. Full faithfulness makes this
   independent of every chosen origin, and transports the trace and both coefficient maps.
10. Substitute the orientation and tensor-map coefficient equations to obtain
    S(gamma) followed by c equals lambda followed by gamma. The counit identity and
    adjunction bijectivity give all quotient cocycles. At the coefficient unit the root
    line is a sheaf, so source and target have cohomology only in degree -2d. The same
    comparison equations specialize to that unit and all its successive reductions.
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
  sorry

end AlgebraicGeometry.Etale.FiniteSmoothPurity
