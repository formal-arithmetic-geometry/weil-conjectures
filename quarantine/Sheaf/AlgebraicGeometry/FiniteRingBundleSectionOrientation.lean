/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.Targets.VectorBundlePurity
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import Sheaf.AlgebraicGeometry.VectorProjectiveCompletion
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.Paper.DegreeZeroDerivedMapGluing
import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import Sheaf.AlgebraicGeometry.ProperProjectionFormula

/-! # Finite-ring orientation along the zero section of a vector bundle

Source: main-20261015, sec-smooth-purity/sk-prop-sp-orientation,
orientation-charts proof Step 4, linear normalization and comparison to bundle purity.
(blueprint: lem-trf-finite-ring-bundle-section-orientation).

The local normalization is an equation on inverse orientations, using the actual
compact-support mate and the actual affine coordinate counit. It simultaneously specifies
all frame restrictions, including restrictions to overlaps, without choosing an orientation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

/-- Bundle affineness from the recorded geometry, used to synthesize compactifications.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
instance bundleSectionAffine (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    IsAffineHom (VectorBundleZeroSection.π S d M) :=
  (vectorIntegration_geometry S d M).1

/-- The bundle is of finite type locally, as recorded in its integration construction.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
instance bundleSectionFiniteType (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
  (vectorIntegration_geometry S d M).2.1

/-- The total space is Noetherian, including the empty and rank-zero cases.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
instance bundleSectionNoetherian (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    IsNoetherian (VectorBundleZeroSection.scheme S d M) :=
  (vectorIntegration_geometry S d M).2.2

/-- Every open of the Noetherian base is Noetherian; overlaps need not be affine.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
instance bundleSectionOpenNoetherian (S : Scheme.{u}) [IsNoetherian S] (V : S.Opens) :
    IsNoetherian V.toScheme :=
  letI : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  { toIsLocallyNoetherian := inferInstance
    toCompactSpace :=
      { isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ } }

/-- The actual dualizing object for the chosen bundle compact-support adjunction.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionOmega (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    DerivedCategoryModule A (VectorBundleZeroSection.scheme S d M) :=
  (rightDerivedUpperShriek (ModuleCat.{u + 1} A)
    (VectorBundleZeroSection.π S d M)).obj (ordinaryFiniteUnit A S)

/-- The object z^* omega_pi on the ordinary unbounded category of the base.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionObject (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] : DerivedCategoryModule A S :=
  (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).obj
    (bundleSectionOmega A S d M)

/-- Canonical z^* pi^* A_S(d)[2d] = A_S(d)[2d], using pi z = 1.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionCoefficientIso (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).obj
        (vectorIntegrationCoefficient A N hA S d M) ≅
      affineLinearBaseCoefficient A N hA S d :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (VectorBundleZeroSection.zero S d M) (VectorBundleZeroSection.π S d M)
    (VectorBundleZeroSection.zero_spec S d M).1).app _

/-- Inverse images around a commuting square of sections, with their canonical compositors.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionPullbackSquare (A : Type (u + 1)) [CommRing A]
    {X U S T : Scheme.{u}} (z : S ⟶ X) (w : T ⟶ U) (h : U ⟶ X) (v : T ⟶ S)
    (hw : w ≫ h = v ≫ z) (K : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A v).obj ((ordinaryFinitePullback A z).obj K) ≅
      (ordinaryFinitePullback A w).obj ((ordinaryFinitePullback A h).obj K) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v z).symm.app K ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w h (v ≫ z) hw.symm).app K

/-- The counit-preserving comparison on section objects: the canonical exceptional mate
of inverse compact-support exchange, followed by the constant-unit pullback comparison.
For the open and isomorphism squares below this is exactly the right-adjoint comparison.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U S T : Scheme.{u}} (p : X ⟶ S) (q : U ⟶ T)
    [HasCompactification p] [HasCompactification q] [QuasiCompact q]
    (h : U ⟶ X) (v : T ⟶ S) (sq : IsPullback h q p v)
    (z : S ⟶ X) (w : T ⟶ U) (hw : w ≫ h = v ≫ z) :
    (ordinaryFinitePullback A v).obj
        ((ordinaryFinitePullback A z).obj
          ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) p).obj
            (ordinaryFiniteUnit A S))) ⟶
      (ordinaryFinitePullback A w).obj
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) q).obj
          (ordinaryFiniteUnit A T)) :=
  (bundleSectionPullbackSquare A z w h v hw _).hom ≫
    (ordinaryFinitePullback A w).map
      ((rightDerivedUpperShriekBaseChangeMap A sq).app (ordinaryFiniteUnit A S) ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} A) q).map
          (ordinaryFiniteUnitPullback A v).hom)

/-- The zero section expressed in the actual inverse frame, by its Cartesian lifting property.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionChartZero (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d M V) :
    V.toScheme ⟶ affineTraceTower V.toScheme d :=
  (vectorIntegrationChart_isPullback S d M V e).lift
    (V.ι ≫ VectorBundleZeroSection.zero S d M) (𝟙 _)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f ↦ V.ι ≫ f) (VectorBundleZeroSection.zero_spec S d M).1).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))

/-- Canonical comparison from a restricted global section object to the frame section object.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionChartComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d M V) :=
  bundleSectionComparison A (VectorBundleZeroSection.π S d M)
    (affineTraceProjection V.toScheme d) (vectorIntegrationChart S d M V e) V.ι
    (vectorIntegrationChart_isPullback S d M V e) (VectorBundleZeroSection.zero S d M)
    (bundleSectionChartZero S d M V e)
    ((vectorIntegrationChart_isPullback S d M V e).lift_fst _ _ _)

/-- The actual affine adjunct alpha_p, not an arbitrary purity isomorphism.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionAffineAdjunct (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
    (affineTraceProjection T d)).homEquiv _ (ordinaryFiniteUnit A T)
      ((affineLinearCompactComparison N hN A hA T hT d).inv ≫
        affineTraceCounit A N hA t D T hT d)

/-- The coefficient identification along the zero section in a frame.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionChartCoefficient (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d M V) :
    (ordinaryFinitePullback A (bundleSectionChartZero S d M V e)).obj
        ((affineTraceRight A N hA V.toScheme d).obj (ordinaryFiniteUnit A V.toScheme)) ≅
      affineLinearBaseCoefficient A N hA V.toScheme d :=
  (ordinaryFinitePullback A (bundleSectionChartZero S d M V e)).mapIso
      (affineLinearCoefficientDescent A N hA t V.toScheme
        (affineTracePullbackInvertible N V.ι hS) d) ≪≫
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (bundleSectionChartZero S d M V e) (affineTraceProjection V.toScheme d)
      ((vectorIntegrationChart_isPullback S d M V e).lift_snd _ _ _)).app _

/-- Every affine frame has the specified inverse-affine-adjunct orientation. Using an
inverse equation avoids assuming in advance the invertibility that the theorem asserts.
Since every frame, not a selected cover, occurs, this also states agreement on overlaps
and under every invertible linear change of frames via the same restriction map.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def BundleSectionOrientationNormalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (o : bundleSectionObject A S d M ≅ affineLinearBaseCoefficient A N hA S d) : Prop :=
  ∀ (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (V : S.Opens) (_hV : IsAffine V.toScheme)
    (e : VectorBundleZeroSection.Trivialization S d M V),
    (ordinaryFinitePullback A V.ι).map o.inv ≫
        bundleSectionChartComparison A S d M V e =
      (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d).hom ≫
        (bundleSectionChartCoefficient N A hA t S hS d M V e).inv ≫
        (ordinaryFinitePullback A (bundleSectionChartZero S d M V e)).map
          (bundleSectionAffineAdjunct N hN A hA t D V.toScheme
            (affineTracePullbackInvertible N V.ι hS) d)

/-- The normalized local orientations glue uniquely, including all frame changes.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).

Proof: (1) bundle projective completion and Noetherian open restriction supply all geometric
hypotheses. (2) Conjugate the affine coordinate-tower adjunction through the unbounded
compact-support compositor. Its counit identifies its comparison at the unit with alpha_p,
so alpha_p is invertible. (3) Compose open extension/restriction adjunctions with the ambient
adjunctions. The resulting Hom chain defines exactly bundleSectionComparison; mate pasting
proves its composition law. (4) Affine-trace base change identifies restricted adjuncts,
even on non-affine intersections. (5) Linear trace invariance makes the two frame adjuncts
agree, without any determinant factor. (6) Shift source and target by -2d into the heart.
Degree-zero derived-map gluing gives a unique map and glues the inverse maps; uniqueness
makes both composites identities. (7) Induced frames prove bundle-isomorphism naturality.
(8) The rank-zero tower is the identity adjunction. Empty covers and zero coefficients are
included. (9) At the coefficient unit the canonical projection formula is the identity
under unitors; both signed symmetries have sign one. (10) Integration restricts to the same
coordinate traces, so inverse bundle purity has these frame restrictions and uniqueness
identifies it with the orientation. Annihilator changes use the finite Tate power maps.
-/
theorem finiteRingBundleSectionOrientation (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    ∃! o : bundleSectionObject A S d M ≅ affineLinearBaseCoefficient A N hA S d,
      BundleSectionOrientationNormalization N hN A hA S hS d M o := by
  sorry

/-- Preservation under a linear bundle isomorphism. The last hypothesis expresses linearity
in frames: every linear frame of M is carried to a linear frame of P. The two preceding
equations are its structural-map and zero-section equations, not extra geometric conditions.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).

Proof: compose a frame of the target with the bundle isomorphism. Counit-preserving
comparison and mate pasting identify the two local normalization equations. Uniqueness
in degree-zero gluing makes the two maps equal globally (node proof Step 7). -/
theorem finiteRingBundleSectionOrientation_naturality (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M P : S.Modules) [M.IsFiniteLocallyFreeOfRank d] [P.IsFiniteLocallyFreeOfRank d]
    (o : bundleSectionObject A S d M ≅ affineLinearBaseCoefficient A N hA S d)
    (o' : bundleSectionObject A S d P ≅ affineLinearBaseCoefficient A N hA S d)
    (_ho : BundleSectionOrientationNormalization N hN A hA S hS d M o)
    (_ho' : BundleSectionOrientationNormalization N hN A hA S hS d P o')
    (h : VectorBundleZeroSection.scheme S d M ≅ VectorBundleZeroSection.scheme S d P)
    (hp : h.hom ≫ VectorBundleZeroSection.π S d P = VectorBundleZeroSection.π S d M)
    (hz : VectorBundleZeroSection.zero S d M ≫ h.hom = VectorBundleZeroSection.zero S d P)
    (_hlin : ∀ (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d M V),
      ∃ e' : VectorBundleZeroSection.Trivialization S d P V,
        vectorIntegrationChart S d M V e ≫ h.hom = vectorIntegrationChart S d P V e') :
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.app
        (bundleSectionObject A S d P) ≫
      bundleSectionComparison A (VectorBundleZeroSection.π S d P)
        (VectorBundleZeroSection.π S d M) h.hom (𝟙 S)
        (IsPullback.of_horiz_isIso
          (CommSq.mk (hp.trans (Category.comp_id _).symm)))
        (VectorBundleZeroSection.zero S d P) (VectorBundleZeroSection.zero S d M)
        (hz.trans (Category.id_comp _).symm) ≫ o.hom = o'.hom := by
  sorry

/-- Canonical rank-zero comparison with the identity adjunction, under E = S.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionRankZeroComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S]
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank 0]
    (e : VectorBundleZeroSection.scheme S 0 M ≅ S)
    (hz : e.inv = VectorBundleZeroSection.zero S 0 M) :
    bundleSectionObject A S 0 M ⟶ ordinaryFiniteUnit A S :=
  letI : IsIso (VectorBundleZeroSection.zero S 0 M) := hz ▸ inferInstance
  (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.app _ ≫
    bundleSectionComparison A (VectorBundleZeroSection.π S 0 M) (𝟙 S)
      (VectorBundleZeroSection.zero S 0 M) (𝟙 S)
      (IsPullback.of_horiz_isIso
        (CommSq.mk ((VectorBundleZeroSection.zero_spec S 0 M).1.trans
          (Category.comp_id _).symm)))
      (VectorBundleZeroSection.zero S 0 M) (𝟙 S) rfl ≫
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app _ ≫
    ((conjugateIsoEquiv
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) (𝟙 S))
      (Adjunction.id)) (unboundedEtaleLowerShriekId A S).symm).hom.app _

/-- Identity normalization in rank zero, with the canonical geometric identification.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).

Proof: the rank-zero symmetric algebra is the structure algebra and augmentation is the
identity. Thus pi and z are inverse. The coordinate tower, counit and its adjunct are the
identity in dimension zero. The normalization on every frame and unique gluing identify
o with the displayed identity-adjunction comparison (node proof Step 8). -/
theorem finiteRingBundleSectionOrientation_rankZero (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank 0]
    (o : bundleSectionObject A S 0 M ≅ affineLinearBaseCoefficient A N hA S 0)
    (_ho : BundleSectionOrientationNormalization N hN A hA S hS 0 M o) :
    ∃ (e : VectorBundleZeroSection.scheme S 0 M ≅ S)
      (_hp : e.hom = VectorBundleZeroSection.π S 0 M)
      (hz : e.inv = VectorBundleZeroSection.zero S 0 M),
      o.hom = bundleSectionRankZeroComparison A S M e hz := by
  sorry

/-- The canonical tensor-unit identification pi^* A_S tensor A_E(d)[2d] = A_E(d)[2d].
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionPurityUnitIso (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S) ≅
      vectorIntegrationCoefficient A N hA S d M :=
  ((derivedTensor (ModuleCat.{u + 1} A) (VectorBundleZeroSection.scheme S d M)).mapIso
    (ordinaryFiniteUnitPullback A (VectorBundleZeroSection.π S d M))).app _ ≪≫
      derivedTensorLeftUnitor (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.scheme S d M) _

/-- The actual purity adjunct at the coefficient unit, with the specified projection map.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionPurityUnitMap (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (p : (vectorBundlePurityLower A S d M).obj
        (vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S)) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) S).obj (ordinaryFiniteUnit A S)).obj
        (vectorIntegrationSource A N hA S d M)) :
    vectorIntegrationCoefficient A N hA S d M ⟶ bundleSectionOmega A S d M :=
  (bundleSectionPurityUnitIso N A hA S d M).inv ≫
    (vectorBundlePurityAdjunction A S d M).homEquiv _ (ordinaryFiniteUnit A S)
      (p.hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) S).obj (ordinaryFiniteUnit A S)).map
          (vectorBundleIntegration N hN A hA S hS d M) ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) S (ordinaryFiniteUnit A S)).hom)

/-- Equality with inverse integration-normalized purity, written without inverse maps
whose invertibility would have to be assumed. The projection inverse p is characterized
by p.inv being the canonical projection map; the remaining equation is on o.inv.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def BundleSectionPurityCompatibility (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (o : bundleSectionObject A S d M ≅ affineLinearBaseCoefficient A N hA S d) : Prop :=
  ∃ p : (vectorBundlePurityLower A S d M).obj
        (vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S)) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) S).obj (ordinaryFiniteUnit A S)).obj
        (vectorIntegrationSource A N hA S d M),
    p.inv = vectorBundlePurityProjectionMap A N hA S d M (ordinaryFiniteUnit A S) ∧
    o.inv = (bundleSectionCoefficientIso A N hA S d M).inv ≫
      (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).map
        (bundleSectionPurityUnitMap N hN A hA S hS d M p)

/-- For valuation quotients the orientation is the restriction of inverse bundle purity.
The existing coefficient type denotes O_F / varpi_F^(n+1), so n ranges over all positive
quotient levels without excluding the first level. The equation uses inverse orientations
and therefore refers directly to the specified gamma, without choosing another isomorphism.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).

Proof: at the unit the proper projection map is the transpose of the counit and hence
identity under unitors. The open factor is likewise identity, and the two derived
symmetries have sign one. Thus gamma at the unit is the adjunct of t_pi. Its restriction
to every frame is alpha_p by the integration normalization and mate pasting. Inverting
and restricting by zero gives the prescribed frame orientation. Unique degree-zero gluing
identifies it with o. Any different annihilating power gives the same line by the canonical
roots-of-unity power comparisons (node proof Steps 9--10). -/
theorem finiteRingBundleSectionOrientation_valuation
    (ell : ℕ) [Fact ell.Prime] (F : Type u) [Field F] [Algebra (Padic ell) F]
    [FiniteDimensional (Padic ell) F] (n N : ℕ) (hN : 0 < N)
    (hA : (N : Scheme.finiteTateCoefficient ell F n) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (_hEll : IsUnit (ell : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (o : bundleSectionObject (Scheme.finiteTateCoefficient ell F n) S d M ≅
      affineLinearBaseCoefficient (Scheme.finiteTateCoefficient ell F n) N hA S d)
    (_ho : BundleSectionOrientationNormalization N hN
      (Scheme.finiteTateCoefficient ell F n) hA S hS d M o) :
    BundleSectionPurityCompatibility N hN
      (Scheme.finiteTateCoefficient ell F n) hA S hS d M o := by
  sorry

end AlgebraicGeometry.Etale
