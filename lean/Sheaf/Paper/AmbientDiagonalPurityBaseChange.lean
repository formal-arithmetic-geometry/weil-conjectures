/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.FiniteRingSectionDeformation
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Sheaf.AlgebraicGeometry.ShriekTensorComposition
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.SmoothPurity.TensorMateEtalePrecomp
import Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace
import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm
import Sheaf.Targets.VectorBundlePurity
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import WeilConjectures.Compactification.NagataCompactification

/-! # Ambient diagonal purity and normalized base change

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
finite-stage proof; sk-prop-sp-orientation; sk-prop-sp-purity-bc-factors
(blueprint: lem-trf-ambient-diagonal-purity-base-change).

All coefficient categories below are the ordinary unbounded small-etale categories.
The inverse orientation is characterized by the actual diagonal, normalized Rees
specialization, and the inverse of the Kummer-normalized vector-bundle adjoint.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale.AmbientDiagonalPurity

/-- The normalized transport of Tate lines, obtained by projecting the already normalized
finite-twist transport, whose roots and pure-tensor equations determine its maps.
Source: sk-thm-smooth-purity, finite Tate conventions
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def twistTransport (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) : OrdinaryFiniteTwistTransport A N hA :=
  { roots := (p1DecompositionTwistTransport A N hN hA).roots
    line := fun f hY ↦ (p1DecompositionTwistTransport A N hN hA).line f hY
      ((map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom) 1
    roots_normalization := (p1DecompositionTwistTransport A N hN hA).roots_normalization
    line_normalization := fun f hY ↦
      (p1DecompositionTwistTransport A N hN hA).line_normalization f hY
        ((map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom) }

/-- Restriction of self-base-change to the diagonal, with the canonical section compositor.
Source: sk-prop-sp-orientation, first factor of theta
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def diagonalRestriction (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (h : X ⟶ Y) [HasCompactification h] [QuasiCompact h] :
    dualizingComplex (ModuleCat.{u + 1} A) h ⟶
      sectionInvariant A (pullback.snd h h) (pullback.diagonal h) :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (pullback.diagonal h) (pullback.fst h h) (pullback.diagonal_fst h)).inv.app _ ≫
      (ordinaryFinitePullback A (pullback.diagonal h)).map
        (smoothDualizingBaseChangeMap A h h)

/-- The actual cone-to-bundle section comparison induced by an over-base cone comparison.
The equation on sections fixes its direction; later normalization records the canonical
symmetric-algebra comparison, not an unspecified line isomorphism.
Source: sk-prop-sp-orientation, normal-bundle identification
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def normalSectionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    (s : S ⟶ V) [IsClosedImmersion s] [FiniteRingSectionDeformation.Geometry d g s]
    (e : s.ker.normalCone ≅
      VectorBundleZeroSection.scheme S d (ConormalGradedAlgebra.piece s 1))
    (sq : IsPullback e.hom (Scheme.Hom.normalConeProj g s)
      (VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)) (𝟙 S))
    (hz : s.normalConeZeroSection ≫ e.hom =
      𝟙 S ≫ VectorBundleZeroSection.zero S d (ConormalGradedAlgebra.piece s 1)) :
    (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d
      (ConormalGradedAlgebra.piece s 1))).obj
        ((FiniteRingSectionDeformation.bundleRight A S d
          (ConormalGradedAlgebra.piece s 1)).obj (𝟙_ _)) ⟶
      sectionInvariant A (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection := by
  letI := (vectorIntegration_geometry S d (ConormalGradedAlgebra.piece s 1)).1
  letI := (vectorIntegration_geometry S d (ConormalGradedAlgebra.piece s 1)).2.1
  exact (affineLinearPullbackId A S).inv.app _ ≫
    NoetherianSectionSpecialization.sectionMap A
      (VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1))
      (Scheme.Hom.normalConeProj g s) (𝟙 S) e.hom sq
      (VectorBundleZeroSection.zero S d (ConormalGradedAlgebra.piece s 1))
      s.normalConeZeroSection hz

/-- The diagonal/deformation characterization of the inverse orientation. Kappa is
normalized at one; e factors the canonical associated-graded/symmetric-algebra comparison;
the section comparison is inverted as an actual map. Thus every orientation factor is fixed.
Source: sk-prop-sp-orientation and sk-thm-dnc, final formula
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def DiagonalNormalized (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) (h : X ⟶ Y)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h]
    [HasCompactification h]
    (θ : dualizingComplex (ModuleCat.{u + 1} A) h ≅
      affineLinearBaseCoefficient A N hA X d) : Prop := by
  letI := FiniteRingSectionDeformation.geometry d (pullback.snd h h)
    (pullback.diagonal h) (pullback.diagonal_snd h)
  exact ∃ κ : NoetherianSectionSpecialization.family A (pullback.snd h h)
      (pullback.diagonal h) ≅
        (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) X ↘ X)).obj
          (sectionInvariant A (pullback.snd h h) (pullback.diagonal h)),
    NoetherianSectionSpecialization.Normalized A (pullback.snd h h)
      (pullback.diagonal h) (pullback.diagonal_snd h) κ ∧
    ∃ e₀ : (pullback.diagonal h).ker.normalCone ≅
        PurityNormalBundle.normalCone (pullback.diagonal h),
      e₀.hom ≫ PurityNormalBundle.projection (pullback.diagonal h) =
        Scheme.Hom.purityNormalProjection (pullback.diagonal h) ∧
      (pullback.diagonal h).normalConeZeroSection ≫ e₀.hom =
        PurityNormalBundle.zeroSection (pullback.diagonal h) ∧
    ∃ sq : IsPullback
        (e₀ ≪≫ FiniteRingSectionDeformation.coneBundleIso d (pullback.snd h h)
          (pullback.diagonal h)).hom
        (Scheme.Hom.normalConeProj (pullback.snd h h) (pullback.diagonal h))
        (VectorBundleZeroSection.π X d (ConormalGradedAlgebra.piece (pullback.diagonal h) 1))
        (𝟙 X),
    ∃ hz : (pullback.diagonal h).normalConeZeroSection ≫
        (e₀ ≪≫ FiniteRingSectionDeformation.coneBundleIso d (pullback.snd h h)
          (pullback.diagonal h)).hom =
        𝟙 X ≫ VectorBundleZeroSection.zero X d
          (ConormalGradedAlgebra.piece (pullback.diagonal h) 1),
    ∃ c : (ordinaryFinitePullback A (VectorBundleZeroSection.zero X d
        (ConormalGradedAlgebra.piece (pullback.diagonal h) 1))).obj
          ((FiniteRingSectionDeformation.bundleRight A X d
            (ConormalGradedAlgebra.piece (pullback.diagonal h) 1)).obj (𝟙_ _)) ≅
        sectionInvariant A
          (Scheme.Hom.normalConeProj (pullback.snd h h) (pullback.diagonal h))
          (pullback.diagonal h).normalConeZeroSection,
      c.hom = normalSectionComparison A d (pullback.snd h h) (pullback.diagonal h)
        (e₀ ≪≫ FiniteRingSectionDeformation.coneBundleIso d (pullback.snd h h)
          (pullback.diagonal h)) sq hz ∧
      θ.hom = diagonalRestriction A h ≫
        NoetherianSectionSpecialization.specialization A (pullback.snd h h)
          (pullback.diagonal h) κ ≫ c.inv ≫
        (FiniteRingSectionDeformation.bundleOrientation N hN A hA X hX d
          (ConormalGradedAlgebra.piece (pullback.diagonal h) 1)).hom

/-- The diagonal formula determines the inverse orientation uniquely.
Source: sk-prop-sp-orientation, diagonal formula and sk-thm-dnc, Gluing
(blueprint: lem-trf-ambient-diagonal-purity-base-change).
Proof: apply exceptional self-base-change to the coefficient unit and restrict to the
diagonal. Its conormal is locally free of rank d. The finite-ring section-deformation
lemma gives the unique comparison normalized at one and its invertible zero restriction.
Identify the associated graded with the symmetric algebra of the conormal, and restrict
the inverse Kummer-normalized bundle adjoint to zero. These four factors are invertible.
The resulting map is independent of the cone presentation: an isomorphism over the base
identifies the same compact-support adjunction and its integration counit. Equivalently,
compute on smooth coordinates and apply sheaf-Hom gluing after shifting to degree zero.
Thus the displayed characterization determines one map, including d=0 and empty X. -/
theorem existsUnique_orientation (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) (h : X ⟶ Y)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h]
    [HasCompactification h] :
    ∃! θ : dualizingComplex (ModuleCat.{u + 1} A) h ≅
        affineLinearBaseCoefficient A N hA X d,
      DiagonalNormalized N hN A hA hX d h θ := by
  sorry

/-- The inverse of the uniquely characterized diagonal orientation. The existence theorem
specifies the object up to equality; no arbitrary orientation is chosen.
Source: sk-prop-sp-orientation, theta (blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
def inverseOrientation (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) (h : X ⟶ Y)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h]
    [HasCompactification h] :
    dualizingComplex (ModuleCat.{u + 1} A) h ≅ affineLinearBaseCoefficient A N hA X d :=
  Classical.choose (existsUnique_orientation N hN A hA hX d h)

/-- Pullback followed by the ordered shifted Tate tensor, namely h* M(d)[2d].
Source: sk-thm-smooth-purity, gamma source
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[implicit_reducible] def twistedPullback (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (d : ℕ) (h : X ⟶ Y) :
    DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X :=
  ordinaryFinitePullback A h ⋙
    derivedTensorRight (ModuleCat.{u + 1} A) X (affineLinearBaseCoefficient A N hA X d)

/-- The specified purity map: tensor with the diagonal orientation and then the
inverse-projection/counit transpose. Source: sk-thm-smooth-purity, finite-stage gamma
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def gamma (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) (h : X ⟶ Y)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h]
    [HasCompactification h] (M : DerivedCategoryModule A Y) :
    (twistedPullback A N hA d h).obj M ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} A) h).obj M :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((ordinaryFinitePullback A h).obj M)).map
      (inverseOrientation N hN A hA hX d h).inv ≫
    smoothTensorDualityMap (ModuleCat.{u + 1} A) h
      (isIso_projectionMap_of_finite A h) M

/-- The adjoint smooth trace, with its actual counit normalization.
Source: sk-thm-smooth-purity, adjunct trace
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def trace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) (h : X ⟶ Y)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h]
    [HasCompactification h] (M : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).obj
      ((twistedPullback A N hA d h).obj M) ⟶ M :=
  ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) h).homEquiv _ M).symm
    (gamma N hN A hA hX d h M)

/-- The canonical identification of the sources in the purity base-change square.
Source: sk-prop-sp-purity-bc-factors, tensor and twist identifications
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def gammaBaseChangeIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    {X Y Y' : Scheme.{u}} (d : ℕ) (h : X ⟶ Y) (v : Y' ⟶ Y)
    (hX : IsUnit (N : Γ(X, ⊤))) (M : DerivedCategoryModule A Y) :
    (ordinaryFinitePullback A (pullback.fst h v)).obj
        ((twistedPullback A N hA d h).obj M) ≅
      (twistedPullback A N hA d (pullback.snd h v)).obj
        ((ordinaryFinitePullback A v).obj M) :=
  leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (pullback.fst h v)
      ((ordinaryFinitePullback A h).obj M) (affineLinearBaseCoefficient A N hA X d) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) (pullback h v)).mapIso
      (smoothSquarePullbackIso A h v M)).app _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) (pullback h v)).obj
      ((ordinaryFinitePullback A (pullback.snd h v)).obj
        ((ordinaryFinitePullback A v).obj M))).mapIso
      (vectorIntegrationBaseCoefficientPullback A N hA (twistTransport A N hN hA)
        (pullback.fst h v) hX d)

/-- The exceptional tensor map in the derived-bifunctor presentation. This is precisely
inverse projection followed by the compact-support counit, transposed along its adjunction.
Source: sk-thm-smooth-purity, exceptional tensor pairing
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def exceptionalTensorMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (h : X ⟶ Y) [HasCompactification h]
    (M L : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) h).obj M)).obj
        ((ordinaryFinitePullback A h).obj L) ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} A) h).obj
        (((derivedTensor (ModuleCat.{u + 1} A) Y).obj M).obj L) := by
  letI := isIso_projectionMap_of_finite A h
  exact (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) h).homEquiv _ _
    (((asIso (projectionMap (ModuleCat.{u + 1} A) h)).app
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) h).obj M)).inv.app L ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) h).counit.app M)).app L)

/-- The exceptional internal-Hom map with its evaluation normalization. The pairing uses
exceptional tensor followed by evaluation, and is transposed along tensor-Hom.
Source: sk-thm-smooth-purity, exceptional internal-Hom comparison
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def exceptionalHomComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (h : X ⟶ Y) [HasCompactification h]
    (L M : DerivedCategoryModule A Y) :
    (rightDerivedUpperShriek (ModuleCat.{u + 1} A) h).obj
        (((derivedHom (ModuleCat.{u + 1} A) Y).obj (Opposite.op L)).obj M) ⟶
      ((derivedHom (ModuleCat.{u + 1} A) X).obj
        (Opposite.op ((ordinaryFinitePullback A h).obj L))).obj
          ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) h).obj M) :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
    ((ordinaryFinitePullback A h).obj L)).homEquiv _ _
      ((((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app
        ((ordinaryFinitePullback A h).obj L)).app _) ≫
        exceptionalTensorMap A h
          (((derivedHom (ModuleCat.{u + 1} A) Y).obj (Opposite.op L)).obj M) L ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} A) h).map
          ((((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app
            (((derivedHom (ModuleCat.{u + 1} A) Y).obj (Opposite.op L)).obj M)).app L) ≫
            (derivedTensorHomAdjunction (ModuleCat.{u + 1} A) L).counit.app M))

/-- Canonical multiplication of the ordered shifted Tate tensors, using only tensor
associativity and the coefficient unit. The recursion includes the empty tensor.
Source: sk-thm-smooth-purity, composition and even shifts
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def coefficientProduct (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (X : Scheme.{u}) (a : ℕ) : ∀ b : ℕ,
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      (affineLinearBaseCoefficient A N hA X a)).obj
        (affineLinearBaseCoefficient A N hA X b) ≅
      affineLinearBaseCoefficient A N hA X (a + b)
  | 0 => ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      (affineLinearBaseCoefficient A N hA X a)).mapIso
        (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X) ≪≫
      derivedTensorRightUnitor (ModuleCat.{u + 1} A) X _
  | b + 1 => (derivedTensorAssociator (ModuleCat.{u + 1} A) X
      (affineLinearBaseCoefficient A N hA X a)
      (affineLinearBaseCoefficient A N hA X b)
      ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)).symm ≪≫
        (derivedTensorRight (ModuleCat.{u + 1} A) X
          ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)).mapIso
            (coefficientProduct A N hA X a b)

/-- Canonical coefficient identification for a smooth composite. The base coordinates
precede the fibre tensor in this presentation; the total shift is even.
Source: sk-thm-smooth-purity, composition formula
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def coefficientCompositionIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (d e : ℕ) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA Y e))).obj
        (affineLinearBaseCoefficient A N hA X d) ≅
      affineLinearBaseCoefficient A N hA X (d + e) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
    (vectorIntegrationBaseCoefficientPullback A N hA (twistTransport A N hN hA)
      f hY e)).app _ ≪≫ coefficientProduct A N hA X e d ≪≫
    eqToIso (congrArg (affineLinearBaseCoefficient A N hA X) (Nat.add_comm e d))

/-- The canonical identification from iterated twisted pullback to the composite one.
Source: sk-thm-smooth-purity, composition formula
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def gammaCompositionIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hY : IsUnit (N : Γ(Y, ⊤))) (d e : ℕ) (M : DerivedCategoryModule A Z) :
    (twistedPullback A N hA d f).obj ((twistedPullback A N hA e g).obj M) ≅
      (twistedPullback A N hA (d + e) (f ≫ g)).obj M :=
  (derivedTensorRight (ModuleCat.{u + 1} A) X
    (affineLinearBaseCoefficient A N hA X d)).mapIso
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f
        ((ordinaryFinitePullback A g).obj M) (affineLinearBaseCoefficient A N hA Y e)) ≪≫
    derivedTensorAssociator (ModuleCat.{u + 1} A) X
      ((ordinaryFinitePullback A f).obj ((ordinaryFinitePullback A g).obj M))
      ((ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA Y e))
      (affineLinearBaseCoefficient A N hA X d) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((ordinaryFinitePullback A f).obj ((ordinaryFinitePullback A g).obj M))).mapIso
        (coefficientCompositionIso N hN A hA f hY d e) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g (f ≫ g) rfl).symm.app M)).app _

/-- Exceptional transitivity is the unique right-adjoint comparison preserving the
composite compact-support counit, using the published unbounded tower comparison.
Source: sk-thm-smooth-purity, q_(g,f)
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def exceptionalCompositionIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)] :
    rightDerivedUpperShriek (ModuleCat.{u + 1} A) (f ≫ g) ≅
      rightDerivedUpperShriek (ModuleCat.{u + 1} A) g ⋙
        rightDerivedUpperShriek (ModuleCat.{u + 1} A) f :=
  Adjunction.rightAdjointUniq
    ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) (f ≫ g)).ofNatIsoLeft
      (unboundedEtaleLowerShriekCompIso A f g).symm)
    ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).comp
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) g))

/-- Remove the zero-fold twist, including the degree-zero coefficient-unit comparison.
Source: sk-thm-smooth-purity, dimension-zero normalization
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def zeroTwistIso (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (h : X ⟶ Y) (M : DerivedCategoryModule A Y) :
    (twistedPullback A N hA 0 h).obj M ≅ (ordinaryFinitePullback A h).obj M :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((ordinaryFinitePullback A h).obj M)).mapIso
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X) ≪≫
    derivedTensorRightUnitor (ModuleCat.{u + 1} A) X _

/-- All conclusions at one annihilating invertible modulus. Invertibility and naturality
range over all unbounded inputs. Base change uses the actual counit mate, including
its orientation and trace specializations. Composition uses the actual adjoint comparison.
Source: sk-thm-smooth-purity, finite-stage proof and base-change factors
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def Conclusions (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) (h : X ⟶ Y)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h]
    [HasCompactification h] : Prop :=
  DiagonalNormalized N hN A hA hX d h (inverseOrientation N hN A hA hX d h) ∧
  (∀ M : DerivedCategoryModule A Y, IsIso (gamma N hN A hA hX d h M)) ∧
  (∀ (M M' : DerivedCategoryModule A Y) (k : M ⟶ M'),
    (twistedPullback A N hA d h).map k ≫ gamma N hN A hA hX d h M' =
      gamma N hN A hA hX d h M ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} A) h).map k) ∧
  (∀ (L M : DerivedCategoryModule A Y), IsIso (exceptionalHomComparison A h L M)) ∧
  (∀ (Y' : Scheme.{u}) [IsNoetherian Y']
      (_hExcellent : ∀ U : Y'.affineOpens, IsExcellent Γ(Y', U.1)) (v : Y' ⟶ Y),
    ∀ [IsNoetherian (pullback h v)] (hX' : IsUnit (N : Γ(pullback h v, ⊤))),
      (ordinaryFinitePullback A (pullback.fst h v)).map
          (inverseOrientation N hN A hA hX d h).inv ≫
        smoothDualizingBaseChangeMap A h v =
      (vectorIntegrationBaseCoefficientPullback A N hA (twistTransport A N hN hA)
        (pullback.fst h v) hX d).hom ≫
          (inverseOrientation N hN A hA hX' d (pullback.snd h v)).inv ∧
      ∀ M : DerivedCategoryModule A Y,
        (ordinaryFinitePullback A (pullback.fst h v)).map
            (gamma N hN A hA hX d h M) ≫ smoothExceptionalBaseChangeMap A h v M =
          (gammaBaseChangeIso N hN A hA d h v hX M).hom ≫
            gamma N hN A hA hX' d (pullback.snd h v)
              ((ordinaryFinitePullback A v).obj M) ∧
        (ordinaryFinitePullback A v).map (trace N hN A hA hX d h M) =
          (rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback h v)).app
              ((twistedPullback A N hA d h).obj M) ≫
            (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd h v)).map
              (gammaBaseChangeIso N hN A hA d h v hX M).hom ≫
            trace N hN A hA hX' d (pullback.snd h v)
              ((ordinaryFinitePullback A v).obj M)) ∧
  (∀ (Z : Scheme.{u}) [IsNoetherian Z]
      (_hExcellent : ∀ U : Z.affineOpens, IsExcellent Γ(Z, U.1))
      (g : Y ⟶ Z) [IsSeparated g] [QuasiCompact g] [HasCompactification g]
      [HasCompactification (h ≫ g)] (e : ℕ) [SmoothOfRelativeDimension e g]
      (hY : IsUnit (N : Γ(Y, ⊤))) (M : DerivedCategoryModule A Z),
    (gammaCompositionIso N hN A hA h g hY d e M).hom ≫
        gamma N hN A hA hX (d + e) (h ≫ g) M =
      gamma N hN A hA hX d h ((twistedPullback A N hA e g).obj M) ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} A) h).map
          (gamma N hN A hA hY e g M) ≫
        (exceptionalCompositionIso A h g).inv.app M) ∧
  (∀ (Z : Scheme.{u}) [IsNoetherian Z]
      (_hExcellent : ∀ U : Z.affineOpens, IsExcellent Γ(Z, U.1))
      (g : Y ⟶ Z) [IsSeparated g] [QuasiCompact g] [HasCompactification g]
      [HasCompactification (h ≫ g)] (e : ℕ) [SmoothOfRelativeDimension e g]
      (hY : IsUnit (N : Γ(Y, ⊤))),
    (coefficientCompositionIso N hN A hA h hY d e).hom ≫
        (inverseOrientation N hN A hA hX (d + e) (h ≫ g)).inv =
      gamma N hN A hA hX d h (affineLinearBaseCoefficient A N hA Y e) ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} A) h).map
          (inverseOrientation N hN A hA hY e g).inv ≫
        (exceptionalCompositionIso A h g).inv.app (𝟙_ _))

/-- The finite coefficient ring of the recorded trace-formula conventions, in the
ordinary-etale coefficient universe. The level n+1 ranges over exactly all positive levels.
Source: def-trf-coefficient-conventions
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
abbrev Coefficient (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) : Type (u + 1) :=
  ULift.{u + 1, u} (Padic.coefficientExtensionRing ell E (n + 1))

/-- Finiteness is supplied by the recorded finite coefficient theorem.
Source: finite-level conventions (blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
instance coefficientFinite (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    Finite (Coefficient ell E n) :=
  letI := Padic.finite_coefficientExtensionRing ell E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  inferInstance

set_option linter.defProp false in
/-- Invertibility of an annihilating prime power after pullback. This is transport of
IsUnit along the structural ring map, with the natural-number cast made explicit.
Source: ambient hypotheses (blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
def invertiblePower (ell m : ℕ) {X Y : Scheme.{u}} (h : X ⟶ Y)
    (hY : IsUnit (ell : Γ(Y, ⊤))) : IsUnit ((ell ^ m : ℕ) : Γ(X, ⊤)) :=
  (map_natCast h.appTop.hom (ell ^ m)) ▸
    (((Nat.cast_pow (α := Γ(Y, ⊤)) ell m).symm ▸ hY.pow m).map h.appTop.hom)

/-- Independence of the annihilating exponent, with the actual power map on roots and
its scalar-extension map on pure tensors. Positive powers are its tensor powers; zero is
the identity, and negative powers are determined by evaluation.
Source: finite Tate conventions, Stacks 03PK and 03Q1
(blueprint: lem-trf-ambient-diagonal-purity-base-change). -/
@[irreducible] def ExponentIndependent (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) : Prop :=
  ∀ (N' : ℕ), 0 < N' → ∀ (_hdiv : N ∣ N') (hA' : (N' : A) = 0),
    IsUnit (N' : Γ(S, ⊤)) →
    ∃ (q : S.rootsOfUnitySheaf N' ⟶ S.rootsOfUnitySheaf N)
      (t : ∀ a : ℤ, Scheme.finiteEtaleTateSheaf A N' S hA' a ≅
        Scheme.finiteEtaleTateSheaf A N S hA a),
      q ≫ kernel.ι (N • 𝟙 S.gmSheaf) = (N' / N) • kernel.ι (N' • 𝟙 S.gmSheaf) ∧
      (∀ (W : S.Etaleᵒᵖ) (a : A) (z : (S.rootsOfUnitySheaf N').obj.obj W),
        (t 1).hom.hom.app W (Scheme.finiteEtaleTateOneGenerator A N' S hA' W a z) =
          Scheme.finiteEtaleTateOneGenerator A N S hA W a (q.hom.app W z)) ∧
      t 0 = Iso.refl _ ∧
      (∀ k : ℕ, t (.ofNat (k + 2)) = tensorIso (t (.ofNat (k + 1))) (t 1)) ∧
      (∀ k : ℕ,
        tensorHom (t (.ofNat (k + 1))).hom (t (.negSucc k)).hom ≫
            (ihom.ev (Scheme.finiteEtaleTateSheaf A N S hA (.ofNat (k + 1)))).app
              (Scheme.finiteEtaleTateSheaf A N S hA 0) =
          (ihom.ev (Scheme.finiteEtaleTateSheaf A N' S hA' (.ofNat (k + 1)))).app
            (Scheme.finiteEtaleTateSheaf A N' S hA' 0))

/-- Every positive finite coefficient level has a positive annihilating prime power.
Source: finite-stage coefficient conventions
(blueprint: lem-trf-ambient-diagonal-purity-base-change).
Proof: in O_E the principal ideal generated by ell is a positive power of the maximal
ideal, times a unit, since E/Q_ell is finite. Thus a sufficiently large power of ell
belongs to (varpi^(n+1)), so its image in the specified quotient, and in its universe
lift, is zero. This supplies auxiliary choices of m, rather than a hypothesis on A. -/
theorem coefficient_annihilator (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ((ell ^ m : ℕ) : Coefficient ell E n) = 0 := by
  sorry

/-- Ambient smooth purity with the specified diagonal normalization, unbounded tensor
mate, orientation/tensor/trace base-change equations, composition, and evaluation-normalized
exceptional internal Hom. The modulus is any positive annihilating prime power; its
existence is coefficient_annihilator. No restriction is imposed on any derived input.
Source: sk-thm-smooth-purity, finite-stage proof; sk-prop-sp-orientation;
sk-prop-sp-purity-bc-factors (blueprint: lem-trf-ambient-diagonal-purity-base-change).
Proof:
1. Finite Tate sheaves are rank-one locally free and their normalized power maps identify
all annihilating exponents. Smooth finite-type permanence gives Noetherian sources and
self-products; Nagata supplies all compactifications. The ambient unbounded adjoints apply.
2. Self-base-change restricted along the diagonal gives diagonalRestriction. Apply the
finite-ring section-deformation theorem, identify the regular normal cone with the
symmetric-algebra bundle of I/I^2, and restrict inverse bundle purity to zero. This is
exactly DiagonalNormalized and the chosen inverseOrientation, not an unspecified line.
3. Smooth tensor duality makes the inverse-projection/counit transpose invertible for
all M. Tensoring with the orientation gives gamma; functoriality gives naturality.
4. Smooth exceptional base change is the transpose of inverse compact-support exchange
followed by the pulled-back counit. Its tensor compatibility is equality of these maps.
5. Mate pasting identifies the diagonal factors after base change. Uniqueness of the
comparison normalized at one identifies the deformation factors, including nonflat bases.
6. Trivialize the bundle. The affine-space integration counit commutes with base change;
shift to degree zero and glue sheaf maps to identify bundle factors globally. Substitute
in Step 4, then take adjuncts to obtain the trace equation.
7. In smooth coordinates the section normalization is the standard one. Translation
invariance of the ambient affine-space trace identifies the centred and uncentred charts.
8. Transpose inverse projection and the composite counit to obtain tensor composition.
9. Compatible smooth charts give the same ordered affine coordinate tower. Its counit
is the successive affine-line counit, proving orientation composition locally. Shifted
rank-one sheaf-Hom gluing gives global equality and hence gamma composition. Even shifts
introduce no sign. Taking adjuncts proves the companion trace-composition statement.
10. Rank zero gives identity deformation and bundle factors; the compact-support-to-sum
comparison identifies the adjunction with etale sum/evaluation. This is the companion
etale normalization below. The hypotheses include all separably closed field extensions
and geometric fibres of excellent traits; no finite-type condition is imposed on v.
11. For every test T, apply compact-support adjunction, tensor-Hom adjunction, unbounded
projection, compact-support adjunction, and tensor-Hom adjunction. Yoneda proves that
exceptionalHomComparison is invertible, without dualizability of L.
12. Apply these Hom bijections to the identity at h^times RHom(L,M). The resulting pairing
is exceptional tensor followed by evaluation, exactly the formula in its definition. -/
theorem ambientDiagonalPurityBaseChange (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n m : ℕ) (hm : 0 < m) (hA : ((ell ^ m : ℕ) : Coefficient ell E n) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (_hExcellent : ∀ U : Y.affineOpens, IsExcellent Γ(Y, U.1))
    (hEll : IsUnit (ell : Γ(Y, ⊤))) (d : ℕ) (h : X ⟶ Y)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h]
    [HasCompactification h] :
    Conclusions (ell ^ m) (pow_pos (Fact.out : ell.Prime).pos m)
      (Coefficient ell E n) hA (invertiblePower ell m h hEll) d h ∧
    ∀ S : Scheme.{u}, IsUnit (ell : Γ(S, ⊤)) →
      ExponentIndependent (Coefficient ell E n) (ell ^ m) hA S := by
  sorry

/-- Adjoint traces compose through the actual unbounded compact-support tower map.
Source: sk-thm-smooth-purity, composition Steps 8--9
(blueprint: lem-trf-ambient-diagonal-purity-base-change).
Proof: apply the composite compact-support adjunction to the gamma-composition equality.
Its counit is epsilon_g composed with Rg_! epsilon_f. The two sides become the displayed
successive trace composite, with inverse source and tower comparisons inserted. -/
theorem trace_composition (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (hX : IsUnit (N : Γ(X, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤)))
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [SmoothOfRelativeDimension d f] [IsSeparated f] [QuasiCompact f]
    [SmoothOfRelativeDimension e g] [IsSeparated g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (M : DerivedCategoryModule A Z) :
    trace N hN A hA hX (d + e) (f ≫ g) M =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map
          (gammaCompositionIso N hN A hA f g hY d e M).inv ≫
        (unboundedEtaleLowerShriekCompIso A f g).inv.app _ ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
          (trace N hN A hA hX d f ((twistedPullback A N hA e g).obj M)) ≫
        trace N hN A hA hY e g M := by
  sorry

/-- In relative dimension zero the actual trace is the degreewise etale sum/evaluation
counit, under the normalized compact-support and exact-pullback comparisons.
Source: sk-thm-smooth-purity, rank-zero paragraph
(blueprint: lem-trf-ambient-diagonal-purity-base-change).
Proof: the diagonal section and rank-zero normal-bundle factors are identities. The
normalized compact-support comparison preserves the sum counit. The tensor mate with
the zero-fold coefficient tensor is its right-adjoint comparison; its adjunct is the
sum/evaluation counit in this formula. This also identifies the orientation at A with
the etale adjunction unit normalization. -/
theorem etale_trace_normalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : IsUnit (N : Γ(X, ⊤))) (h : X ⟶ Y)
    [SmoothOfRelativeDimension 0 h] [Etale h] [IsSeparated h] [QuasiCompact h]
    [HasCompactification h] (ν : EtaleCompactSupportNormalization A)
    (M : DerivedCategoryModule A Y) :
    trace N hN A hA hX 0 h M =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).map (zeroTwistIso A N hA h M).hom ≫
        (ν.comparison h (HasCompactification.compactification h)).hom.app _ ≫
        (etaleLowerShriek (ModuleCat.{u + 1} A) h inferInstance).mapDerivedCategory.map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).hom.app M) ≫
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
          h inferInstance).counit.app M := by
  sorry

end AlgebraicGeometry.Etale.AmbientDiagonalPurity
