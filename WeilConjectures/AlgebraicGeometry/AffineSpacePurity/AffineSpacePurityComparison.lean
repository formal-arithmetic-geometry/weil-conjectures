/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityComparison
public import WeilConjectures.AlgebraicGeometry.SfAffineChartPresentation.PurityAffineChartBounds
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.GeneralFiniteAffineLinePurity.Fixed.GeneralFiniteAffineLinePurityComparison
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnitConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImageCurrent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed

/-! # The ordered affine-space purity comparison

Source: blueprint sec-smooth-purity/sk-prop-an/def-pur-affine-space-comparison.md
(blueprint: def-pur-affine-space-comparison).
The standard iterated-affine-line model fixes the coordinate order and makes X_0=Y literal.
The source is the pullback followed by the finite Tate tensor power on X_d itself.
The displayed I_d is constructed from canonical pullback composition, the canonical
tensor comparison, and the finite Tate-line pullback. Each successor adds the last
coordinate and applies the recorded affine-line comparison, with no choice of orientation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v w v₁ w₁
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineSpacePurity
open AffineLinePurity VectorIntegrationSite

/-- Fixed-scalar derived category, with its module-category parameters cached.
Source: finite derived category convention (blueprint: def-pur-affine-space-comparison). -/
abbrev C (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- The recorded bounded-below category in fixed-scalar coordinates.
Source: etale-origin domain (blueprint: def-pur-affine-space-comparison). -/
abbrev Plus (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- Cached form of the existing bounded-below predicate.
Source: origin applicability (blueprint: def-pur-affine-space-comparison). -/
abbrev boundedBelow (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) (K : C A T) : Prop :=
  DerivedCategory.TStructure.t.plus K

/-- Cached form of the existing ordinary finite-Tor constructibility predicate.
Source: constructible domain (blueprint: def-pur-affine-space-comparison). -/
abbrev etaleFiniteTor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K : Etale.DerivedCategoryModule A T) : Prop :=
  Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T K

/-- Ordered iteration of a given source operation, with literal identity at zero.
Source: ordered tensor-power construction (blueprint: def-pur-affine-space-comparison). -/
def action {C : Type v} [Category.{w} C] (F : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | d + 1 => action F d ⋙ F

/-- Iterate the specified one-factor comparison without choosing any other maps.
Source: iterated tensor comparison (blueprint: def-pur-affine-space-comparison). -/
def actionPullbackIso {C : Type v} [Category.{w} C]
    {C' : Type v₁} [Category.{w₁} C']
    (F : C ⥤ C) (G : C' ⥤ C') (H : C ⥤ C')
    (e : ∀ M : C, H.obj (F.obj M) ≅ G.obj (H.obj M)) (K : C) :
    (d : ℕ) → H.obj ((action F d).obj K) ≅ (action G d).obj (H.obj K)
  | 0 => Iso.refl _
  | d + 1 => e ((action F d).obj K) ≪≫ G.mapIso (actionPullbackIso F G H e K d)

/-- Fixed-scalar tensor, cached before coefficient specialization.
Source: finite-level derived tensor (blueprint: def-pur-affine-space-comparison). -/
@[implicit_reducible]
def tensor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  derivedTensor (ModuleCat.{u + 1} A) T

/-- Fixed-scalar exact inverse image, cached before coefficient specialization.
Source: finite-level derived pullback (blueprint: def-pur-affine-space-comparison). -/
@[implicit_reducible]
def inverseImage (A : Type (u + 1)) [CommRing A]
    {X T : Scheme.{u}} (f : X ⟶ T) :=
  (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor

/-- Tensor two given isomorphisms using the recorded derived bifunctor.
Source: tensor reassociation (blueprint: def-pur-affine-space-comparison). -/
def tensorIso (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {M M' N N' : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))}
    (e : M ≅ M') (e' : N ≅ N') :
    ((tensor A T).obj M).obj N ≅ ((tensor A T).obj M').obj N' :=
  ((tensor A T).mapIso e).app N ≪≫ ((tensor A T).obj M').mapIso e'

/-- The canonical ambient tensor comparison, cached in fixed-scalar coordinates.
Source: finite tensor comparison (blueprint: def-pur-affine-space-comparison). -/
def inverseImageTensorIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T : Scheme.{u}} (f : X ⟶ T)
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    (inverseImage A f).obj (((tensor A T).obj M).obj N) ≅
      ((tensor A X).obj ((inverseImage A f).obj M)).obj ((inverseImage A f).obj N) :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f M N

/-- The canonical pullback compositor in cached finite-scalar coordinates.
Source: exact pullback composition (blueprint: def-pur-affine-space-comparison). -/
def inverseImageComp (A : Type (u + 1)) [CommRing A]
    {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S) :
    inverseImage A (f ≫ g) ≅ inverseImage A g ⋙ inverseImage A f :=
  leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g

/-- The canonical identity-pullback normalization in the same coordinates.
Source: dimension-zero convention (blueprint: def-pur-affine-space-comparison). -/
def inverseImageId (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    inverseImage A (𝟙 T) ≅ 𝟭 _ :=
  leftDerivedUpperStarId (ModuleCat.{u + 1} A) T

/-- Canonical reordering of a total pullback and its last shifted-line tensor factor.
All category instances are fixed before specializing the finite purity coefficient.
Source: I_d tensor calculation (blueprint: def-pur-affine-space-comparison). -/
def tensorReassociation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S)
    (W : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (W' C : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (eW : (inverseImage A f).obj W ≅ W') (eC : W' ≅ C)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
    (d : ℕ) :
    ((tensor A X).obj
      ((action ((tensor A X).flip.obj W') d).obj
        ((inverseImage A (f ≫ g)).obj K))).obj W' ≅
    ((tensor A X).obj ((inverseImage A f).obj
      ((action ((tensor A T).flip.obj W) d).obj ((inverseImage A g).obj K)))).obj C :=
  tensorIso A X
    ((action ((tensor A X).flip.obj W') d).mapIso ((inverseImageComp A f g).app K) ≪≫
      (actionPullbackIso ((tensor A T).flip.obj W) ((tensor A X).flip.obj W')
        (inverseImage A f)
        (fun M => inverseImageTensorIso A f M W ≪≫ tensorIso A X (Iso.refl _) eW)
        ((inverseImage A g).obj K) d).symm) eC

/-- Canonical identity-pullback normalization for the first line.
Source: I_0 and p_0=id (blueprint: def-pur-affine-space-comparison). -/
def tensorZeroReassociation (A : Type (u + 1)) [CommRing A]
    {X T : Scheme.{u}} (f : X ⟶ T)
    (W C : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (e : W ≅ C)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    ((tensor A X).obj ((inverseImage A (f ≫ 𝟙 T)).obj K)).obj W ≅
      ((tensor A X).obj ((inverseImage A f).obj K)).obj C :=
  tensorIso A X ((inverseImageComp A f (𝟙 T)).app K ≪≫
    (inverseImage A f).mapIso ((inverseImageId A T).app K)) e

/-- Fixed-scalar coordinates for the recorded finite pro-etale derived category.
Source: finite purity conventions (blueprint: def-pur-affine-space-comparison). -/
abbrev D (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) := C (Ring P) T

/-- An explicit annihilating exponent, valid at every positive coefficient level.
Source: the choice a>=1 in the finite Tate-line paragraph
(blueprint: def-pur-affine-space-comparison).
Proof: ell belongs to the maximal ideal (varpi) of O_E. Its level-th power belongs to
(varpi^level), so ell^(level+1) is zero in the quotient and its ULift. The zero-based Tate
index is level-1 and (level-1)+1=level by positivity. No e-divides-level assumption is used. -/
theorem annihilates (P : WeilConjectures.PurityFiniteSetting.{u}) :
    ((P.coefficients.l ^ (P.level + 1) : ℕ) : Ring P) = 0 := by
  apply (ringEquiv P).injective
  rw [map_natCast, map_zero, Nat.cast_pow, pow_succ]
  have h : (P.coefficients.l : P.Coefficient) ^ P.level = 0 := by
    simpa only [WeilConjectures.PurityFiniteSetting.diagonalExponent, Nat.cast_pow] using
      P.diagonalExponent_annihilates
  rw [h, zero_mul]

/-- The last-coordinate affine-line projection in the existing iterated-affine-space model.
Source: q_r in the ordered-composite paragraph (blueprint: def-pur-affine-space-comparison). -/
abbrev lastProjection (Y : Scheme.{u}) (d : ℕ) :=
  AffineSpace PUnit.{u + 1} (iteratedAffineLine Y d) ↘ iteratedAffineLine Y d

/-- The coordinate projections are separated and have canonical compactifications.
Source: the polynomial-chart paragraph (blueprint: def-pur-affine-space-comparison).
Proof: the existing iteratedAffineLineProj is a composite of d polynomial projections.
Every projection is affine, hence separated and quasi-compact, and is locally finite type
by its polynomial generators. Compactify each affine line by its projective line;
composition of compactifiable separated morphisms supplies the iterated compactification.
This argument works over arbitrary Y, and d=0 uses the identity compactification. -/
theorem projection_geometry (Y : Scheme.{u}) (d : ℕ) :
    IsSeparated (iteratedAffineLineProj Y d) ∧
    HasCompactification (iteratedAffineLineProj Y d) := by
  refine ⟨inferInstance, ?_⟩
  induction d with
  | zero => exact inferInstanceAs (HasCompactification (𝟙 Y))
  | succ d ih =>
    let c := @HasCompactification.compactification _ _ (iteratedAffineLineProj Y d) ih
    let c' := HasCompactification.compactification
      (AffineSpace PUnit.{u + 1} c.Z ↘ c.Z)
    refine (((c'.postcomp c.g).precomp (AffineSpace.map PUnit.{u + 1} c.i)).copy
      (f' := iteratedAffineLineProj Y (d + 1)) ?_).hasCompactification
    rw [iteratedAffineLineProj_succ, ← Category.assoc, AffineSpace.map_over,
      Category.assoc, ← c.comm]

/-- The structure morphism on the coordinate tower.
Source: X_d and p_d (blueprint: def-pur-affine-space-comparison). -/
abbrev towerBase {Y S : Scheme.{u}} (aY : Y ⟶ S) (d : ℕ) :=
  iteratedAffineLineProj Y d ≫ aY

/-- Separated finite-type geometry of the coordinate tower over k.
Source: the polynomial-chart paragraph (blueprint: def-pur-affine-space-comparison).
Proof: compose the affine finite-type projection with the separated finite-type aY.
The locally finite-type property is inherited from the existing projection instance;
quasi-compactness follows from affineness and composition. Separatedness composes. -/
theorem tower_geometry {Y S : Scheme.{u}} (aY : Y ⟶ S)
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] (d : ℕ) :
    LocallyOfFiniteType (towerBase aY d) ∧ QuasiCompact (towerBase aY d) ∧
      IsSeparated (towerBase aY d) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Noetherian geometry of every coordinate stage over the fixed field.
Source: polynomial-chart paragraph (blueprint: def-pur-affine-space-comparison).
Proof: tower_geometry supplies the finite-type structure over Spec k. A field is
Noetherian, and a locally finite-type scheme over it is locally Noetherian. Quasi-
compactness of the finite-type structure gives quasi-compactness, hence Noetherianness. -/
theorem tower_noetherian (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] (d : ℕ) :
    IsNoetherian (iteratedAffineLine Y d) := by
  let := (tower_geometry aY d).1
  let := (tower_geometry aY d).2.1
  exact isNoetherian_of_locallyOfFiniteType (towerBase aY d)

/-- The actual affine-line twisted pullback functor, with the recorded compared Tate line.
Source: Lq* (-)(1)[2] in the recursion (blueprint: def-pur-affine-space-comparison). -/
@[irreducible]
def lineSource (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    D P T ⥤ D P (AffineSpace PUnit.{u + 1} T) :=
  (inverseImage (Ring P) (AffineSpace PUnit.{u + 1} T ↘ T)) ⋙
    (tensor (Ring P)
      (AffineSpace PUnit.{u + 1} T)).flip.obj
        (coefficient P.coefficients.l P.extension (P.level - 1) T P.level (annihilates P))

/-- The source functor's object is the recorded affine-line source, with no new notion.
Source: the affine-line factor (blueprint: def-pur-affine-space-comparison).
Proof: unfold lineSource and Functor.comp_obj/flip_obj; the result is exactly source_eq.
The equality only unfolds the fixed tensor coordinate and does not choose an isomorphism. -/
theorem lineSource_obj_eq (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (K : D P T) :
    (lineSource P T).obj K =
      source P.coefficients.l P.extension (P.level - 1) T P.level (annihilates P) K := by
  unfold lineSource
  exact (source_eq P.coefficients.l P.extension (P.level - 1) T P.level
    (annihilates P) K).symm

/-- The compared shifted finite Tate line B_a[2]. This is the recorded ordinary line,
not a new choice of orientation. Source: finite Tate-line paragraph
(blueprint: def-pur-affine-space-comparison). -/
def shiftedLine (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) : D P T :=
  (comparison (Ring P) T).obj
    ((Etale.ordinaryFiniteLine (Ring P) (P.coefficients.l ^ (P.level + 1))
      (annihilates P) T)⟦(2 : ℤ)⟧)

/-- Tensor by d copies of the shifted finite line, in the specified coordinate order.
This is the finite tensor-power presentation of M(d)[2d], with zero literally M.
Source: the nonnegative tensor-power and even-shift conventions
(blueprint: def-pur-affine-space-comparison). -/
@[irreducible]
def twistAction (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    ℕ → D P T ⥤ D P T :=
  action ((tensor (Ring P) T).flip.obj (shiftedLine P T))

/-- The annihilating exponent is invertible on every scheme over k.
Source: finite Tate-line pullback paragraph (blueprint: def-pur-affine-space-comparison).
Proof: primeUnit gives invertibility of ell. Powers of units are units, and the
natural-number cast of ell^(level+1) equals the power of its cast. -/
theorem exponentUnit (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) :
    IsUnit ((P.coefficients.l ^ (P.level + 1) : ℕ) : Γ(T, ⊤)) := by
  simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (P.level + 1)

/-- Canonical pullback of the shifted Tate line: inverse site comparison, then the
ordinary roots-of-unity pullback. Source: finite Tate-line pullback display
(blueprint: def-pur-affine-space-comparison). -/
def shiftedLinePullback (P : WeilConjectures.PurityFiniteSetting.{u})
    {X T : Scheme.{u}} (f : X ⟶ T) (aT : T ⟶ Spec (.of P.field.k)) :
    (inverseImage (Ring P) f).obj (shiftedLine P T) ≅
      shiftedLine P X :=
  ((pullback (Ring P) f).app
    ((Etale.ordinaryFiniteLine (Ring P) (P.coefficients.l ^ (P.level + 1))
      (annihilates P) T)⟦(2 : ℤ)⟧)).symm ≪≫
    comparedLinePullback (Ring P) (P.coefficients.l ^ (P.level + 1))
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P) f
      (exponentUnit P T aT)

/-- The affine-line comparison coefficient identified with that same shifted line.
Source: the finite Tate-line normalization (blueprint: def-pur-affine-space-comparison). -/
def lineCoefficientIso (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) :
    coefficient P.coefficients.l P.extension (P.level - 1) T P.level (annihilates P) ≅
      shiftedLine P (AffineSpace PUnit.{u + 1} T) :=
  eqToIso (coefficient_comparison_eq P.coefficients.l P.extension (P.level - 1)
    T P.level (annihilates P)) ≪≫
    (comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).mapIso
      (eqToIso (etaleCoefficient_eq P.coefficients.l P.extension (P.level - 1)
        T P.level (annihilates P))) ≪≫
    comparedLinePullback (Ring P) (P.coefficients.l ^ (P.level + 1))
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
      (ProjectiveLine.affineChart T)
      (exponentUnit P (ProjectiveLine T) ((ProjectiveLine T ↘ T) ≫ aT))

/-- Lp_d* K(d)[2d], using the finite Tate tensor power on X_d itself. The identity
pullback, zero twist and zero shift are normalized to the identity at d=0.
Source: domain of gamma (blueprint: def-pur-affine-space-comparison). -/
@[irreducible]
def orderedSource (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    (d : ℕ) → D P Y ⥤ D P (iteratedAffineLine Y d)
  | 0 => 𝟭 _
  | d + 1 =>
    (upperStar (ModuleCat.{u + 1} (Ring P))
      (iteratedAffineLineProj Y (d + 1))).leftDerivedFunctor ⋙
        twistAction P (iteratedAffineLine Y (d + 1)) (d + 1)

/-- The literal canonical tensor reassociation, retaining its own computed endpoints.
This avoids making elaboration normalize the whole derived category merely to change
source coordinates. It contains the actual pullback compositor, inverse canonical tensor
comparison in each Tate factor, and canonical affine-line coefficient identification.
Source: I_d display (blueprint: def-pur-affine-space-comparison). -/
def sourceReassociationRaw (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) (K : D P Y) :
    (d : ℕ) → Σ M N : D P (iteratedAffineLine Y (d + 1)), M ≅ N
  | 0 => ⟨_, _, tensorZeroReassociation (Ring P) (lastProjection Y 0)
      (shiftedLine P (iteratedAffineLine Y 1))
      (coefficient P.coefficients.l P.extension (P.level - 1) Y P.level (annihilates P))
      (lineCoefficientIso P Y aY).symm K⟩
  | d + 1 => ⟨_, _, tensorReassociation (Ring P) (lastProjection Y (d + 1))
      (iteratedAffineLineProj Y (d + 1))
      (shiftedLine P (iteratedAffineLine Y (d + 1)))
      (shiftedLine P (iteratedAffineLine Y (d + 2)))
      (coefficient P.coefficients.l P.extension (P.level - 1)
        (iteratedAffineLine Y (d + 1)) P.level (annihilates P))
      (shiftedLinePullback P (lastProjection Y (d + 1)) (towerBase aY (d + 1)))
      (lineCoefficientIso P (iteratedAffineLine Y (d + 1)) (towerBase aY (d + 1))).symm
      K (d + 1)⟩

/-- The literal canonical tensor composite has precisely the displayed I_d endpoints.
The hom is specified by heterogeneous equality to the actual composite, so this is a
unique coordinate transport, never a bare existence assertion for an arbitrary iso.
Source: I_d and nonnegative twist/shift additivity
(blueprint: def-pur-affine-space-comparison).
Proof: split d=0 or d+1. Unfold orderedSource, lineSource, twistAction and action at their
outermost successor only. At zero the two endpoints are the tensorZeroReassociation
endpoints because p_1=q_0≫id and the zero twist is identity. At a positive stage they are
the tensorReassociation endpoints because p_(d+2)=q_(d+1)≫p_(d+1). The raw map already
uses the canonical inverse finite tensor comparison in every factor, the inverse site
comparison on the finite roots-of-unity line, and lineCoefficientIso; no map is chosen.
Transport that raw iso along the definitional endpoint equalities. Its hom satisfies HEq
by reflexivity after substitution. If another iso satisfies the same HEq, transitivity
of HEq gives equality of homs; Iso.ext then proves equality of the isomorphisms. -/
theorem sourceReassociation_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k)) (K : D P Y) (d : ℕ) :
    ∃! e : (orderedSource P Y (d + 1)).obj K ≅
      (lineSource P (iteratedAffineLine Y d)).obj ((orderedSource P Y d).obj K),
      HEq e.hom (sourceReassociationRaw P Y aY K d).2.2.hom := by
  cases d with
  | zero =>
    unfold orderedSource lineSource twistAction
    refine ⟨(sourceReassociationRaw P Y aY K 0).2.2, HEq.rfl, ?_⟩
    intro e he
    apply Iso.ext
    exact eq_of_heq he
  | succ d =>
    unfold orderedSource lineSource twistAction
    refine ⟨(sourceReassociationRaw P Y aY K (d + 1)).2.2, HEq.rfl, ?_⟩
    intro e he
    apply Iso.ext
    exact eq_of_heq he

/-- The specified I_d, obtained by unique transport of the actual canonical composite.
Its hom is fixed exactly by sourceReassociation_existsUnique, including the zero unitor.
Source: I_d display (blueprint: def-pur-affine-space-comparison). -/
@[irreducible]
def sourceReassociation (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) (K : D P Y) (d : ℕ) :
    (orderedSource P Y (d + 1)).obj K ≅
      (lineSource P (iteratedAffineLine Y d)).obj ((orderedSource P Y d).obj K) :=
  (sourceReassociation_existsUnique P Y aY K d).exists.choose

/-- The exceptional functor at each stage, normalized to the identity in dimension zero.
At every positive dimension this is the recorded transported etale exceptional functor.
Source: Rp_d! and p_0=id conventions (blueprint: def-pur-affine-space-comparison). -/
@[irreducible]
def exceptional (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    (d : ℕ) → D P Y ⥤ D P (iteratedAffineLine Y d)
  | 0 => 𝟭 _
  | d + 1 =>
    letI : HasCompactification (iteratedAffineLineProj Y (d + 1)) :=
      (projection_geometry Y (d + 1)).2
    rightDerivedUpperShriek (Ring P) (iteratedAffineLineProj Y (d + 1))

/-- The ordinary etale antecedent of the exceptional image at a positive stage.
This is the actual etale right adjoint applied to Rnu_* K, not a chosen antecedent.
Source: the exceptional functor's defining comparison formula
(blueprint: def-pur-affine-space-comparison). -/
def exceptionalEtale (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (d : ℕ) (K : D P Y) :=
  letI : HasCompactification (iteratedAffineLineProj Y (d + 1)) :=
    (projection_geometry Y (d + 1)).2
  (Etale.rightDerivedUpperShriek (Ring P)
    (iteratedAffineLineProj Y (d + 1))).obj
      ((comparisonLowerStar (ModuleCat.{u + 1} (Ring P)) Y).rightDerivedFunctor.obj K)

/-- The defining etale-origin comparison for the transported exceptional functor.
Source: exceptional functor formula (blueprint: def-pur-affine-space-comparison).
Proof: unfold exceptional at d+1 and exceptionalEtale. The pro-etale functor is,
by definition, Rnu_* followed by the ordinary right adjoint and then comparison. -/
theorem exceptionalEtale_eq (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (d : ℕ) (K : D P Y) :
    (comparison (Ring P) (iteratedAffineLine Y (d + 1))).obj
      (exceptionalEtale P Y d K) = (exceptional P Y (d + 1)).obj K := by
  unfold exceptional exceptionalEtale
  rfl

/-- Finite-Tor constructibility and boundedness needed to apply the affine-line comparison
at the next step, without any added preservation hypothesis.
Source: the last applicability paragraph, thm-sf-preservation-class and
lem-sf-proetale-constructible-origin (blueprint: def-pur-affine-space-comparison).
Proof: transport the supplied bounded etale finite-Tor representative Ke to K. Apply
thm-sf-preservation-class to p_(d+1); polynomial charts give its finite-type domain.
Comparison reflects finite Tor amplitude by finiteTorComparisonNoetherian. The comparison
unit identifies the canonical Rnu_* antecedent with any supplied antecedent. Thus the
literal etale exceptionalEtale object is bounded constructible of finite Tor amplitude,
and its comparison image is bounded below. This covers all positive levels and empty Y. -/
theorem exceptional_applicability (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (d : ℕ) (K : Plus (Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) :
    boundedBelow (Ring P) (iteratedAffineLine Y (d + 1))
      ((exceptional P Y (d + 1)).obj K.obj) ∧
    etaleFiniteTor (Ring P)
      (iteratedAffineLine Y (d + 1)) (exceptionalEtale P Y d K.obj) := by
  let := (projection_geometry Y (d + 1)).2
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  let : HasInvertibleExponent (Ring P) Y :=
    ⟨P.coefficients.l ^ (P.level + 1),
      pow_pos (Fact.out : P.coefficients.l.Prime).pos _, annihilates P,
      exponentUnit P Y aY⟩
  let U := (comparisonLowerStar (ModuleCat.{u + 1} (Ring P)) Y).rightDerivedFunctor
  have hu := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} (Ring P)) Y Ke hKe.1.1.1
  let e : Ke ≅ U.obj K.obj :=
    asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} (Ring P)) Y).unit.app Ke) ≪≫
      U.mapIso eK
  have hU : etaleFiniteTor (Ring P) Y (U.obj K.obj) :=
    (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y).prop_of_iso
      e hKe
  constructor
  · unfold exceptional
    exact plus_rightDerivedUpperShriek_obj (iteratedAffineLineProj Y (d + 1)) K.property
  · exact Etale.constructibleFiniteTor_rightDerivedUpperShriek (Ring P) aY
      (iteratedAffineLineProj Y (d + 1)) hU

/-- Transpose a pasted counit, with its category parameters cached.
Source: pasted adjunction paragraph (blueprint: def-pur-affine-space-comparison). -/
@[irreducible]
def transposeComposition {C D E : Type v} [Category.{w} C] [Category.{w} D]
    [Category.{w} E] (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (P : ObjectProperty C) {M N : C} {V : D} {K : E} (hM : P M)
    (eh : (H.obj M ⟶ K) ≃ (M ⟶ N)) (a : F.obj M ⟶ V) (b : G.obj V ⟶ K)
    (e : P.ι ⋙ F ⋙ G ≅ P.ι ⋙ H) : M ⟶ N :=
  eh (e.inv.app ⟨M, hM⟩ ≫ G.map a ≫ b)

/-- The inverse conjugate of the actual compact-support compositor. It is constructed
by transposing the pasted counit through the composite morphism's standing Hom bijection.
In particular this is a concrete map, not a choice from a bare isomorphism existence result.
Source: c_r^-1 and the pasted adjunction paragraph
(blueprint: def-pur-affine-space-comparison). -/
def compositionInverse (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace T] [CompactSpace S]
    (K : Plus A S) :
    (rightDerivedUpperShriek A f).obj
      ((rightDerivedUpperShriek A g).obj K.obj) ⟶
      (rightDerivedUpperShriek A (f ≫ g)).obj K.obj :=
  transposeComposition
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X)
    (plusEtaleOrigin_rightDerivedUpperShriek_obj f
      (plus_rightDerivedUpperShriek_obj g K.property))
    (rightDerivedUpperShriekHomEquiv (f ≫ g)
      (plusEtaleOrigin_rightDerivedUpperShriek_obj f
        (plus_rightDerivedUpperShriek_obj g K.property)) K.property)
    (rightDerivedUpperShriekCounit f _ (plus_rightDerivedUpperShriek_obj g K.property))
    (rightDerivedUpperShriekCounit g K.obj K.property)
    (originCompositionAmbient A f g)

/-- The canonical inverse exceptional identity compositor, cached at a general ring.
Source: c_0 normalization (blueprint: def-pur-affine-space-comparison). -/
def identityCompositeMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T : Scheme.{u}} (f : X ⟶ T) [HasCompactification f]
    [HasCompactification (f ≫ 𝟙 T)] (K : C A T) :
    (rightDerivedUpperShriek A f).obj K ⟶
      (rightDerivedUpperShriek A (f ≫ 𝟙 T)).obj K :=
  (rightDerivedUpperShriekCongr A (Category.comp_id f).symm).hom.app K

/-- Canonical change from the explicit affine-chart compactification to the standing
exceptional functor, through uniqueness of the ordinary etale right adjoint. The left
comparison is the already recorded canonical compactification comparison.
Source: the standing exceptional-functor convention
(blueprint: def-pur-affine-space-comparison). -/
def lineExceptionalIso (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    [(Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (affineTraceLineCompactification T)).IsLeftAdjoint]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    (sfFiniteExceptionalAt A (affineTraceLineCompactification T)).obj K ≅
      (rightDerivedUpperShriek A
        (AffineSpace PUnit.{u + 1} T ↘ T)).obj K :=
  (comparison A (AffineSpace PUnit.{u + 1} T)).mapIso
    (((Adjunction.ofIsLeftAdjoint
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (affineTraceLineCompactification T))).rightAdjointUniq
          ((Etale.rightDerivedUpperShriekAdjunction A
            (AffineSpace PUnit.{u + 1} T ↘ T)).ofNatIsoLeft
              (Etale.rightDerivedLowerShriekIso A
                (affineTraceLineCompactification T)).symm)).app
      ((comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctor.obj K))

/-- The recorded affine-line comparison in the literal source-functor coordinates and
standing exceptional coordinates. Only canonical compactification transport is applied.
Source: gamma_(q_r,-) in the recursive display
(blueprint: def-pur-affine-space-comparison). -/
@[irreducible]
def lineComparison (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (K : Plus (Ring P) T)
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : etaleFiniteTor (Ring P) T Ke)
    (eK : (comparison (Ring P) T).obj Ke ≅ K.obj) :
    (lineSource P T).obj K.obj ⟶
      (rightDerivedUpperShriek (Ring P)
        (AffineSpace PUnit.{u + 1} T ↘ T)).obj K.obj :=
  eqToHom (lineSource_obj_eq P T K.obj) ≫
    AffineLinePurity.affineLinePurityComparison P T P.level (annihilates P) aT K Ke hKe eK ≫
    (lineExceptionalIso (Ring P) T K.obj).hom

/-- Ordinary antecedent at every coordinate stage, with the given antecedent at zero.
Source: origin witnesses in the recursion (blueprint: def-pur-affine-space-comparison). -/
def stageEtale (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : D P Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y) :
    (d : ℕ) → Etale.DerivedCategoryModule (Ring P) (iteratedAffineLine Y d)
  | 0 => Ke
  | d + 1 => exceptionalEtale P Y d K

/-- The actual comparison identification of the stage antecedent.
Source: retained witnesses (blueprint: def-pur-affine-space-comparison). -/
def stageComparison (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : D P Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K) : (d : ℕ) →
    (comparison (Ring P) (iteratedAffineLine Y d)).obj (stageEtale P Y K Ke d) ≅
      (exceptional P Y d).obj K
  | 0 => by
    unfold exceptional
    exact eK
  | d + 1 => eqToIso (exceptionalEtale_eq P Y d K)

/-- All-stage form of the applicability clause, including the identity at zero.
Source: thm-sf-preservation-class and the recursion domain
(blueprint: def-pur-affine-space-comparison).
Proof: at zero use K.property and hKe. At a positive stage use
exceptional_applicability, since stageEtale is the canonical etale exceptional antecedent.
The comparison is exactly stageComparison; hence no origin witness is chosen. -/
theorem stage_applicability (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    boundedBelow (Ring P) (iteratedAffineLine Y d) ((exceptional P Y d).obj K.obj) ∧
      etaleFiniteTor (Ring P)
        (iteratedAffineLine Y d) (stageEtale P Y K.obj Ke d) := by
  cases d with
  | zero =>
    unfold exceptional stageEtale
    exact ⟨K.property, hKe⟩
  | succ d => exact exceptional_applicability P Y aY d K Ke hKe eK

/-- The concrete inverse exceptional compositor, retaining its computed endpoints.
Zero uses the identity-composition normalization; positive stages use the inverse mate.
Source: c_d inverse (blueprint: def-pur-affine-space-comparison). -/
def exceptionalCompositeRaw (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) :
    (d : ℕ) → Σ M N : D P (iteratedAffineLine Y (d + 1)), M ⟶ N
  | 0 =>
    letI : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
      HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
    ⟨_, _, identityCompositeMap (Ring P) (lastProjection Y 0) K.obj⟩
  | d + 1 =>
    letI : HasCompactification (iteratedAffineLineProj Y (d + 1)) :=
      (projection_geometry Y (d + 1)).2
    letI : HasCompactification (iteratedAffineLineProj Y (d + 2)) :=
      (projection_geometry Y (d + 2)).2
    letI : HasCompactification
        (lastProjection Y (d + 1) ≫ iteratedAffineLineProj Y (d + 1)) :=
      HasCompactification.of_eq (f := iteratedAffineLineProj Y (d + 2))
        (iteratedAffineLineProj_succ Y (d + 1))
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    letI : IsNoetherian (iteratedAffineLine Y (d + 1)) := tower_noetherian P Y aY (d + 1)
    ⟨_, _, compositionInverse (Ring P) (lastProjection Y (d + 1))
      (iteratedAffineLineProj Y (d + 1)) K⟩

/-- The inverse compositor's hom is uniquely the concrete inverse mate above.
Source: c_d convention (blueprint: def-pur-affine-space-comparison).
Proof: at zero normalize exceptional_0 to identity and use p_1=q_0≫id.
At a positive stage unfold exceptional and iteratedAffineLineProj once. The raw inverse
mate then has exactly these endpoints. Transport along these definitional equalities;
HEq is reflexive after substitution. Equality with the fixed hom gives uniqueness. -/
theorem exceptionalComposite_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (d : ℕ) :
    ∃! m : (rightDerivedUpperShriek (Ring P)
        (lastProjection Y d)).obj ((exceptional P Y d).obj K.obj) ⟶
      (exceptional P Y (d + 1)).obj K.obj,
      HEq m (exceptionalCompositeRaw P Y aY K d).2.2 := by
  cases d with
  | zero =>
    unfold exceptional
    refine ⟨(exceptionalCompositeRaw P Y aY K 0).2.2, HEq.rfl, ?_⟩
    intro m hm
    exact eq_of_heq hm
  | succ d =>
    unfold exceptional
    refine ⟨(exceptionalCompositeRaw P Y aY K (d + 1)).2.2, HEq.rfl, ?_⟩
    intro m hm
    exact eq_of_heq hm

/-- The inverse conjugate in normalized exceptional coordinates, with hom fixed exactly.
Source: c_d inverse (blueprint: def-pur-affine-space-comparison). -/
@[irreducible]
def exceptionalComposite (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (d : ℕ) :
    (rightDerivedUpperShriek (Ring P)
      (lastProjection Y d)).obj ((exceptional P Y d).obj K.obj) ⟶
      (exceptional P Y (d + 1)).obj K.obj :=
  (exceptionalComposite_existsUnique P Y aY K d).exists.choose

/-- The comparison hom type with a single cached derived-category instance.
Source: the displayed comparison (blueprint: def-pur-affine-space-comparison). -/
abbrev ComparisonHom (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : D P Y) (d : ℕ) :=
  (orderedSource P Y d).obj K ⟶ (exceptional P Y d).obj K

/-- The literal four-arrow successor, uniformly including the identity stage.
Source: recursive gamma display (blueprint: def-pur-affine-space-comparison). -/
def comparisonStep (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) (d : ℕ)
    (h : ComparisonHom P Y K.obj d) : ComparisonHom P Y K.obj (d + 1) :=
  letI : LocallyOfFiniteType (towerBase aY d) := (tower_geometry aY d).1
  letI : QuasiCompact (towerBase aY d) := (tower_geometry aY d).2.1
  letI : IsSeparated (towerBase aY d) := (tower_geometry aY d).2.2
  (sourceReassociation P Y aY K.obj d).hom ≫
    (lineSource P (iteratedAffineLine Y d)).map h ≫
    lineComparison P (iteratedAffineLine Y d) (towerBase aY d)
      ⟨(exceptional P Y d).obj K.obj, (stage_applicability P Y aY K Ke hKe eK d).1⟩
      (stageEtale P Y K.obj Ke d) (stage_applicability P Y aY K Ke hKe eK d).2
      (stageComparison P Y K.obj Ke eK d) ≫
    exceptionalComposite P Y aY K d

/-- Dependent ordered recursion, keeping its type family abstract while checking the
recursor. Source: the recursive display (blueprint: def-pur-affine-space-comparison). -/
def orderedRec {H : ℕ → Sort v} (zero : H 0)
    (step : (d : ℕ) → H d → H (d + 1)) : (d : ℕ) → H d
  | 0 => zero
  | d + 1 => step d (orderedRec zero step d)

/-- The literal dimension-zero identity in the normalized source and target coordinates.
Source: gamma_0=id (blueprint: def-pur-affine-space-comparison). -/
def comparisonZero (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : D P Y) : ComparisonHom P Y K 0 := by
  unfold ComparisonHom orderedSource exceptional
  exact 𝟙 K

/-- The affine-space purity comparison, defined by the required ordered recursion.
The source uses the finite tensor-power presentation of Lp_d* K(d)[2d].
In dimension zero both source and target are literally K, and the map is its identity.
At every successor precompose lineSource(gamma_d) with the explicit sourceReassociation,
then the recorded affine-line comparison at Rp_d!K, then c_d inverse. The latter is the
conjugate of the recorded compact-support compositor through pasted adjunctions.
No isomorphy of gamma is part of the definition.
Source: blueprint sec-smooth-purity/sk-prop-an, final recursive display
(blueprint: def-pur-affine-space-comparison). -/
def affineSpacePurityComparison (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    ComparisonHom P Y K.obj d :=
  orderedRec (H := fun j => ComparisonHom P Y K.obj j)
    (comparisonZero P Y K.obj) (comparisonStep P Y aY K Ke hKe eK) d

end AlgebraicGeometry.ProEtale.AffineSpacePurity

namespace AlgebraicGeometry.ProEtale.GeneralFiniteAffineSpacePurity

/-- Ordered iteration, with literal identity at zero.
Source: ordered Tate powers (blueprint: def-pur-affine-space-comparison). -/
def action {C : Type v} [Category.{w} C] (F : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | d + 1 => action F d ⋙ F

/-- Pull a specified one-factor comparison through an ordered power.
Source: the source reassociation (blueprint: def-pur-affine-space-comparison). -/
def actionPullbackIso {C : Type v} [Category.{w} C]
    {C' : Type v₁} [Category.{w₁} C']
    (F : C ⥤ C) (G : C' ⥤ C') (H : C ⥤ C')
    (e : ∀ M : C, H.obj (F.obj M) ≅ G.obj (H.obj M)) (K : C) :
    (d : ℕ) → H.obj ((action F d).obj K) ≅ (action G d).obj (H.obj K)
  | 0 => Iso.refl _
  | d + 1 => e ((action F d).obj K) ≪≫ G.mapIso (actionPullbackIso F G H e K d)

/-- The fixed coefficient derived category.
Source: current purity conventions (blueprint: def-pur-affine-space-comparison). -/
abbrev D (T : Scheme.{u}) := P.derived T

/-- The ordered tower, built by adjoining the last coordinate.
Source: ordered affine tower (blueprint: def-pur-affine-space-comparison). -/
def tower (Y : Over (Spec (.of P.field.k))) : ℕ → Over (Spec (.of P.field.k))
  | 0 => Y
  | d + 1 => GeneralFiniteAffineLinePurity.affineOver P (tower Y d)

instance tower_finite (Y : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType Y.hom] (d : ℕ) : LocallyOfFiniteType (tower P Y d).hom := by
  induction d with
  | zero => exact inferInstanceAs (LocallyOfFiniteType Y.hom)
  | succ d ih =>
    exact inferInstanceAs
      (LocallyOfFiniteType (GeneralFiniteAffineLinePurity.affineOver P _).hom)

instance tower_compact (Y : Over (Spec (.of P.field.k)))
    [QuasiCompact Y.hom] (d : ℕ) : QuasiCompact (tower P Y d).hom := by
  induction d with
  | zero => exact inferInstanceAs (QuasiCompact Y.hom)
  | succ d ih =>
    exact inferInstanceAs (QuasiCompact (GeneralFiniteAffineLinePurity.affineOver P _).hom)

instance tower_separated (Y : Over (Spec (.of P.field.k)))
    [IsSeparated Y.hom] (d : ℕ) : IsSeparated (tower P Y d).hom := by
  induction d with
  | zero => exact inferInstanceAs (IsSeparated Y.hom)
  | succ d ih =>
    exact inferInstanceAs (IsSeparated (GeneralFiniteAffineLinePurity.affineOver P _).hom)

/-- The total ordered projection, with its identity normalization at dimension zero.
Source: p_d and q_d (blueprint: def-pur-affine-space-comparison). -/
def projection (Y : Over (Spec (.of P.field.k))) :
    (d : ℕ) → tower P Y d ⟶ Y
  | 0 => 𝟙 Y
  | 1 => GeneralFiniteAffineLinePurity.affineMap P Y
  | d + 2 => GeneralFiniteAffineLinePurity.affineMap P (tower P Y (d + 1)) ≫ projection Y (d + 1)

/-- One twisted pullback factor, distributing its even shift to the Tate line.
Source: Lq* (-)(1)[2] (blueprint: def-pur-affine-space-comparison). -/
def lineSource (Y : Over (Spec (.of P.field.k))) :
    D P Y.left ⥤ D P (GeneralFiniteAffineLinePurity.affineOver P Y).left :=
  P.pullback (GeneralFiniteAffineLinePurity.affineMap P Y).left ⋙
    tensorRight (GeneralFiniteAffineLinePurity.nativeLine P _)

/-- The finite tensor-power presentation of Lp_d* K(d)[2d].
Source: ordered source (blueprint: def-pur-affine-space-comparison). -/
def orderedSource (Y : Over (Spec (.of P.field.k))) :
    (d : ℕ) → D P Y.left ⥤ D P (tower P Y d).left
  | 0 => 𝟭 _
  | d + 1 => P.pullback (projection P Y (d + 1)).left ⋙
      action
        (tensorRight (GeneralFiniteAffineLinePurity.nativeLine P (tower P Y (d + 1)).left)) (d + 1)

/-- The exceptional functor preserves Dctf because it is the recorded Brown restriction.
Its dimension-zero normalization is literal identity.
Source: applicability clause (blueprint: def-pur-affine-space-comparison). -/
def exceptional : (d : ℕ) → P.constructibleFiniteTor Y.left ⥤
    P.constructibleFiniteTor (tower P Y d).left
  | 0 => 𝟭 _
  | d + 1 => (P.exceptionalData (projection P Y (d + 1))).right

/-- The full inclusion into the localizing category, unchanged on objects and maps.
Source: constructible composition domain (blueprint: def-pur-affine-space-comparison). -/
def toLocalizing (T : Scheme.{u}) : P.constructibleFiniteTor T ⥤
    (localizingClosureProEtale P.ring T).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K hK _Q _ hQ ↦ hQ K hK)

/-- Compact-support composition for the exact lower functors of the recorded Brown data.
The displayed iso is obtained by restricting the normalized ambient compositor.
Source: alpha_r (blueprint: def-pur-affine-space-comparison). -/
def lowerComposition
    {X T S : Over (Spec (.of P.field.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (f : X ⟶ T) (g : T ⟶ S) :
    (P.exceptionalData f).lower ⋙ (P.exceptionalData g).lower ≅
      (P.exceptionalData (f ≫ g)).lower := by
  let a := P.exceptionalData f
  let b := P.exceptionalData g
  let c := P.exceptionalData (f ≫ g)
  let iX := (constantModelBoundedConstructible P.ring X.left ⊓
    fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K).ι
  let iT := (constantModelBoundedConstructible P.ring T.left ⊓
    fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K).ι
  let iS := (constantModelBoundedConstructible P.ring S.left ⊓
    fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K).ι
  let F := P.compactSupport (compactificationOverField f)
  let G := P.compactSupport (compactificationOverField g)
  let H := P.compactSupport (compactificationOverField (f ≫ g))
  let e := (coherence P).comp (SepFinType.homMk f) (SepFinType.homMk g)
    (compactificationOverField f) (compactificationOverField g)
    (compactificationOverField (f ≫ g))
  exact Functor.fullyFaithfulCancelRight iS
    (Functor.associator a.lower b.lower iS ≪≫
      Functor.isoWhiskerLeft a.lower (eqToIso b.lower_eq) ≪≫
      (Functor.associator a.lower iT G).symm ≪≫
      Functor.isoWhiskerRight (eqToIso a.lower_eq) G ≪≫
      Functor.associator iX F G ≪≫
      Functor.isoWhiskerLeft (toLocalizing P X.left) e ≪≫
      (eqToIso c.lower_eq).symm)

/-- The exceptional compositor is the adjoint conjugate of the fixed alpha_r.
Source: c_r (blueprint: def-pur-affine-space-comparison). -/
def exceptionalComposition
    {X T S : Over (Spec (.of P.field.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (f : X ⟶ T) (g : T ⟶ S) :
    (P.exceptionalData (f ≫ g)).right ≅
      (P.exceptionalData g).right ⋙ (P.exceptionalData f).right :=
  conjugateIsoEquiv (P.exceptionalData (f ≫ g)).adjunction
    ((P.exceptionalData f).adjunction.comp (P.exceptionalData g).adjunction)
    (lowerComposition P f g)

/-- Root-normalized transport of the shifted Tate line along a map over k.
The integral coordinates are determined by their projections to the root tower.
Source: tau and its tensor powers (blueprint: def-pur-affine-space-comparison). -/
def shiftedLinePullback
    {X T : Over (Spec (.of P.field.k))} (f : X ⟶ T) :
    (P.pullback f.left).obj (GeneralFiniteAffineLinePurity.nativeLine P T.left) ≅
      GeneralFiniteAffineLinePurity.nativeLine P X.left := by
  letI : ∀ x : X.left, Invertible (P.coefficients.l : X.left.residueField x) :=
    fun x ↦ (by
      simpa only [map_natCast] using
        (PurityTransport.primeUnit P.field P.coefficients.l P.coefficients.different).map
          (X.hom.residueFieldAlgebraMap x) :
            IsUnit (P.coefficients.l : X.left.residueField x)).invertible
  letI : ∀ x : T.left, Invertible (P.coefficients.l : T.left.residueField x) :=
    fun x ↦ (by
      simpa only [map_natCast] using
        (PurityTransport.primeUnit P.field P.coefficients.l P.coefficients.different).map
          (T.hom.residueFieldAlgebraMap x) :
            IsUnit (P.coefficients.l : T.left.residueField x)).invertible
  let e (Z : Scheme.{u}) : GeneralFiniteAffineLinePurity.nativeLine P Z ≅
      P.coefficient.derivedLine P.coefficients.l Z 1 :=
    (shiftFunctor _ (2 : ℤ)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso
        (GeneralFiniteAffineLinePurity.signedFirstIso P Z ≪≫
          (λ_ (P.firstTwist Z)).symm))
  let c := (linePullCoordinates_nonempty P.coefficients.l P.coefficient f.left).some
  exact (P.pullback f.left).mapIso (e T.left) ≪≫
    c.derived P.coefficients.l 1 ≪≫ (e X.left).symm

/-- The four source arrows in ordered tensor-power coordinates. At zero the
normalized source is literally the one-line source. At a positive stage use the
pullback compositor, pull the ordered tensor power back factor by factor, and
leave the last Tate factor on the right. Every factor is the canonical tensorator.
Source: I_r (blueprint: def-pur-affine-space-comparison). -/
def sourceReassociation (K : D P Y.left) : (d : ℕ) →
    (orderedSource P Y (d + 1)).obj K ≅
      (lineSource P (tower P Y d)).obj ((orderedSource P Y d).obj K)
  | 0 => Iso.refl _
  | d + 1 =>
    let f := GeneralFiniteAffineLinePurity.affineMap P (tower P Y (d + 1))
    let g := projection P Y (d + 1)
    let W := GeneralFiniteAffineLinePurity.nativeLine P (tower P Y (d + 1)).left
    let W' := GeneralFiniteAffineLinePurity.nativeLine P (tower P Y (d + 2)).left
    let F := tensorRight W
    let G := tensorRight W'
    let H := P.pullback f.left
    tensorIso
      ((action G (d + 1)).mapIso
        ((CondensedRing.leftDerivedUpperStarComp P.ring f.left g.left).app K)
        ≪≫ (actionPullbackIso F G H
          (fun M ↦ (Functor.Monoidal.μIso H M W).symm ≪≫
            tensorIso (Iso.refl _) (shiftedLinePullback P f))
          ((P.pullback g.left).obj K) (d + 1)).symm)
      (Iso.refl W')

/-- The inverse exceptional compositor, normalized to identity at the first stage.
At a positive stage this is the inverse conjugate of alpha_r, evaluated at K.
Source: c_r inverse (blueprint: def-pur-affine-space-comparison). -/
def exceptionalComposite (K : P.constructibleFiniteTor Y.left) : (d : ℕ) →
    ((P.exceptionalData (GeneralFiniteAffineLinePurity.affineMap P (tower P Y d))).right.obj
      ((exceptional P Y d).obj K)).obj ⟶ ((exceptional P Y (d + 1)).obj K).obj
  | 0 => 𝟙 _
  | d + 1 => ((exceptionalComposition P
      (GeneralFiniteAffineLinePurity.affineMap P (tower P Y (d + 1)))
      (projection P Y (d + 1))).inv.app K).hom

/-- The comparison type on the actual current coefficient module sheaves.
Source: gamma display (blueprint: def-pur-affine-space-comparison). -/
abbrev ComparisonHom (K : P.constructibleFiniteTor Y.left) (d : ℕ) :=
  (orderedSource P Y d).obj K.obj ⟶ ((exceptional P Y d).obj K).obj

/-- The ordered four-arrow successor. The exceptional input is already an object
of the recorded constructible finite-Tor category, so no origin witness is added.
Source: recursive display (blueprint: def-pur-affine-space-comparison). -/
def comparisonStep (K : P.constructibleFiniteTor Y.left) (d : ℕ)
    (h : ComparisonHom P Y K d) : ComparisonHom P Y K (d + 1) :=
  (sourceReassociation P Y K.obj d).hom ≫
    (lineSource P (tower P Y d)).map h ≫
    lineComparison P (tower P Y d) A n hA hP ((exceptional P Y d).obj K) ≫
    exceptionalComposite P Y K d

/-- The literal dimension-zero identity.
Source: gamma_0 = id (blueprint: def-pur-affine-space-comparison). -/
def comparisonZero (K : P.constructibleFiniteTor Y.left) : ComparisonHom P Y K 0 :=
  𝟙 K.obj

/-- The current-coefficient ordered affine-space purity comparison. This is the
specified recursion, not a choice of an isomorphism. The source is the ordered
finite tensor-power presentation of Lp_d* K(d)[2d], with the even shift carried by
each Tate factor. The target is the recorded Brown exceptional functor, normalized
at dimension zero. Every current Dctf input over the finite primary coefficient
presentation is admitted; no auxiliary etale-origin or comparison data is required.
Source: ordered recursive composite (blueprint: def-pur-affine-space-comparison). -/
def intrinsicAffineSpacePurityComparison (K : P.constructibleFiniteTor Y.left) :
    (d : ℕ) → ComparisonHom P Y K d
  | 0 => comparisonZero P Y K
  | d + 1 => comparisonStep P Y A n hA hP K d
      (intrinsicAffineSpacePurityComparison K d)

/-- The dimension-zero normalization is definitional.
Source: gamma_0 = id (blueprint: def-pur-affine-space-comparison).
Proof: unfold the zero branch of the recursion. -/
theorem intrinsicAffineSpacePurityComparison_zero (K : P.constructibleFiniteTor Y.left) :
    intrinsicAffineSpacePurityComparison P Y A n hA hP K 0 = 𝟙 K.obj := rfl

/-- The specified successor is definitional, in precisely the blueprint's arrow order.
Source: recursive display (blueprint: def-pur-affine-space-comparison).
Proof: unfold the successor branch of the recursion. -/
theorem intrinsicAffineSpacePurityComparison_succ (K : P.constructibleFiniteTor Y.left)
    (d : ℕ) : intrinsicAffineSpacePurityComparison P Y A n hA hP K (d + 1) =
      comparisonStep P Y A n hA hP K d
        (intrinsicAffineSpacePurityComparison P Y A n hA hP K d) := rfl

/-- At rank one the ordered recursion is the recorded line comparison in the
same tensor-factor coordinates.
Source: first successor of the recursive display
(blueprint: def-pur-affine-space-comparison).
Proof: the source and exceptional normalizations are identities; functors preserve
identity maps, and identity composition cancels. -/
theorem intrinsicAffineSpacePurityComparison_one (K : P.constructibleFiniteTor Y.left) :
    intrinsicAffineSpacePurityComparison P Y A n hA hP K 1 =
      lineComparison P Y A n hA hP K := by
  change (𝟙 _) ≫ (lineSource P Y).map (𝟙 K.obj) ≫
    lineComparison P Y A n hA hP K ≫ (𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]
  exact (congrArg (fun f ↦ f ≫ lineComparison P Y A n hA hP K)
    ((lineSource P Y).map_id K.obj)).trans (Category.id_comp _)

end AlgebraicGeometry.ProEtale.GeneralFiniteAffineSpacePurity
