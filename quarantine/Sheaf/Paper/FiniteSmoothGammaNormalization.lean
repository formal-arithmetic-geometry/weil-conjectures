/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
public import Sheaf.AlgebraicGeometry.SmoothTensorDuality
public import Sheaf.Paper.NoetherianEtaleSectionSpecialization
public import Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility
public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import Sheaf.Targets.VectorBundlePurity
import Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension
import Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat
import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
import Sheaf.AlgebraicGeometry.ShriekTensorComposition
import WeilConjectures.Compactification.NagataCompactification
import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# The three-factor smooth orientation in relative dimension zero

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
three-factor purity formula and its sum-counit normalization
(blueprint: lem-pur-finite-smooth-gamma-normalization).

The comparison families are quantified with the graph and homotopy normalization equations
of etaleSupportMapCompatibility. That dependency supplies precisely such families. The
right-adjoint coordinates are constructed from the actual adjunctions, not chosen.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

noncomputable section

namespace AlgebraicGeometry.Etale

/-- A finite-type fibre product over a Noetherian scheme is Noetherian. This packages
Mathlib's locally Noetherian and compact-space base-change instances into IsNoetherian.
Source: the item's proof Step 2, finite-type-over-Noetherian permanence
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
instance finiteSmoothPullbackNoetherian {X Y : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] :
    IsNoetherian (pullback f f) := {}

/-- The type of the compact-support comparison families in etaleSupportMapCompatibility.
This only names its existing quantified family type for use in the coordinate constructions.
Source: Stacks Tags 0F4Y and 0GKM
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
abbrev FiniteSmoothCompactSupportComparisons (A : Type (u + 1)) [CommRing A] :=
  ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification e),
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory

/-- The graph and homotopy normalization equations of etaleSupportMapCompatibility.
The sheaf arrow extends sheet sections by zero off their graphs; its degreewise descent,
followed by the total-derived unit, is the inverse comparison. Thus N is never an
unconstrained isomorphism. Source: Stacks Tags 0F4Y, 0GKM, 0F7L
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def FiniteSmoothComparisonNormalized (A : Type (u + 1)) [CommRing A]
    (N : FiniteSmoothCompactSupportComparisons A) : Prop :=
  ∃ a : ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
      (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (c : Compactification e),
      etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⟶
        openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
          lowerStar (ModuleCat.{u + 1} A) c.g,
    ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
      [IsLocallyNoetherian T] [CompactSpace T]
      (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (c : Compactification e),
      (∀ M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A),
        (a e c).app M ≫ (compactificationSheafToDirectImage A c).app M =
          etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) e M) ∧
      (∀ P : HomotopyCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
          (ComplexShape.up ℤ),
        (N e c).inv.app (DerivedCategory.Qh.obj P) =
          compactSupportComparisonOnHomotopy A e c (a e c) P)

/-- Transport the graph-normalized fixed-compactification comparison to R e_!.
Source: Stacks Tags 0F4Y and 0GKM, as normalized by etaleSupportMapCompatibility
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothSumComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory :=
  (rightDerivedLowerShriekIso A (HasCompactification.compactification e)).symm ≪≫
    N e (HasCompactification.compactification e)

/-- The counit-preserving right-adjoint comparison rho_e, constructed by adjoint uniqueness.
The last transport changes exact degreewise inverse image into its left-derived model.
Source: the item's proof Step 1, Stacks Tags 0F4Y and 0GKM
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothAdjointCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    rightDerivedUpperShriek (ModuleCat.{u + 1} A) e ≅
      (upperStar (ModuleCat.{u + 1} A) e).leftDerivedFunctor :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) e).rightAdjointUniq
    (((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
      inferInstance).mapDerivedCategoryAdjunction).ofNatIsoLeft
      (finiteSmoothSumComparison A N e).symm) ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm

/-- Coordinates omega_e ≅ A_V induced by rho_e at A_T.
Source: the item's proof Step 1 (blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothOmegaCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    dualizingComplex (ModuleCat.{u + 1} A) e ≅
      MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A V) :=
  (finiteSmoothAdjointCoordinates A N e).app _ ≪≫
    leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) e

/-- Coordinates on the section invariant, obtained by pulling back rho_e at the unit.
Source: the item's proof Steps 1--3
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothSectionCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {V T : Scheme.{u}} [IsNoetherian V] [IsNoetherian T]
    (e : V ⟶ T) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] (s : T ⟶ V) :
    sectionInvariant A e s ≅ MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A T) :=
  (upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.mapIso
    (finiteSmoothOmegaCoordinates A N e) ≪≫
      leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) s

/-- First factor: pull back the actual exceptional base-change map by the diagonal.
The inverse section compositor identifies Delta^* p_2^* omega_f with omega_f.
Source: three-factor formula, prop-asd-smooth-base-change, proof Step 3
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothDiagonalFactor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    dualizingComplex (ModuleCat.{u + 1} A) f ⟶
      sectionInvariant A (pullback.fst f f) (pullback.diagonal f) :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (pullback.diagonal f) (pullback.snd f f) (pullback.diagonal_snd f)).inv.app _ ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.diagonal f)).leftDerivedFunctor.map
        (dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f f).flip)

/-- Type of deformation comparisons for the actual diagonal Rees space.
Source: lem-pur-noetherian-etale-section-specialization, normalized kappa
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def FiniteSmoothDeformationComparisons (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (hc : HasCompactification
      (Scheme.Hom.deformationSpaceProj (pullback.fst f f) (pullback.diagonal f))) :=
  letI := hc
  NoetherianSectionSpecialization.family A (pullback.fst f f) (pullback.diagonal f) ≅
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) X ↘ X)).leftDerivedFunctor.obj
        (sectionInvariant A (pullback.fst f f) (pullback.diagonal f))

/-- The normalization condition on the preceding comparison is exactly its t=1 condition.
Source: lem-pur-noetherian-etale-section-specialization, Normalized
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def FiniteSmoothDeformationNormalized (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f]
    (hc : HasCompactification
      (Scheme.Hom.deformationSpaceProj (pullback.fst f f) (pullback.diagonal f)))
    (κ : FiniteSmoothDeformationComparisons A f hc) : Prop :=
  letI := hc
  NoetherianSectionSpecialization.Normalized A (pullback.fst f f) (pullback.diagonal f)
    (pullback.diagonal_fst f) κ

/-- Proofs of the rank-zero geometry and the uniquely normalized deformation comparison.
The only non-proof field is kappa, whose t=1 normalization determines it uniquely by
lem-pur-noetherian-etale-section-specialization; no arbitrary existence choice is made.
Source: the item's proof Steps 2, 4--6
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
structure FiniteSmoothGammaData (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f] where
  /-- The actual normal projection identifies the rank-zero cone with X. -/
  normalIso : IsIso (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
  /-- Compactifiability of the actual extended-Rees family. -/
  deformationCompact : HasCompactification
    (Scheme.Hom.deformationSpaceProj (pullback.fst f f) (pullback.diagonal f))
  /-- The normalized family comparison, not an arbitrary comparison of its fibres. -/
  comparison : FiniteSmoothDeformationComparisons A f deformationCompact
  /-- Normalization by the specified mate on the fibre t=1. -/
  normalized : FiniteSmoothDeformationNormalized A f deformationCompact comparison

/-- The actual section invariant on the normal cone, retaining its Rees construction.
Source: the item's proof Step 4 (blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothNormalInvariant (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f] (G : FiniteSmoothGammaData A f) : DerivedCategoryModule A X :=
  letI := G.normalIso
  sectionInvariant A (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
    (pullback.diagonal f).normalConeZeroSection

/-- Second factor: the specified specialization, evaluated at zero from normalized kappa.
Source: the item's proof Step 6; lem-pur-noetherian-etale-section-specialization
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothDeformationFactor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f] (G : FiniteSmoothGammaData A f) :
    sectionInvariant A (pullback.fst f f) (pullback.diagonal f) ⟶
      finiteSmoothNormalInvariant A f G :=
  letI := G.normalIso
  letI := G.deformationCompact
  NoetherianSectionSpecialization.specialization A (pullback.fst f f)
    (pullback.diagonal f) G.comparison

/-- Normal-cone coordinates from the same graph-normalized sum adjunction.
Source: the item's proof Steps 1, 6--7
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothNormalCoordinates (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : FiniteSmoothCompactSupportComparisons A)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (G : FiniteSmoothGammaData A f) :
    finiteSmoothNormalInvariant A f G ≅
      MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A X) :=
  letI := G.normalIso
  letI := LocallyOfFiniteType.isLocallyNoetherian
    (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
  letI := QuasiCompact.compactSpace_of_compactSpace
    (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
  letI : IsNoetherian (pullback.diagonal f).ker.normalCone := {}
  finiteSmoothSectionCoordinates A N
    (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
    (pullback.diagonal f).normalConeZeroSection

/-- In rank zero the integration is the identity-adjunction trace. Its adjunct is the
vector-bundle purity map; invert it and restrict by the zero section. The actual normal
cone is transported to (X,1_X) by its projection and zero section, using the exceptional
base-change mate. Thus this formula retains the canonical geometric transport.
Source: def-amb-vector-integration, rank-zero local trace; thm-amb-vector-bundle-purity;
the item's proof Step 7 (blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothRankZeroFactor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f] (G : FiniteSmoothGammaData A f) :
    finiteSmoothNormalInvariant A f G ⟶
      MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A X) := by
  letI := G.normalIso
  let π := Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f)
  let z := (pullback.diagonal f).normalConeZeroSection
  have hz : z ≫ π = 𝟙 X :=
    Scheme.Hom.normalConeZeroSection_normalConeProj (pullback.diagonal_fst f)
  let sq : IsPullback z (𝟙 X) π (𝟙 X) := IsPullback.of_vert_isIso ⟨by simpa using hz⟩
  exact (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).inv.app _ ≫
    NoetherianSectionSpecialization.sectionMap A π (𝟙 X) (𝟙 X) z sq z (𝟙 X)
      (by simp) ≫
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).hom.app _ ≫
    ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) (𝟙 X)).rightAdjointUniq
      (Adjunction.id.ofNatIsoLeft (unboundedEtaleLowerShriekId A X).symm)).hom.app _

/-- Gamma is the canonical smooth tensor map after the inverse three-factor orientation.
Source: sk-thm-smooth-purity, displayed gamma formula
(blueprint: lem-pur-finite-smooth-gamma-normalization). -/
def finiteSmoothGammaMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (α : dualizingComplex (ModuleCat.{u + 1} A) f ≅
      MonoidalCategoryStruct.tensorUnit (DerivedCategoryModule A X))
    (K : DerivedCategoryModule A Y) :
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K :=
  (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).inv ≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).map α.inv ≫
    smoothTensorDualityMap (ModuleCat.{u + 1} A) f
      (isIso_projectionMap_of_finite A f) K

/-- Every factor of the geometric orientation is the identity in the specified
adjunction-preserving coordinates. Gamma is rho inverse, and its adjunct is precisely
the sum/evaluation counit transported by the graph-normalized comparison.
Source: sk-thm-smooth-purity, three-factor formula at d=0
(blueprint: lem-pur-finite-smooth-gamma-normalization).

Proof:
1. Use quasifiniteCompactSupportExact and etaleSupportMapCompatibility to identify R e_!
   with exact sum extension by graph extension and the total-derived unit. Transport the
   sum adjunction and apply the Hom bijections to its counit. Adjoint uniqueness gives rho
   and the counit equation, including omega_e = A_V in these coordinates.
2. The etale diagonal is a clopen section of p_1. Its ideal is zero on its image and the
   unit ideal on its complement V_0. It is regular of codimension zero, and the actual
   normal projection is an isomorphism with zero section its inverse.
3. The specified compact-support exchange becomes the sum exchange. The latter's
   unit--exchange--counit formula and both triangle identities identify the exceptional
   mate with the pullback compositor. Restrict by Delta: the first coordinate equation.
4. Compute the actual Rees algebra on both clopen pieces: O_X[t] and O_{V_0}[t,t^-1].
   Thus D = A1_X disjoint union (V_0 times Gm), preserving parameter and section. The
   fibres are (W,Delta) at one and (X,id) at zero.
5. These spaces and maps are Noetherian, separated, etale and finite type. Open-subscheme
   and base-change permanence give these assertions on the punctured second component;
   Nagata supplies compactifiability, including that required by the deformation family.
6. In the coordinates of Step 1 the family and both specified fibre mates are constant
   identities. Uniqueness of kappa normalized at one therefore makes its zero reading
   the identity: the second coordinate equation.
7. Rank-zero integration is the identity trace and its purity adjunct is the identity.
   Transport through the actual normal projection and zero section gives the third
   coordinate equation. The composite orientation is consequently rho at the unit.
8. The specified projection map becomes the sum projection, on a generator sending
   (s,m) tensor k to (s,m tensor s^*k). Its inverse uses the natural signed symmetry;
   on the coefficient unit in degree zero that sign is one. Sum extension preserves
   flat and K-flat complexes, so the calculation descends for all unbounded K.
9. Under rho, the transpose of the canonical tensor map is tensoring with evaluation
   and then evaluating. Insert alpha inverse: on every summand the result is precisely
   evaluation. Adjunction bijectivity gives gamma = rho inverse, and its displayed
   adjunct is the actual sum counit, with the exact/left-derived inverse-image transport.
-/
theorem finite_smooth_gamma_normalization
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : ∀ x : X, IsUnit (ell : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y))
    (f : X ⟶ Y) [Etale f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (N : FiniteSmoothCompactSupportComparisons (NoetherianSectionSpecialization.Coeff ell n))
    (hN : FiniteSmoothComparisonNormalized (NoetherianSectionSpecialization.Coeff ell n) N) :
    ∃ (G : FiniteSmoothGammaData (NoetherianSectionSpecialization.Coeff ell n) f)
      (α : dualizingComplex (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n)) f ≅
        MonoidalCategoryStruct.tensorUnit
          (DerivedCategoryModule (NoetherianSectionSpecialization.Coeff ell n) X)),
      α.hom = finiteSmoothDiagonalFactor _ f ≫ finiteSmoothDeformationFactor _ f G ≫
        finiteSmoothRankZeroFactor _ f G ∧
      finiteSmoothDiagonalFactor _ f ≫
          (finiteSmoothSectionCoordinates _ N (pullback.fst f f) (pullback.diagonal f)).hom =
        (finiteSmoothOmegaCoordinates _ N f).hom ∧
      finiteSmoothDeformationFactor _ f G ≫ (finiteSmoothNormalCoordinates _ N f G).hom =
        (finiteSmoothSectionCoordinates _ N (pullback.fst f f) (pullback.diagonal f)).hom ∧
      finiteSmoothRankZeroFactor _ f G = (finiteSmoothNormalCoordinates _ N f G).hom ∧
      α = finiteSmoothOmegaCoordinates _ N f ∧
      ∀ K : DerivedCategoryModule (NoetherianSectionSpecialization.Coeff ell n) Y,
        finiteSmoothGammaMap _ f α K = (finiteSmoothAdjointCoordinates _ N f).inv.app K ∧
        ((rightDerivedUpperShriekAdjunction
          (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n)) f).homEquiv _ K).symm
            (finiteSmoothGammaMap _ f α K) =
          (finiteSmoothSumComparison _ N f).hom.app _ ≫
            (etaleLowerShriek
              (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n)) f
              inferInstance).mapDerivedCategory.map
                ((leftDerivedUpperStarIsoMapDerivedCategory
                  (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n)) f).hom.app K) ≫
            ((etaleLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n)) f
              inferInstance).mapDerivedCategoryAdjunction).counit.app K := by
  sorry

end AlgebraicGeometry.Etale
