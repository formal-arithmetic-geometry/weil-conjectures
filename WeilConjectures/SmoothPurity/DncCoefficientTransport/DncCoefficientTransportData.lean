/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization

/-! # Coefficient transport for the actual deformation family

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity/
sk-thm-smooth-purity-general-ring.proof.md, Proof (2)
(blueprint: lem-pur-dnc-coefficient-transport).

Finite constructible objects are written in their ordinary etale-origin presentation.
The specified `reductionSite` realizes them in the ordinary uncompleted pro-etale
constant-ring category. Both coefficient rings have their own exceptional inverse image:
no B-object is defined by scalar-extending the corresponding R-object.
- Counit-characterized coefficient maps use `ExceptionalCoefficients.mateMap`.
- Fibre maps, normalization and specialization use the published Rees-family maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures
namespace DncCoefficientTransport

/-- The canonical coefficient map on relative dualizing objects: transpose the
scalar-extended counit, then identify the extended unit with the B-unit.
Source: Proof (2), Step 1; det-sp-reduction-exceptional
(blueprint: lem-pur-dnc-coefficient-transport). -/
def dualizingMap {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] :
    (Etale.scalarExtension φ V).obj (Etale.dualizingComplex A g) ⟶
      Etale.dualizingComplex B g :=
  Etale.ExceptionalCoefficients.mateMap φ g (𝟙_ _) ≫
    (Etale.rightDerivedUpperShriek B g).map
      (Etale.ExceptionalCoefficients.unitIso φ S).hom

/-- The actual section coefficient map: balancing for Ls* followed by Ls*(c_g).
Source: Proof (2), Step 1 (blueprint: lem-pur-dnc-coefficient-transport). -/
def sectionMap {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g]
    (s : S ⟶ V) :
    (Etale.scalarExtension φ S).obj (Etale.sectionInvariant A g s) ⟶
      Etale.sectionInvariant B g s :=
  (Etale.scalarPullbackIso φ s).inv.app _ ≫
    (Etale.upperStar (ModuleCat.{u + 1} B) s).leftDerivedFunctor.map (dualizingMap φ g)

/-- The genuine B-coefficient section object in the uncompleted pro-etale category.
This is the canonical site realization of Ls* g_B^! B_S, formed using g_B^!.
Source: Proof (2), definition of C_D (blueprint: lem-pur-dnc-coefficient-transport). -/
def sectionObject (A : Type u) [CommRing A] [Finite A]
    {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] (s : S ⟶ V) :
    proEtaleDerivedCategory S A :=
  (ProEtale.reductionSite A S).obj (Etale.sectionInvariant (ULift.{u + 1, u} A) g s)

/-- The actual pro-etale coefficient map, with the fixed site/scalar comparison.
Source: Proof (2), q_(g,s) (blueprint: lem-pur-dnc-coefficient-transport). -/
def realizedSectionMap {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g]
    (s : S ⟶ V) :
    (ProEtale.scalarExtensionFunctor φ S).obj (sectionObject A g s) ⟶
      sectionObject B g s :=
  (ProEtale.reductionSiteScalarIso φ S).hom.app _ ≫
    (ProEtale.reductionSite B S).map (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s)

/-- Scalar compatibility with both canonical exceptional fibre mates of the Rees family.
Source: Proof (2), Step 2 (blueprint: lem-pur-dnc-coefficient-transport). -/
def FibreCompatibility {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {V S : Scheme.{u}}
    (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] : Prop :=
  ((Etale.scalarPullbackIso φ (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).inv.app
        (Etale.NoetherianSectionSpecialization.family A g s) ≫
      (Etale.upperStar (ModuleCat.{u + 1} B)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map
          (sectionMap φ (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection) ≫
      Etale.NoetherianSectionSpecialization.atOne B g s hs =
    (Etale.scalarExtension φ S).map (Etale.NoetherianSectionSpecialization.atOne A g s hs) ≫
      sectionMap φ g s) ∧
  ((Etale.scalarPullbackIso φ (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).inv.app
        (Etale.NoetherianSectionSpecialization.family A g s) ≫
      (Etale.upperStar (ModuleCat.{u + 1} B)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map
          (sectionMap φ (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection) ≫
      Etale.NoetherianSectionSpecialization.atZero B g s =
    (Etale.scalarExtension φ S).map (Etale.NoetherianSectionSpecialization.atZero A g s) ≫
      sectionMap φ (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection)

/-- Naturality for etale localization of pairs, using the specified exceptional mate.
Source: Proof (2), Steps 2--3 (blueprint: lem-pur-dnc-coefficient-transport). -/
def LocalizationCompatibility {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {V S : Scheme.{u}}
    (g : V ⟶ S) [HasCompactification g] (s : S ⟶ V) : Prop :=
  ∀ {V' S' : Scheme.{u}} (g' : V' ⟶ S') [HasCompactification g'] [QuasiCompact g']
    (b : S' ⟶ S) [AlgebraicGeometry.Etale b] (v : V' ⟶ V)
    (sq : IsPullback v g' g b) (s' : S' ⟶ V') (hsection : s' ≫ v = b ≫ s),
    (Etale.scalarPullbackIso φ b).inv.app (Etale.sectionInvariant A g s) ≫
        (Etale.upperStar (ModuleCat.{u + 1} B) b).leftDerivedFunctor.map (sectionMap φ g s) ≫
        Etale.NoetherianSectionSpecialization.sectionMap B g g' b v sq s s' hsection =
      (Etale.scalarExtension φ S').map
          (Etale.NoetherianSectionSpecialization.sectionMap A g g' b v sq s s' hsection) ≫
        sectionMap φ g' s'

/-- The direct constant-family coordinate comparison. After restriction to any etale
base chart on which the family has a constant model, the normalized global comparison
is the identity on that model, read through its value at one.
Source: Proof (2), Step 6 (blueprint: lem-pur-dnc-coefficient-transport). -/
def CoordinateNormalization (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    (h1 : IsIso (Etale.NoetherianSectionSpecialization.atOne A g s hs))
    (κ : Etale.NoetherianSectionSpecialization.family A g s ≅
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (Etale.sectionInvariant A g s)) : Prop :=
  ∀ {S' : Scheme.{u}} (b : S' ⟶ S) [AlgebraicGeometry.Etale b]
    [IsSeparated b] [QuasiCompact b] (C0 : Etale.DerivedCategoryModule A S')
    (e : (Etale.upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj
        (Etale.NoetherianSectionSpecialization.family A g s) ≅
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.obj C0),
    (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.map κ.hom ≫
      (Etale.NoetherianSectionSpecialization.linePullback A b
        (Etale.sectionInvariant A g s)).hom ≫
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.map
          (Etale.sectionRestrictionIso (ModuleCat.{u + 1} A) b
            (AffineSpace.map (ULift.{u} (Fin 1)) b)
            (AffineSpace.oneSection_comp_map b)
            (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S')
            (@asIso _ _ _ _ (Etale.NoetherianSectionSpecialization.atOne A g s hs) h1)
            e).hom = e.hom

/-- The normalized B-family comparison and its specialization equation, with uniqueness
among all normalized isomorphisms, not just among coefficient-compatible choices.
Source: Proof (2), Steps 4--7 (blueprint: lem-pur-dnc-coefficient-transport). -/
def NormalizedTransport {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {V S : Scheme.{u}}
    (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] : Prop :=
  ∀ κR : Etale.NoetherianSectionSpecialization.family A g s ≅
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (Etale.sectionInvariant A g s),
    Etale.NoetherianSectionSpecialization.Normalized A g s hs κR →
    ∃ κB : Etale.NoetherianSectionSpecialization.family B g s ≅
        (Etale.upperStar (ModuleCat.{u + 1} B)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
            (Etale.sectionInvariant B g s),
      Etale.NoetherianSectionSpecialization.Normalized B g s hs κB ∧
      (∀ κ, Etale.NoetherianSectionSpecialization.Normalized B g s hs κ → κ = κB) ∧
      (sectionMap φ (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection ≫ κB.hom =
        (Etale.scalarExtension φ (AffineSpace (ULift.{u} (Fin 1)) S)).map κR.hom ≫
          (Etale.scalarPullbackIso φ (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).inv.app _ ≫
          (Etale.upperStar (ModuleCat.{u + 1} B)
            (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.map (sectionMap φ g s)) ∧
      (∀ h1 : IsIso (Etale.NoetherianSectionSpecialization.atOne B g s hs),
        CoordinateNormalization B g s hs h1 κB) ∧
      IsIso (Etale.NoetherianSectionSpecialization.specialization B g s κB) ∧
      (sectionMap φ g s ≫ Etale.NoetherianSectionSpecialization.specialization B g s κB =
        (Etale.scalarExtension φ S).map
            (Etale.NoetherianSectionSpecialization.specialization A g s κR) ≫
          sectionMap φ (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection)

/-- Arbitrary-base-change coefficient square, without imposing any section on g0.
All morphisms remain in the separated finite-type k-setting.
Source: Proof (2), Step 2 (blueprint: lem-pur-dnc-coefficient-transport). -/
def MixedBaseChange (D : FiniteFieldDatum.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) : Prop :=
  ∀ (V S S' : Over (Spec (.of D.k)))
    [IsSeparated V.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [IsSeparated S.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [IsSeparated S'.hom] [LocallyOfFiniteType S'.hom] [QuasiCompact S'.hom]
    (g : V ⟶ S) (r : ℕ) [SmoothOfRelativeDimension r g.left]
    [HasCompactification g.left] [QuasiCompact g.left] (h : S' ⟶ S),
    IsIso (Etale.smoothDualizingBaseChangeMap A g.left h.left) ∧
      IsIso (Etale.smoothDualizingBaseChangeMap B g.left h.left) ∧
      Etale.ExceptionalCoefficients.BaseChangeCompatibility φ g.left h.left (𝟙_ _)

/-- The counit-normalized chart equation, including the standard coordinate pair.
The right-adjoint comparisons are fixed by etale summation and ordered affine trace;
the model coefficient map is the canonical root-normalized Tate reassociation.
Source: Proof (2), Step 3 (blueprint: lem-pur-dnc-coefficient-transport). -/
def ChartCompatibility (D : FiniteFieldDatum.{u}) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) (N : ℕ) : Prop :=
  ∀ (V S : Over (Spec (.of D.k)))
    [IsSeparated V.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [IsSeparated S.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [IsNoetherian V.left] [IsNoetherian S.left]
    (g : V ⟶ S) [HasCompactification g.left] (d : ℕ)
    [SmoothOfRelativeDimension d g.left]
    {U : Scheme.{u}} [IsNoetherian U] (i : U ⟶ V.left) [IsOpenImmersion i]
    (e : U ⟶ affineTraceTower S.left d) [AlgebraicGeometry.Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ g.left = e ≫ affineTraceProjection S.left d)
    (MA : Etale.EtaleCompactSupportNormalization A)
    (MB : Etale.EtaleCompactSupportNormalization B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (tA : Etale.OrdinaryFiniteTwistTransport A N hA)
    (tB : Etale.OrdinaryFiniteTwistTransport B N hB)
    (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA tA T hT)
    (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum B N hB tB T hT)
    (hS : IsUnit (N : Γ(S.left, ⊤))),
    (Etale.scalarExtension φ U).map
        ((ProEtale.reductionEtaleChartRightIso A MA g.left i d e he
          (HasCompactification.compactification g.left)
          (Etale.rightDerivedUpperShriek A g.left)
          (Etale.rightDerivedUpperShriekAdjunction A g.left)
          N hA tA PA hS).hom.app (𝟙_ _)) ≫
      (ProEtale.reductionEtaleChartScalarIso φ N hA hB hS d e (𝟙_ _)).hom ≫
      (Etale.affineTraceRight B N hB S.left d ⋙ Etale.ordinaryFinitePullback B e).map
        (Etale.ExceptionalCoefficients.unitIso φ S.left).hom =
    (Etale.scalarPullbackIso φ i).inv.app
        (Etale.dualizingComplex A g.left) ≫
      (Etale.ordinaryFinitePullback B i).map (dualizingMap φ g.left) ≫
      (ProEtale.reductionEtaleChartRightIso B MB g.left i d e he
        (HasCompactification.compactification g.left)
        (Etale.rightDerivedUpperShriek B g.left)
        (Etale.rightDerivedUpperShriekAdjunction B g.left)
        N hB tB PB hS).hom.app (𝟙_ _)

/-- Geometric domain facts for the actual Rees family and its actual normal cone.
These are proof data only; no replacement deformation space is selected.
Source: sk-lem-geometry, Proof (2) Step 1
(blueprint: lem-pur-dnc-coefficient-transport). -/
structure Geometry {V S : Scheme.{u}} (g : V ⟶ S) (s : S ⟶ V) : Prop where
  compact : HasCompactification g
  compactFamily : HasCompactification (Scheme.Hom.deformationSpaceProj g s)
  compactNormal : HasCompactification (Scheme.Hom.normalConeProj g s)
  quasiCompactNormal : QuasiCompact (Scheme.Hom.normalConeProj g s)

end DncCoefficientTransport
end WeilConjectures
