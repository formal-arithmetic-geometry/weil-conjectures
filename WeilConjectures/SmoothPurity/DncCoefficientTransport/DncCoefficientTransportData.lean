/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation

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
