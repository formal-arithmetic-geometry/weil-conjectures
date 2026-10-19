/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.NoetherianEtaleSectionSpecialization
public import Sheaf.SecSmoothPurity.ReductionExceptional
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.PurityAffineLineComponents
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.PurLisseMorphismRigidity
import Sheaf.Paper.PurityDncComparisons
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SecSmoothPurity.MixedBaseChange
import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
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
set_option warn.sorry false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures
namespace DncCoefficientTransport

/-- The coefficient ring Z/(ell^n), lifted only for size.
Source: Proof (2), R=Z/ell^n (blueprint: lem-pur-dnc-coefficient-transport). -/
abbrev BaseRing (ell n : ℕ) : Type u := ULift.{u} (ZMod (ell ^ n))

/-- The positive prime-power coefficient ring is finite, including n=0.
Source: Proof (2), finite coefficient convention
(blueprint: lem-pur-dnc-coefficient-transport). -/
instance baseRingFinite (ell n : ℕ) [Fact ell.Prime] : Finite (BaseRing.{u} ell n) :=
  letI : NeZero (ell ^ n) := ⟨ne_of_gt (pow_pos (Fact.out : ell.Prime).pos n)⟩
  inferInstance

/-- The canonical coefficient map on relative dualizing objects: transpose the
scalar-extended counit, then identify the extended unit with the B-unit.
Source: Proof (2), Step 1; det-sp-reduction-exceptional
(blueprint: lem-pur-dnc-coefficient-transport). -/
def dualizingMap {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V S : Scheme.{u}} (g : V ⟶ S) [HasCompactification g] :
    (Etale.scalarExtension φ V).obj (Etale.dualizingComplex (ModuleCat.{u + 1} A) g) ⟶
      Etale.dualizingComplex (ModuleCat.{u + 1} B) g :=
  Etale.ExceptionalCoefficients.mateMap φ g (𝟙_ _) ≫
    (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} B) g).map
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
          (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) g.left)
          (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) g.left)
          N hA tA PA hS).hom.app (𝟙_ _)) ≫
      (ProEtale.reductionEtaleChartScalarIso φ N hA hB hS d e (𝟙_ _)).hom ≫
      (Etale.affineTraceRight B N hB S.left d ⋙ Etale.ordinaryFinitePullback B e).map
        (Etale.ExceptionalCoefficients.unitIso φ S.left).hom =
    (Etale.scalarPullbackIso φ i).inv.app
        (Etale.dualizingComplex (ModuleCat.{u + 1} A) g.left) ≫
      (Etale.ordinaryFinitePullback B i).map (dualizingMap φ g.left) ≫
      (ProEtale.reductionEtaleChartRightIso B MB g.left i d e he
        (HasCompactification.compactification g.left)
        (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} B) g.left)
        (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) g.left)
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

/-- The domain facts follow from the source hypotheses, rather than being additional
hypotheses of the coefficient theorem.
Source: Proof (2) Step 1, sk-lem-geometry (blueprint: lem-pur-dnc-coefficient-transport).
Proof: finite type over the field makes S and V Noetherian. A closed section of a
smooth relative-dimension d map is regular of codimension d. On its extended-Rees
charts x_i=t*u_i the deformation projection is smooth of dimension d; its zero
fibre is the actual rank-d normal bundle. The projections are separated finite type,
and Nagata gives the three coefficient-independent compactifications. -/
theorem geometry (D : FiniteFieldDatum.{u}) {V S : Scheme.{u}}
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aS : S ⟶ Spec (.of D.k)) [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) : Geometry g s := by
  sorry

/-- The complete finite coefficient transport assertion in canonical coordinates.
Source: Proof (2), all clauses (blueprint: lem-pur-dnc-coefficient-transport). -/
def Assertions (D : FiniteFieldDatum.{u}) (ell n : ℕ) [Fact ell.Prime]
    {V S : Scheme.{u}} (g : V ⟶ S) [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (G : Geometry g s) {B : Type u} [CommRing B] [Finite B]
    (φ : BaseRing.{u} ell n →+* B) : Prop := by
  letI := G.compact
  letI := G.compactFamily
  letI := G.compactNormal
  letI := G.quasiCompactNormal
  exact
    IsIso (realizedSectionMap φ g s) ∧
    IsIso (realizedSectionMap φ (Scheme.Hom.deformationSpaceProj g s)
      s.deformationSpaceSection) ∧
    IsIso (realizedSectionMap φ (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection) ∧
    IsIso (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s) ∧
    IsIso (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) (Scheme.Hom.deformationSpaceProj g s)
      s.deformationSpaceSection) ∧
    IsIso (sectionMap (RingHom.ulift.{u + 1, u + 1, u, u} φ) (Scheme.Hom.normalConeProj g s)
      s.normalConeZeroSection) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atOne
      (ULift.{u + 1, u} (BaseRing.{u} ell n)) g s hs) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atZero
      (ULift.{u + 1, u} (BaseRing.{u} ell n)) g s) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atOne (ULift.{u + 1, u} B) g s hs) ∧
    IsIso (Etale.NoetherianSectionSpecialization.atZero (ULift.{u + 1, u} B) g s) ∧
    (∃! κR : Etale.NoetherianSectionSpecialization.family
        (ULift.{u + 1, u} (BaseRing.{u} ell n)) g s ≅
        (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (BaseRing.{u} ell n)))
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
            (Etale.sectionInvariant (ULift.{u + 1, u} (BaseRing.{u} ell n)) g s),
      Etale.NoetherianSectionSpecialization.Normalized
        (ULift.{u + 1, u} (BaseRing.{u} ell n)) g s hs κR) ∧
    FibreCompatibility (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s hs ∧
    LocalizationCompatibility (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s ∧
    MixedBaseChange D (RingHom.ulift.{u + 1, u + 1, u, u} φ) ∧
    ChartCompatibility D (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ell ^ n) ∧
    NormalizedTransport (RingHom.ulift.{u + 1, u + 1, u, u} φ) g s hs

end DncCoefficientTransport

/-- Coefficient transport for the actual smooth-section deformation family.
Source: Proof (2), sk-thm-smooth-purity-general-ring
(blueprint: lem-pur-dnc-coefficient-transport).
Proof, in the seven DAG steps:
1. At E=Q_ell identify the positive finite coefficient ring with Z/ell^n. Apply
   det-sp-reduction-exceptional to g, the actual Rees deformation projection, and
   the actual normal projection. Pull its counit transpose back to the sections
   using lem-weil-pbc-ringed-topoi-derived-tensor-pullback to obtain the defined q maps.
2. Apply det-sp-mixed-base-change at the coefficient unit. Its square gives the
   arbitrary-base-change equation without a section on g0. Apply it to i1 and i0
   and compose the section pullbacks to obtain both displayed fibre equations.
3. On centered etale charts x_i=t*u_i, the counit is the etale fibre sum followed
   by the ordered affine trace. det-sp-reduction-exceptional therefore computes q
   as canonical Tate-line reassociation, x tensor b mapping to bx. The scalar and
   pullback identifications in det-sp-scalar-extension-functor and
   lem-asd-etale-finite-twist-pullback prove localization and the standard-pair value.
4. Scalar-extend the R-family comparison of prop-pur-dnc-family-constancy and
   conjugate by qF and a*q. The one-fibre equation cancels these q maps at t=1.
5. Remove the common shift [2d] from the finite locally constant B-lines and use
   lem-weil-pbc-derived-single-fully-faithful. On restriction to R the sheaves
   remain finite locally constant, even for a nonflat B. The section t=1 meets
   every affine-line component (lem-pur-a1-components). The difference of two
   normalized maps is zero there and hence everywhere by lem-pur-lisse-morphism-rigidity.
   For empty S all maps are unique.
6. The local constant-family comparison on each centered coordinate chart is
   normalized at one, so Step 5 identifies it with kappaB. Glue using
   lem-pur-sheaf-hom-cover-gluing after removing the common shift.
7. Restrict the conjugation equation at zero and apply the zero-fibre square.
   Invert i0*kappa to get deltaB q = qNormal (deltaR)_B. The same formulas include
   d=0, empty bases and B=0; no flatness assumption on the ring map is used. -/
theorem dncCoefficientTransport (D : FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p) (n : ℕ) (hn : 1 ≤ n)
    {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (aS : S ⟶ Spec (.of D.k)) [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    {B : Type u} [CommRing B] [Finite B]
    (φ : DncCoefficientTransport.BaseRing.{u} ell n →+* B) :
    DncCoefficientTransport.Assertions D ell n g s hs
      (DncCoefficientTransport.geometry D d g aS s hs) φ := by
  sorry

end WeilConjectures
