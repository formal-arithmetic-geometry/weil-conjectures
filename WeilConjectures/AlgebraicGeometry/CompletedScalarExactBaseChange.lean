/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.FlatScalarRealization
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.SiteDerivedConstantModuleFunctor
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.ConstantLeftModuleInverseImage
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.CategoryTheory.ScalarInverseImageTowerDiagram
import WeilConjectures.SixFunctors.GeometricInverseImageConstantModuleSupplement

/-! # Exact completed scalar realization and ordinary balanced pullback

Source: Stacks Tags 093J, 093M, 03D7 and 03EL
(blueprint: lem-a1-completed-scalar-exact-base-change).
The equivalent small site retains all bounded pro-etale objects. The independent
parameters t and u permit arbitrary enlargement of sites and coefficients.
Positive exponents are indexed by n+1; the exponent-zero quotient is zero.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u uA vA uB vB w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace AlgebraicGeometry.CompletedScalar

/-- An equivalent small pro-etale site in the common ambient universe.
Source: Stacks 09A5; size convention
(blueprint: lem-a1-completed-scalar-exact-base-change). -/
abbrev Site (T : Scheme.{t}) := AsSmall.{max (t + 1) u} T.ProEt

/-- The topology transported from the actual small pro-etale site.
Source: Stacks 09A5 (blueprint: lem-a1-completed-scalar-exact-base-change). -/
abbrev topology (T : Scheme.{t}) : GrothendieckTopology (Site.{t, u} T) :=
  (AsSmall.down : Site.{t, u} T ⥤ T.ProEt).inducedTopology (Scheme.ProEt.topology T)

/-- Base change on the equivalent sites, without a restriction on g.
Source: Stacks 09A5 (blueprint: lem-a1-completed-scalar-exact-base-change). -/
abbrev baseChange {X Y : Scheme.{t}} (g : X ⟶ Y) : Site.{t, u} Y ⥤ Site.{t, u} X :=
  AsSmall.down ⋙ Scheme.proEtaleBaseChange g ⋙ AsSmall.up

/-- Base change is continuous on the transported sites.
Source: Stacks 09A5 (blueprint: lem-a1-completed-scalar-exact-base-change).
Proof: equivalences transport the topology, and pro-etale base change is continuous. -/
@[instance] theorem baseChange_continuous {X Y : Scheme.{t}} (g : X ⟶ Y) :
    (baseChange.{t, u} g).IsContinuous (topology.{t, u} Y) (topology.{t, u} X) := by
  sorry

variable (R : Type (max (t + 1) u)) [CommRing R] (I : Ideal R)

/-- The existing constant ring, with its canonical sheafification unit.
Source: Stacks 093J (blueprint: lem-a1-completed-scalar-exact-base-change). -/
abbrev constant (T : Scheme.{t}) := ConstantCompletion.constant (topology.{t, u} T) R

/-- The existing inverse limit of the constant positive-power quotient rings.
Source: Stacks 093M (blueprint: lem-a1-completed-scalar-exact-base-change). -/
abbrev completed (T : Scheme.{t}) := ConstantCompletion.completed (topology.{t, u} T) R I

/-- The existing scalar map, determined by the quotient projections.
Source: Stacks 093M (blueprint: lem-a1-completed-scalar-exact-base-change). -/
abbrev scalar (T : Scheme.{t}) := ConstantCompletion.coefficientMap (topology.{t, u} T) R I

/-- The canonical constant-section comparison, extended by sheafification.
Source: Stacks 0H7J (blueprint: lem-a1-completed-scalar-exact-base-change). -/
def rho {X Y : Scheme.{t}} (g : X ⟶ Y) (A : CommRingCat.{max (t + 1) u}) :
    (constantSheaf (topology.{t, u} Y) CommRingCat).obj A ⟶
      ((baseChange.{t, u} g).sheafPushforwardContinuous CommRingCat
        (topology.{t, u} Y) (topology.{t, u} X)).obj
          ((constantSheaf (topology.{t, u} X) CommRingCat).obj A) :=
  ((sheafificationAdjunction (topology.{t, u} Y) CommRingCat).homEquiv _ _).symm
    (Functor.whiskerLeft (baseChange g).op
      (toSheafify (topology.{t, u} X) ((Functor.const (Site.{t, u} X)ᵒᵖ).obj A)))

/-- Constant-section comparisons commute with every scalar map, hence all quotient maps.
Source: Stacks 093J (blueprint: lem-a1-completed-scalar-exact-base-change).
Proof (node step 1): precompose with the sheafification unit. Both maps send a to its
constant section with value f(a). Uniqueness of sheafification proves equality. -/
theorem rho_natural {X Y : Scheme.{t}} (g : X ⟶ Y)
    {A B : CommRingCat.{max (t + 1) u}} (f : A ⟶ B) :
    (constantSheaf (topology.{t, u} Y) CommRingCat).map f ≫ rho g B =
      rho g A ≫ ((baseChange g).sheafPushforwardContinuous CommRingCat
        (topology.{t, u} Y) (topology.{t, u} X)).map
          ((constantSheaf (topology.{t, u} X) CommRingCat).map f) := by
  sorry

/-- The unique direct-image coefficient map with its specified finite projections.
Source: Stacks 03DB, 093M (blueprint: lem-a1-completed-scalar-exact-base-change).
Proof (node step 2): direct image and the ring limit are sectionwise. Apply rho_natural
to every quotient transition. The compatible maps rho_Q composed with projections
therefore give a unique map into the target limit; all operations are coordinatewise. -/
theorem directMap_existsUnique {X Y : Scheme.{t}} (g : X ⟶ Y) :
    ∃! d : completed R I Y ⟶
      ((baseChange g).sheafPushforwardContinuous CommRingCat
        (topology.{t, u} Y) (topology.{t, u} X)).obj (completed R I X),
      ∀ n : ℕ,
        d ≫ ((baseChange g).sheafPushforwardContinuous CommRingCat
          (topology.{t, u} Y) (topology.{t, u} X)).map
            (ConstantCompletion.projection (topology.{t, u} X) R I n) =
        ConstantCompletion.projection (topology.{t, u} Y) R I n ≫
          rho g (CommRingCat.of (R ⧸ I ^ (n + 1))) := by
  sorry

/-- The uniquely determined ring map; only its proof, not its data, is postponed.
Source: Stacks 03DB (blueprint: lem-a1-completed-scalar-exact-base-change). -/
def directMap {X Y : Scheme.{t}} (g : X ⟶ Y) :=
  (directMap_existsUnique R I g).exists.choose

/-- The canonical inverse-image ring functor in the enlarged coefficient universe.
Source: Stacks 00VC (blueprint: lem-a1-completed-scalar-exact-base-change). -/
abbrev inverse {X Y : Scheme.{t}} (g : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafPullback (baseChange.{t, u} g)
    CommRingCat.{max (t + 1) u} (topology.{t, u} Y) (topology.{t, u} X)

/-- The associated ring-sheaf adjunction, with the specified Kan/sheafification left side.
Source: Stacks 00VC (blueprint: lem-a1-completed-scalar-exact-base-change). -/
abbrev ringAdjunction {X Y : Scheme.{t}} (g : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (baseChange.{t, u} g)
    CommRingCat.{max (t + 1) u} (topology.{t, u} Y) (topology.{t, u} X)

/-- The adjoint completed coefficient map c_g.
Source: Stacks 03D2 (blueprint: lem-a1-completed-scalar-exact-base-change). -/
def coefficientMap {X Y : Scheme.{t}} (g : X ⟶ Y) :=
  ((ringAdjunction g).homEquiv _ _).symm (directMap R I g)

/-- Projection characterization, scalar square, and the constant-ring identification.
Source: Stacks 03D2, 093M (blueprint: lem-a1-completed-scalar-exact-base-change).
Proof (node steps 1--2): the adjunct of rho_R is the constant-ring isomorphism.
Adjunction naturality gives the finite projection formula. For the scalar square,
postcompose its direct-image version with every finite projection, use rho_natural,
and then use the limit universal property. Take adjuncts to obtain the displayed square. -/
theorem coefficientMap_properties {X Y : Scheme.{t}} (g : X ⟶ Y) :
    IsIso (((ringAdjunction g).homEquiv _ _).symm (rho g (CommRingCat.of R))) ∧
    (∀ n : ℕ, coefficientMap R I g ≫ ConstantCompletion.projection (topology.{t, u} X) R I n =
      (inverse g).map (ConstantCompletion.projection (topology.{t, u} Y) R I n) ≫
        ((ringAdjunction g).homEquiv _ _).symm
          (rho g (CommRingCat.of (R ⧸ I ^ (n + 1))))) ∧
    (inverse g).map (scalar R I Y) ≫ coefficientMap R I g =
      ((ringAdjunction g).homEquiv _ _).symm (rho g (CommRingCat.of R)) ≫ scalar R I X := by
  sorry

/-- The completed ring with commutativity forgotten, for Mathlib module sheaves.
Source: Stacks 03D1 (blueprint: lem-a1-completed-scalar-exact-base-change). -/
abbrev rings (T : Scheme.{t}) :=
  (sheafCompose (topology.{t, u} T) (forget₂ CommRingCat RingCat)).obj (completed R I T)

/-- The actual direct-image map with commutativity forgotten.
Source: Stacks 03D1 (blueprint: lem-a1-completed-scalar-exact-base-change). -/
def moduleMap {X Y : Scheme.{t}} (g : X ⟶ Y) :
    rings R I Y ⟶ ((baseChange g).sheafPushforwardContinuous RingCat
      (topology.{t, u} Y) (topology.{t, u} X)).obj (rings R I X) :=
  ⟨Functor.whiskerRight (directMap R I g).hom (forget₂ CommRingCat RingCat)⟩

/-- The published independent-universe theorem supplies the module right adjoint.
Source: Stacks 03D7 (blueprint: lem-a1-completed-scalar-exact-base-change). -/
instance pushforward_rightAdjoint {X Y : Scheme.{t}} (g : X ⟶ Y) :
    (SheafOfModules.pushforward.{max (t + 1) u} (moduleMap R I g)).IsRightAdjoint :=
  SheafOfModules.module_pushforward_isRightAdjoint_of_universes (moduleMap R I g)

/-- Ordinary ringed pullback, the canonical left adjoint to module direct image.
Source: Stacks 03D7, 03EL (blueprint: lem-a1-completed-scalar-exact-base-change). -/
abbrev pullback {X Y : Scheme.{t}} (g : X ⟶ Y) :=
  SheafOfModules.pullback.{max (t + 1) u} (moduleMap R I g)

/-- The published scalar-realization functor, for every R-module.
Source: Stacks 093J, 093M (blueprint: lem-a1-completed-scalar-exact-base-change). -/
abbrev realization (T : Scheme.{t}) :=
  SheafOfModules.flatScalarRealization.{max (t + 1) u, max (t + 1) u}
    (topology.{t, u} T) (scalar R I T)

/-- Additivity and exactness for all modules, with no finite-generation condition.
Source: Stacks 093J, 093M (blueprint: lem-a1-completed-scalar-exact-base-change).
Proof (node step 4): 093M makes the completion flat over the constant ring. Thus scalar
extension is exact. Compose with the exact constant-module functor of 093J. Tensor and
sheafification preserve addition. All of these statements hold on the equivalent site. -/
theorem realization_exact [IsNoetherianRing R] (T : Scheme.{t}) :
    (realization R I T).Additive ∧ PreservesFiniteLimits (realization R I T) ∧
      PreservesFiniteColimits (realization R I T) := by
  sorry

/-- Left exactness supplies the canonical cycle comparison.
Source: Stacks 010N (blueprint: lem-a1-completed-scalar-exact-base-change). -/
instance realization_limits [IsNoetherianRing R] (T : Scheme.{t}) :
    PreservesFiniteLimits (realization R I T) := (realization_exact R I T).2.1

/-- Right exactness supplies the canonical boundary and quotient comparisons.
Source: Stacks 010N (blueprint: lem-a1-completed-scalar-exact-base-change). -/
instance realization_colimits [IsNoetherianRing R] (T : Scheme.{t}) :
    PreservesFiniteColimits (realization R I T) := (realization_exact R I T).2.2

/-- Assemble the existing cycle/boundary comparison naturally on cochain complexes.
Source: Stacks 010N (blueprint: lem-a1-completed-scalar-exact-base-change). -/
def exactCohomologyIso {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (j : ℤ) :
    F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor B (.up ℤ) j ≅
      HomologicalComplex.homologyFunctor A (.up ℤ) j ⋙ F :=
  NatIso.ofComponents (fun P ↦ (P.sc j).mapHomologyIso F)
    (fun f ↦ ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor A (.up ℤ) j).map f) F)

/-- The canonical natural cohomology isomorphism for arbitrary, unbounded complexes.
This is the kernel and cokernel comparison, not a chosen unnormalized isomorphism.
Source: Stacks 010N (blueprint: lem-a1-completed-scalar-exact-base-change). -/
def cohomologyIso [IsNoetherianRing R] (T : Scheme.{t}) (j : ℤ) :=
  exactCohomologyIso (realization R I T) j

/-- The same canonical cohomology comparison read as a cohomology sheaf of Q(S(P)).
Source: Stacks 010N, 05RR (blueprint: lem-a1-completed-scalar-exact-base-change). -/
def derivedCohomologyIso [IsNoetherianRing R] (T : Scheme.{t})
    [HasDerivedCategory.{w} (ringedSiteModules.{max (t + 1) u} (rings R I T))]
    (P : CochainComplex (ModuleCat.{max (t + 1) u} R) ℤ) (j : ℤ) :
    (DerivedCategory.homologyFunctor
      (ringedSiteModules.{max (t + 1) u} (rings R I T)) j).obj
        (DerivedCategory.Q.obj (((realization R I T).mapHomologicalComplex (.up ℤ)).obj P)) ≅
      (realization R I T).obj (P.homology j) :=
  (DerivedCategory.homologyFunctorFactors _ j).app _ ≪≫ (cohomologyIso R I T j).app P

/-- A constant module section, through the actual module sheafification unit.
Source: Stacks 093J (blueprint: lem-a1-completed-scalar-exact-base-change). -/
def constantSection (T : Scheme.{t}) (N : ModuleCat.{max (t + 1) u} R)
    (V : (Site.{t, u} T)ᵒᵖ) (n : N) :
    ((commutativeSiteConstantModuleFunctor (topology.{t, u} T) R).obj N).val.obj V :=
  letI := (realizationRingUnit_locallyBijective (topology.{t, u} T) R).1
  letI := (realizationRingUnit_locallyBijective (topology.{t, u} T) R).2
  (((PresheafOfModules.sheafificationAdjunction
    (realizationRingUnit (topology.{t, u} T) R)).unit.app
      ((siteConstantModulePresheafGeneral (C := Site.{t, u} T) R).obj N)).app V) n

/-- The pure scalar tensor section in the existing scalar realization.
Source: Stacks 03EK (blueprint: lem-a1-completed-scalar-exact-base-change). -/
def tensorSection (T : Scheme.{t}) (N : ModuleCat.{max (t + 1) u} R)
    (V : (Site.{t, u} T)ᵒᵖ) (b : (completed R I T).obj.obj V)
    (n : ((commutativeSiteConstantModuleFunctor (topology.{t, u} T) R).obj N).val.obj V) :
    ((realization R I T).obj N).val.obj V :=
  (toSheafify (topology.{t, u} T)
    (SheafOfModules.changeOfRingsPresheafOfUniverses (scalar R I T)
      ((commutativeSiteConstantModuleFunctor (topology.{t, u} T) R).obj N)).presheaf).app V
        (b ⊗ₜ[(constant R T).obj.obj V, ((scalar R I T).hom.app V).hom] n)

/-- A tensor generator of ordinary pullback over a base-changed site object.
The adjunction unit inserts 1; target scalar multiplication supplies b'.
Source: Stacks 03D7, 03EL (blueprint: lem-a1-completed-scalar-exact-base-change). -/
def pullTensor {X Y : Scheme.{t}} (g : X ⟶ Y)
    (F : ringedSiteModules.{max (t + 1) u} (rings R I Y))
    (V : Site.{t, u} Y) (b' : (completed R I X).obj.obj (op ((baseChange g).obj V)))
    (x : F.val.obj (op V)) :
    ((pullback R I g).obj F).val.obj (op ((baseChange g).obj V)) :=
  b' • (@id (((pullback R I g).obj F).val.obj (op ((baseChange g).obj V)))
    (((SheafOfModules.pullbackPushforwardAdjunction (moduleMap R I g)).unit.app F).val.app
      (op V) x))

/-- The adjunction unit on rings, defining module inverse image over g-inverse B.
Source: Stacks 03D2 (blueprint: lem-a1-completed-scalar-exact-base-change). -/
def inverseModuleMap {X Y : Scheme.{t}} (g : X ⟶ Y) :
    rings R I Y ⟶ ((baseChange g).sheafPushforwardContinuous RingCat
      (topology.{t, u} Y) (topology.{t, u} X)).obj
        ((sheafCompose (topology.{t, u} X) (forget₂ CommRingCat RingCat)).obj
          ((inverse g).obj (completed R I Y))) :=
  ⟨Functor.whiskerRight ((ringAdjunction g).unit.app (completed R I Y)).hom
    (forget₂ CommRingCat RingCat)⟩

/-- Module inverse image over the inverse-image ring has its standard direct-image adjoint.
Source: Stacks 03D7 (blueprint: lem-a1-completed-scalar-exact-base-change). -/
instance inverseModule_rightAdjoint {X Y : Scheme.{t}} (g : X ⟶ Y) :
    (SheafOfModules.pushforward.{max (t + 1) u} (inverseModuleMap R I g)).IsRightAdjoint :=
  SheafOfModules.module_pushforward_isRightAdjoint_of_universes (inverseModuleMap R I g)

/-- Module inverse image with its actual inverse-image coefficient ring.
Source: Stacks 03D2 (blueprint: lem-a1-completed-scalar-exact-base-change). -/
abbrev moduleInverse {X Y : Scheme.{t}} (g : X ⟶ Y) :=
  SheafOfModules.pullback.{max (t + 1) u} (inverseModuleMap R I g)

/-- The explicit ordinary tensor description of the left adjoint, normalized by its unit.
This comparison states g_B^* F = B_X tensor_(g-inverse B_Y) g-inverse F as functors.
Source: Stacks 03D2, 03D7, 03EL (blueprint: lem-a1-completed-scalar-exact-base-change).
Proof (node step 3): compose module inverse image with extension along c_g. Its
right adjoint is sectionwise direct image with scalar action through the adjunct
of c_g, which is directMap. Uniqueness of left adjoints supplies the comparison.
The uniqueness equation on units, followed by B_X-linearity, gives the tensor formula. -/
theorem pullback_tensor {X Y : Scheme.{t}} (g : X ⟶ Y) :
    ∃ e : pullback R I g ≅ moduleInverse R I g ⋙
        ConstantCompletion.change (coefficientMap R I g),
      ∀ (F : ringedSiteModules.{max (t + 1) u} (rings R I Y)) (V : Site.{t, u} Y)
        (b' : (completed R I X).obj.obj (op ((baseChange g).obj V)))
        (x : F.val.obj (op V)),
        (e.hom.app F).val.app (op ((baseChange g).obj V)) (pullTensor R I g F V b' x) =
          ConstantCompletion.tensorSection (coefficientMap R I g) ((moduleInverse R I g).obj F)
            (op ((baseChange g).obj V)) b'
            (@id (((moduleInverse R I g).obj F).val.obj (op ((baseChange g).obj V)))
              (((SheafOfModules.pullbackPushforwardAdjunction
                (inverseModuleMap R I g)).unit.app F).val.app (op V) x)) := by
  sorry

/-- The ordinary comparison, including its two balanced-tensor formulas.
Naturality in every linear map is part of the natural isomorphism.
Source: Stacks 03EL (blueprint: lem-a1-completed-scalar-exact-base-change).
Proof (node steps 3, 6--8): direct image along moduleMap has the published tensor
pullback as its left adjoint. Inverse image preserves constants and sheafified tensor
products, so the pulled realization is D tensor_C (C tensor_A constant N).
Send d tensor (c tensor n) to d*c_g(c) tensor n; the inverse inserts 1.
The scalar square in coefficientMap_properties respects the inner A-relation, and
multiplicativity of c_g respects the outer C-relation. Both rules commute with
restrictions and descend through sheafification. Their composites are identities
on local pure tensors and hence on the sheaves. Replacing n by any linear image
proves naturality. These formulas use no flatness of D over C and apply to every N.
The equivalent sites in the common ambient universe retain the original site
objects and their section maps, so the construction also proves the size clause. -/
theorem completedScalarExactBaseChange [IsNoetherianRing R] {X Y : Scheme.{t}} (g : X ⟶ Y) :
    ∃ e : realization R I Y ⋙ pullback R I g ≅ realization R I X,
      (∀ (N : ModuleCat.{max (t + 1) u} R) (V : Site.{t, u} Y)
        (b : (completed R I Y).obj.obj (op V))
        (b' : (completed R I X).obj.obj (op ((baseChange g).obj V))) (n : N),
        (e.hom.app N).val.app (op ((baseChange g).obj V))
          (pullTensor R I g ((realization R I Y).obj N) V b'
            (tensorSection R I Y N (op V) b (constantSection R Y N (op V) n))) =
          tensorSection R I X N (op ((baseChange g).obj V))
            (b' * (@id ((completed R I X).obj.obj (op ((baseChange g).obj V)))
              ((directMap R I g).hom.app (op V) b)))
            (constantSection R X N (op ((baseChange g).obj V)) n)) ∧
      (∀ (N : ModuleCat.{max (t + 1) u} R) (V : Site.{t, u} Y)
        (b' : (completed R I X).obj.obj (op ((baseChange g).obj V))) (n : N),
        (e.inv.app N).val.app (op ((baseChange g).obj V))
          (tensorSection R I X N (op ((baseChange g).obj V)) b'
            (constantSection R X N (op ((baseChange g).obj V)) n)) =
          pullTensor R I g ((realization R I Y).obj N) V b'
            (tensorSection R I Y N (op V) 1 (constantSection R Y N (op V) n))) := by
  sorry

end AlgebraicGeometry.CompletedScalar
