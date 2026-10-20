/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.CartierReductionSiteComparison
public import Sheaf.Paper.ProEtaleTateTwists
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Adjunction

import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits

import Sheaf.Algebra.Homology.KFlat

import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf

import Mathlib.Algebra.Homology.DerivedCategory.Basic

import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison

import WeilConjectures.AlgebraicGeometry.Sites.Kummer

import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

import Sheaf.Paper.PurTwistSheafLocallyFree

import Sheaf.Paper.DivisibleExtensionDerivedReduction

import Sheaf.Paper.CompletedPullbackAdjunction

import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence

import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FreeSheafFlat

import Sheaf.CategoryTheory.SiteInverseImageTensor

import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed

import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction

import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck

import WeilConjectures.SixFunctors.Finite.Stalk

import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.Paper.ProEtaleTateTwistsOfUniverses
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth

/-!
# The diagonal class in the derived category of strict torsion towers

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-system.md (blueprint: det-prop-diagonal-tower-system).
The index n denotes exponent n+1. Fixed-scalar module sheaves present modules over
constant ring sheaves; the underlying integer category is abelian sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u uA uB vA vB wA wS
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- Integral sheaves. Source: blueprint clause 1
(blueprint: det-prop-diagonal-tower-system). -/
abbrev DiagonalAb (W : Scheme.{u}) := Sheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}

/-- Discrete constant Z_l-module sheaves, not continuous-function coefficient sheaves.
Source: blueprint tower category (blueprint: det-prop-diagonal-tower-system). -/
abbrev DiagonalMod (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :=
  Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))

/-- Strict inverse systems. Source: blueprint tower category
(blueprint: det-prop-diagonal-tower-system). -/
abbrev DiagonalSystems (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :=
  ℕᵒᵖ ⥤ DiagonalMod ℓ W

/-- The canonical abelian structure, named once to share all its sheafification
witnesses throughout the strict-system specification. This is the existing Mathlib
structure, with no choice of a replacement category.
Source: blueprint coefficient conventions (blueprint: det-prop-diagonal-tower-system). -/
instance (priority := 2000) diagonalModuleSheafAbelian
    (A : Type (u + 1)) [CommRing A] (W : Scheme.{u}) :
    Abelian (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} A)) := inferInstance

/-- The canonical abelian-sheaf structure, with its witnesses shared by name.
Source: blueprint coefficient conventions (blueprint: det-prop-diagonal-tower-system). -/
instance (priority := 2000) diagonalAbSheafAbelian (W : Scheme.{u}) :
    Abelian (DiagonalAb W) := inferInstance

/-- Ordinary extension from abelian groups to Z_l, before reduction, sheafified
sectionwise. Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalScalarExtension (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    DiagonalAb W ⥤ DiagonalMod ℓ W :=
  sheafToPresheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringRight W.ProEtᵒᵖ AddCommGrpCat.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))).obj
        ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
          ModuleCat.extendScalars (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))) ⋙
    presheafToSheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))

/-- Forget scalars through the unique integer action.
Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalForget (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    DiagonalMod ℓ W ⥤ DiagonalAb W :=
  sheafCompose (Scheme.ProEt.topology W)
    (ModuleCat.restrictScalars (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ])) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})

/-- The usual insertion-of-one scalar adjunction, lifted to sheaves.
Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalScalarAdjunction (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    diagonalScalarExtension ℓ W ⊣ diagonalForget ℓ W :=
  Sheaf.adjunction (Scheme.ProEt.topology W)
    ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence.symm.toAdjunction.comp
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))))

/-- Forgetting constant scalars is exact.
Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system).
Proof: kernels are sectionwise; cokernels are sheafifications of the same additive
quotients. The unique integer action changes neither construction. -/
theorem diagonalForget_exact (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalForget ℓ W) ∧
      PreservesFiniteColimits (diagonalForget ℓ W) := by
  constructor
  · have := (diagonalScalarAdjunction ℓ W).rightAdjoint_preservesLimits
    infer_instance
  · let G := ModuleCat.restrictScalars
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ])) ⋙
        forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
    have : (ModuleCat.restrictScalars.{u + 1}
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, 0, u + 1}
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))).isLeftAdjoint
    have : G.IsLeftAdjoint := inferInstance
    let J := Scheme.ProEt.topology W
    let e : Sheaf.composeAndSheafify J G ≅ sheafCompose J G :=
      Functor.isoWhiskerLeft (sheafCompose J G)
        (sheafificationNatIso J AddCommGrpCat.{u + 1}).symm ≪≫
        Functor.rightUnitor (sheafCompose J G)
    have : (Sheaf.composeAndSheafify J G).IsLeftAdjoint := inferInstance
    have : (sheafCompose J G).IsLeftAdjoint := Functor.isLeftAdjoint_of_iso e
    exact inferInstanceAs (PreservesFiniteColimits (sheafCompose J G))

/-- Exact scalar forgetting, limits. Source: blueprint clause 2
(blueprint: det-prop-diagonal-tower-system). -/
instance diagonalForgetLimits (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalForget ℓ W) := (diagonalForget_exact ℓ W).1

/-- Exact scalar forgetting, colimits. Source: blueprint clause 2
(blueprint: det-prop-diagonal-tower-system). -/
instance diagonalForgetColimits (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteColimits (diagonalForget ℓ W) := (diagonalForget_exact ℓ W).2

/-- Additivity of scalar forgetting. Source: blueprint clause 2
(blueprint: det-prop-diagonal-tower-system).
Proof: the underlying section maps add pointwise and forgetting retains them. -/
theorem diagonalForget_additive (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    (diagonalForget ℓ W).Additive := by
  dsimp only [diagonalForget, sheafCompose]
  infer_instance

attribute [instance] diagonalForget_additive

/-- A strict ordinary reduction functor, characterized by its quotient universal
properties and quotient transitions. With L=extension to Z_l this is tensor with the
whole coefficient system; with L=identity this is its integral version.
Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system). -/
structure DiagonalReductionPresentation
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] (L : A ⥤ B) where
  /-- One functor into the strict system category. -/
  E : A ⥤ (ℕᵒᵖ ⥤ B)
  /-- Termwise tensor is additive. -/
  [additive : E.Additive]
  /-- Quotient of extension by the positive prime power. -/
  π : ∀ n : ℕ, L ⟶ E ⋙ (evaluation ℕᵒᵖ B).obj (op n)
  /-- Its kernel relation. -/
  zero : ∀ (n : ℕ) (M : A),
    (ℓ ^ (n + 1) • 𝟙 (L.obj M)) ≫ (π n).app M = 0
  /-- The quotient is a cokernel, fixing its scalar action and maps. -/
  quotient : ∀ (n : ℕ) (M : A),
    IsColimit (CokernelCofork.ofπ ((π n).app M) (zero n M))
  /-- The transitions are the coefficient quotient maps, not independent level maps. -/
  transition : ∀ (n : ℕ) (M : A),
    (π (n + 1)).app M ≫ (E.obj M).map (homOfLE (Nat.le_succ n)).op = (π n).app M

attribute [instance] DiagonalReductionPresentation.additive

/-- The everywhere-defined left derived functor of a strict reduction presentation.
The universal counit and pointwise condition retain functoriality on all unbounded
complexes. Source: blueprint clause 2 (blueprint: det-prop-diagonal-tower-system). -/
structure DiagonalDerivedReduction
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] (L : A ⥤ B)
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wS} (ℕᵒᵖ ⥤ B)] where
  /-- The ordinary simultaneous reduction. -/
  ordinary : DiagonalReductionPresentation ℓ L
  /-- Its left derived functor, valued in the derived category of strict systems. -/
  T : DerivedCategory A ⥤ DerivedCategory (ℕᵒᵖ ⥤ B)
  /-- Universal comparison with termwise scalar tensor. -/
  ε : DerivedCategory.Q ⋙ T ⟶ ordinary.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  /-- The left derived universal property determines T. -/
  universal : T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))
  /-- It exists pointwise at every complex. -/
  pointwise :
    (ordinary.E.mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q).HasPointwiseLeftDerivedFunctor (HomologicalComplex.quasiIso A (.up ℤ))
  /-- Exactness, including its shift comparison. -/
  triangulated : ∃ (_ : T.CommShift ℤ), T.IsTriangulated

/-- The source identification is the universal derived counit on a degree-zero
flat supported constant, with the standard single-complex comparisons.
Source: blueprint clause 3 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalDerivedSingleCounit
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] (L : A ⥤ B)
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wS} (ℕᵒᵖ ⥤ B)]
    (D : DiagonalDerivedReduction ℓ L) (M : A) :
    D.T.obj ((DerivedCategory.singleFunctor A 0).obj M) ⟶
      (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj (D.ordinary.E.obj M) :=
  D.T.map ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app M) ≫
    D.ε.app ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex D.ordinary.E (.up ℤ) 0).hom.app M) ≫
    (DerivedCategory.singleFunctorIsoCompQ (ℕᵒᵖ ⥤ B) 0).inv.app (D.ordinary.E.obj M)

/-- The positive-exponent finite coefficient ring, lifted to the sheaf universe.
Source: blueprint clauses 3--4 (blueprint: det-prop-diagonal-tower-system). -/
abbrev diagonalResidue (ℓ n : ℕ) := cartierResidueRing.{u} ℓ (n + 1)

/-- The coefficient projection from Z_l to the lifted finite ring.
Source: blueprint clauses 2--4 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalResidueProjection (ℓ n : ℕ) [Fact ℓ.Prime] :
    ULift.{u + 1} ℤ_[ℓ] →+* diagonalResidue.{u} ℓ n :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom)

/-- A finite-coefficient module, read as a Z_l-module through the specified projection.
Source: blueprint clause 4 (blueprint: det-prop-diagonal-tower-system). -/
def diagonalFiniteToPadic (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)) ⥤
      DiagonalMod ℓ W :=
  sheafCompose (Scheme.ProEt.topology W)
    (ModuleCat.restrictScalars (diagonalResidueProjection.{u} ℓ n))

/-- Finite coefficient restriction is exact and additive.
Source: blueprint clause 4 (blueprint: det-prop-diagonal-tower-system).
Proof: the underlying abelian kernels and sheafified cokernels are unchanged;
restriction retains every additive section map. -/
theorem diagonalFiniteToPadic_exact (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalFiniteToPadic ℓ n W) ∧
    PreservesFiniteColimits (diagonalFiniteToPadic ℓ n W) ∧
    (diagonalFiniteToPadic ℓ n W).Additive := by
  constructor
  · have := (Sheaf.adjunction (Scheme.ProEt.topology W)
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (diagonalResidueProjection.{u} ℓ n))).rightAdjoint_preservesLimits
    exact inferInstanceAs (PreservesFiniteLimits
      (sheafCompose (Scheme.ProEt.topology W)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (diagonalResidueProjection.{u} ℓ n))))
  constructor
  · let q := diagonalResidueProjection.{u} ℓ n
    have hadj := ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} q
    have : PreservesLimitsOfSize.{u, u + 1}
        (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} q) :=
      hadj.rightAdjoint_preservesLimits
    have : (Scheme.ProEt.topology W).HasSheafCompose
        (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} q) :=
      hasSheafCompose_of_preservesLimitsOfSize _
    have := (Sheaf.adjunction (Scheme.ProEt.topology W) hadj).isLeftAdjoint
    let J := Scheme.ProEt.topology W
    let G := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q
    let e : Sheaf.composeAndSheafify J G ≅ sheafCompose J G :=
      Functor.isoWhiskerLeft (sheafCompose J G)
        (sheafificationNatIso J (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))).symm ≪≫
        Functor.rightUnitor (sheafCompose J G)
    exact preservesFiniteColimits_of_natIso e
  · dsimp only [diagonalFiniteToPadic, sheafCompose]
    infer_instance

/-- Exact restriction, limits. Source: blueprint clause 4
(blueprint: det-prop-diagonal-tower-system). -/
instance diagonalFiniteToPadicLimits (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalFiniteToPadic ℓ n W) :=
  (diagonalFiniteToPadic_exact ℓ n W).1

/-- Exact restriction, colimits. Source: blueprint clause 4
(blueprint: det-prop-diagonal-tower-system). -/
instance diagonalFiniteToPadicColimits (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteColimits (diagonalFiniteToPadic ℓ n W) :=
  (diagonalFiniteToPadic_exact ℓ n W).2.1

/-- Additive restriction. Source: blueprint clause 4
(blueprint: det-prop-diagonal-tower-system). -/
instance diagonalFiniteToPadicAdditive (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    (diagonalFiniteToPadic ℓ n W).Additive :=
  (diagonalFiniteToPadic_exact ℓ n W).2.2

/-- The product of two projective lines. Source: blueprint opening
(blueprint: det-prop-diagonal-tower-system). -/
abbrev diagonalSurface (Y : Scheme.{u}) :=
  pullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)

/-- The diagonal. Source: blueprint opening
(blueprint: det-prop-diagonal-tower-system). -/
abbrev diagonalImmersion (Y : Scheme.{u}) : ProjectiveLine Y ⟶ diagonalSurface Y :=
  pullback.diagonal (ProjectiveLine Y ↘ Y)

/-- The diagonal is Cartier over every base, including the empty base.
Source: blueprint proof step 1 (blueprint: det-prop-diagonal-tower-system).
Proof: the first projection of the surface is smooth of relative dimension one,
as a base change of the projective line. Its composite with the diagonal is the
identity. The closed subscheme defined by the kernel of the diagonal is isomorphic
to the diagonal, so its projection is an isomorphism, hence finite, flat and locally
of finite presentation. The relative Cartier criterion gives the invertible ideal. -/
theorem diagonalImmersion_cartier (Y : Scheme.{u}) :
    (diagonalImmersion Y).ker.IsInvertible := by
  let d := diagonalImmersion Y
  let p := pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)
  let j := d.ker.subschemeι
  have hker : d.ker = j.ker := by simp [j]
  let e := IsClosedImmersion.lift d j hker.le
  have : IsIso e := IsClosedImmersion.isIso_lift d j hker
  have he : e ≫ d = j := IsClosedImmersion.lift_fac d j hker.le
  have hp : j ≫ p = e := by
    rw [← he, Category.assoc]
    simp [d, p, diagonalImmersion]
  have : IsIso (j ≫ p) := hp.symm ▸ inferInstance
  exact Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat p
    (J := d.ker) inferInstance inferInstance inferInstance

/-- Invertibility pulls from the base to the diagonal surface and all powers.
Source: blueprint standing hypothesis (blueprint: det-prop-diagonal-tower-system).
Proof: apply the ring map of global sections for W→Y to the given unit, then take
its positive power. This also applies to the zero ring of the empty scheme. -/
theorem diagonalSurface_power_unit (ℓ : ℕ) (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤))) (n : ℕ) :
    IsUnit ((ℓ ^ (n + 1) : ℕ) : Γ(diagonalSurface Y, ⊤)) := by
  simpa using (hY.map
    ((pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) ≫
      (ProjectiveLine Y ↘ Y)).appTop.hom).pow (n + 1)

/-- The supported integral constant on the pro-etale site.
Source: blueprint clause 1 (blueprint: det-prop-diagonal-tower-system). -/
abbrev diagonalIntegralSource (Y : Scheme.{u}) :=
  (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)).obj
    ((constantSheaf (Scheme.ProEt.topology (ProjectiveLine Y)) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- Units mean exact comparison pullback of etale units.
Source: blueprint clause 1 (blueprint: det-prop-diagonal-tower-system). -/
abbrev diagonalComparisonUnits (Y : Scheme.{u}) :=
  (comparisonUpperStar AddCommGrpCat.{u + 1} (diagonalSurface Y)).obj
    (diagonalSurface Y).gmSheaf

/-- The positive roof boundary: Ext uses the negative cone projection, so negate it.
This is the roof with [G_m→M] in degrees -1,0, quotient on the left and positive
projection on the right. The pole extension sends t inverse to +1.
Source: blueprint clause 1 and proof steps 1--2
(blueprint: det-prop-diagonal-tower-system). -/
def diagonalIntegralBoundary (Y : Scheme.{u}) :
    Ext (diagonalIntegralSource Y) (diagonalComparisonUnits Y) 1 :=
  -((Ext.mk₀ (cartierIntegralSourceIso (diagonalImmersion Y)).inv).comp
    ((Etale.cartierPoleBoundary (diagonalImmersion Y) (diagonalImmersion_cartier Y)).mapExactFunctor
       (comparisonUpperStar AddCommGrpCat.{u + 1} (diagonalSurface Y)))
    (zero_add 1))

/-- The integral derived-completion formula, with both inverse limits total right
derived functors on strict systems. The integral reduction is independently fixed by
the cokernels of l^(n+1) on the identity functor. Thus its composite with integral
Rlim is exactly Rlim_n(K tensor^L Z/l^(n+1)). The displayed natural isomorphism
retains the comparison after forgetting the constant Z_l action. In addition the
output is right orthogonal to every complex on which l is invertible, the intrinsic
derived l-completeness criterion. The natural unit is universal for maps to all
such complete complexes, so this asserts derived completion, not just a limit formula.
Source: blueprint clause 2 and Stacks 099M, 091S and 091Z
(blueprint: det-prop-diagonal-tower-system). -/
def DiagonalCompletionSpec (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) : Prop :=
  ∃ (I : DiagonalDerivedReduction ℓ (𝟭 (DiagonalAb W)))
    (RF : DerivedCategory (DiagonalSystems ℓ W) ⥤ DerivedCategory (DiagonalMod ℓ W))
    (η : (lim : DiagonalSystems ℓ W ⥤ DiagonalMod ℓ W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (RZ : DerivedCategory (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DerivedCategory (DiagonalAb W))
    (ηZ : (lim : (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DiagonalAb W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RZ),
    RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso (DiagonalSystems ℓ W) (.up ℤ)) ∧
    RZ.IsRightDerivedFunctor ηZ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ DiagonalAb W) (.up ℤ)) ∧
    Nonempty (D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory ≅ I.T ⋙ RZ) ∧
    ∃ unit : 𝟭 (DerivedCategory (DiagonalAb W)) ⟶
        D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory,
      (∀ (K P : DerivedCategory (DiagonalAb W)), IsIso (ℓ • 𝟙 P) →
        Subsingleton (P ⟶ (D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory).obj K)) ∧
      ∀ (K N : DerivedCategory (DiagonalAb W)),
        (∀ P : DerivedCategory (DiagonalAb W), IsIso (ℓ • 𝟙 P) → Subsingleton (P ⟶ N)) →
        Function.Bijective (fun f :
          (D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory).obj K ⟶ N ↦
            unit.app K ≫ f)

/-- The levelwise finite-source comparison preserves the quotient unit, not an
arbitrary automorphism of the supported constant.
Source: blueprint clauses 3--4 (blueprint: det-prop-diagonal-tower-system). -/
def DiagonalSourceNormalization (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (D : DiagonalReductionPresentation ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (n : ℕ)
    (s : (D.E.obj (diagonalIntegralSource Y)).obj (op n) ≅
      (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
        ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)) (diagonalImmersion Y)).obj
          (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y)))) : Prop :=
  HEq
    ((diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
      (diagonalForget ℓ (diagonalSurface Y)).map ((D.π n).app (diagonalIntegralSource Y) ≫
        s.hom))
    (cartierProIntegralGenerator (diagonalResidue.{u} ℓ n) (diagonalImmersion Y))

/-- A single arrow in D(strict systems), its prescribed source and target, and its
finite cycle-class identifications. Ext^2 is used only as the standard homEquiv
presentation of a morphism from a degree-zero system to a system shifted by two.
Source: blueprint clauses 3--4 (blueprint: det-prop-diagonal-tower-system). -/
def DiagonalCycleSystemSpec (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y))) : Prop :=
  ∃ (H : DiagonalSystems ℓ (diagonalSurface Y))
    (roots : H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (c : Ext (D.ordinary.E.obj (diagonalIntegralSource Y)) H 2),
    a.hom = diagonalDerivedSingleCounit ℓ
      (diagonalScalarExtension ℓ (diagonalSurface Y)) D (diagonalIntegralSource Y) ∧
    c.hom = a.inv ≫ D.T.map (diagonalIntegralBoundary Y).hom ≫ b.hom ∧
    ∀ n : ℕ,
      ∃ (s : (D.ordinary.E.obj (diagonalIntegralSource Y)).obj (op n) ≅
          (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
            ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))
              (diagonalImmersion Y)).obj
                (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y))))
        (t : H.obj (op n) ≅ (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
          (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
            (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y))),
        DiagonalSourceNormalization ℓ Y D.ordinary n s ∧
        HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
          (roots.hom.app (op n) ≫
            cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
              (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)
              (pow_pos (Fact.out : ℓ.Prime).pos _) (diagonalSurface_power_unit ℓ Y hY n)) ∧
        (Ext.mk₀ s.inv).comp
          ((c.mapExactFunctor ((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
            (op n))).comp (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2) =
          (cartierResidueReducedPro ℓ (Fact.out : ℓ.Prime) (n + 1) (diagonalImmersion Y)
            (diagonalImmersion_cartier Y) (diagonalSurface_power_unit ℓ Y hY n)).mapExactFunctor
               (diagonalFiniteToPadic ℓ n (diagonalSurface Y))

/-- The diagonal torsion classes form one morphism in the derived category of
strict inverse systems, obtained by simultaneous derived reduction of the positive
integral Cartier roof. No noetherian, finiteness or nonemptiness assumption is imposed
on Y. The displayed typeclasses only choose the localization and Ext size conventions.

Source: blueprint main-20261015, sk-prop-diagonal-tower-system.md, clauses 1--4;
Stacks Project, Tags 099M and 09AD (blueprint: det-prop-diagonal-tower-system).

Proof:
1. The diagonal is a section of the smooth relative curve given by the first
   projection. Its kernel subscheme projects isomorphically to the projective
   line, so the relative Cartier criterion makes its ideal invertible.
   Form the pole extension with all integer powers of t inverse, sending it to +1.
   Exact conservative geometric stalks identify its quotient with Delta_* Z.
2. Exact comparison inverse image preserves the extension and its quotient
   quasi-isomorphism; the open--closed sequence gives the supported comparison.
   The positive cone projection is the negative of the standard Ext boundary,
   which is precisely diagonalIntegralBoundary.
3. Form the actual strict reduction functor by the cokernels specified above,
   with quotient transitions. Resolve every integral input by a flat-term K-flat
   complex. Simultaneous tensor preserves quasi-isomorphisms between these;
   the resolving-class theorem gives its pointwise left derived functor, exact
   because tensor respects shifts and mapping cones.
4. Z_l is torsion free, hence flat over Z. Exact extension is left adjoint to
   restriction, so restriction preserves K-injective strict systems and commutes
   with their inverse limits. Derive with the same resolution. The integral
   composite is Rlim_n(K tensor^L Z/l^(n+1)). The principal-ideal criterion
   of Tags 091S and 091Z identifies completeness with right orthogonality to
   all complexes on which l acts invertibly. Tag 099M supplies complete outputs
   and the natural completion unit, with bijective precomposition for every
   complete target. Thus the composite is the completion reflector, including
   its universal unit, not merely an isomorphism of the naive limit formulas.
5. Open--closed exactness shows Delta_* Z is flat and its ordinary reductions
   are the supported finite constants. These identifications preserve the units
   and every quotient transition, giving a and the normalized level maps s.
6. Kummer exactness computes the reduction of comparison units by
   [G_m --l^(n+1)--> G_m] in degrees -1,0. The resolution transition is l in
   degree -1 and identity in degree 0, hence the roots transition is zeta→zeta^l.
   Exact comparison identifies the roots with the actual pro-etale root sheaves.
   Use the negative Kummer identification, compensating the positive roof sign.
   Concentration in one cohomology degree lifts this to the strict system category.
7. The divisible-extension derived-reduction comparison fixes the complete
   supported Cartier class, not only its Chern composite. Its signed Kummer
   normalization identifies every evaluated arrow with cartierResidueReducedPro.
   The source and roots normalization equations retain the canonical finite
   identifications. Compatibility already holds because T has values in the
   derived category of strict systems, and c is its image of one boundary. -/
theorem exists_diagonalTowerSystem (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))] :
    ∃ D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)),
      DiagonalCompletionSpec ℓ (diagonalSurface Y) D ∧ DiagonalCycleSystemSpec ℓ Y hY D := by
  sorry

end AlgebraicGeometry.ProEtale
