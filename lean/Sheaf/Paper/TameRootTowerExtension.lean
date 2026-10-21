/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FullParameterRootTower
public import Sheaf.Paper.ProfiniteCoefficientLinearization
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.ContinuousRingUniverseRealization
public import Sheaf.Paper.IntegralContinuousPresentationMatrix
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

import Sheaf.AlgebraicGeometry.SNCUniversalResidualCharts
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
import Sheaf.SixFunctors.IntegralLisseReductionEquivalence
import Sheaf.Paper.NormalCompletedIntegralModel
import Sheaf.Paper.LatticeSheafLocallyConstant
import Sheaf.Paper.TotallyDisconnectedCoefficientRealization
import Sheaf.Paper.CartesianCoefficients
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization
import Sheaf.Paper.CoefficientHeartStratificationDefs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Equivariant lisse extension on the full parameter-root tower

Source: blueprint main-20261015, ctf-stability direct-images proof paragraph (3),
tame-boundary expansion (blueprint: lem-sfb-tame-root-tower-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The open complement, with its canonical scheme structure.
Source: tame-boundary expansion, W = Y minus D
(blueprint: lem-sfb-tame-root-tower-extension). -/
abbrev tameBoundaryOpen {Y : Scheme.{u}} (D : Y.IdealSheafData) : Y.Opens :=
  D.support.compl

/-- An affine etale chart and an affine pro-etale refinement with actual boundary equations.
Source: tame-boundary expansion, first conclusion
(blueprint: lem-sfb-tame-root-tower-extension). -/
structure TameRootExtensionChart {Y : Scheme.{u}} {A : Type u} [Finite A]
    (C : A → Y.IdealSheafData) (I : Finset A) where
  V : Scheme.{u}
  affineV : IsAffine V
  v : V ⟶ (parameterStratumOpen C I).toScheme
  etale : Etale v
  t : {a : A // a ∈ I} → Γ(V, ⊤)
  equations : IsBoundaryParameterFamily (fun a ↦ C a.val)
    (v ≫ (parameterStratumOpen C I).ι) t
  U : Scheme.{u}
  affineU : IsAffine U
  u : U ⟶ V
  proetale : WeaklyEtale u
  affineMap : IsAffineHom u

attribute [instance] TameRootExtensionChart.affineV TameRootExtensionChart.affineU

/-- The chart map to Y. Source: tame-boundary expansion, U_alpha over Y
(blueprint: lem-sfb-tame-root-tower-extension). -/
def TameRootExtensionChart.toBase {Y : Scheme.{u}} {A : Type u} [Finite A]
    {C : A → Y.IdealSheafData} {I : Finset A} (c : TameRootExtensionChart C I) :
    c.U ⟶ Y := c.u ≫ c.v ≫ (parameterStratumOpen C I).ι

/-- The parameters pulled to U. Source: tame-boundary expansion, root-algebra parameters
(blueprint: lem-sfb-tame-root-tower-extension). -/
def TameRootExtensionChart.parameters {Y : Scheme.{u}} {A : Type u} [Finite A]
    {C : A → Y.IdealSheafData} {I : Finset A} (c : TameRootExtensionChart C I) :
    {a : A // a ∈ I} → Γ(c.U, ⊤) := fun i ↦ c.u.appTop (c.t i)

/-- The actual tower scheme. Source: tame-boundary expansion, displayed T_alpha
(blueprint: lem-sfb-tame-root-tower-extension). -/
abbrev TameRootExtensionChart.tower {Y : Scheme.{u}} {A : Type u} [Finite A]
    {C : A → Y.IdealSheafData} {I : Finset A} (c : TameRootExtensionChart C I) (p : ℕ) :=
  Spec (.of (FullParameterRootAlgebra p c.parameters))

/-- The tower map to U. Source: tame-boundary expansion, T_alpha over U_alpha
(blueprint: lem-sfb-tame-root-tower-extension). -/
def TameRootExtensionChart.towerMap {Y : Scheme.{u}} {A : Type u} [Finite A]
    {C : A → Y.IdealSheafData} {I : Finset A} (c : TameRootExtensionChart C I) (p : ℕ) :
    c.tower p ⟶ c.U := fullParameterRootMap p c.U c.parameters

/-- The boundary base change. Source: tame-boundary expansion, S_alpha
(blueprint: lem-sfb-tame-root-tower-extension). -/
@[irreducible] def TameRootExtensionChart.boundary {Y : Scheme.{u}} {A : Type u} [Finite A]
    {C : A → Y.IdealSheafData} {I : Finset A} (c : TameRootExtensionChart C I) :=
  pullback c.toBase (parameterStratumInclusion C I)

/-- The canonical boundary projection to U, kept folded for site elaboration.
Source: tame-boundary expansion, S_alpha over U_alpha
(blueprint: lem-sfb-tame-root-tower-extension). -/
def TameRootExtensionChart.boundaryToBase {Y : Scheme.{u}} {A : Type u} [Finite A]
    {C : A → Y.IdealSheafData} {I : Finset A} (c : TameRootExtensionChart C I) :
    c.boundary ⟶ c.U := by
  unfold TameRootExtensionChart.boundary
  exact pullback.fst c.toBase (parameterStratumInclusion C I)

/-- The canonical projection to the stratum, kept folded for site elaboration.
Source: tame-boundary expansion, covering S_alpha to S_I
(blueprint: lem-sfb-tame-root-tower-extension). -/
def TameRootExtensionChart.boundaryToStratum {Y : Scheme.{u}} {A : Type u} [Finite A]
    {C : A → Y.IdealSheafData} {I : Finset A} (c : TameRootExtensionChart C I) :
    c.boundary ⟶ ParameterStratum C I := by
  unfold TameRootExtensionChart.boundary
  exact pullback.snd c.toBase (parameterStratumInclusion C I)

/-- The punctured tower. Source: tame-boundary expansion, T_alpha^circ
(blueprint: lem-sfb-tame-root-tower-extension). -/
abbrev TameRootExtensionChart.punctured {Y : Scheme.{u}} {A : Type u} [Finite A]
    {C : A → Y.IdealSheafData} {I : Finset A} (c : TameRootExtensionChart C I)
    (p : ℕ) (D : Y.IdealSheafData) :=
  pullback (c.towerMap p ≫ c.toBase) (tameBoundaryOpen D).ι

/-- Open inclusion of the punctured tower. Source: tame-boundary expansion, restriction
(blueprint: lem-sfb-tame-root-tower-extension). -/
def TameRootExtensionChart.openInclusion {Y : Scheme.{u}} {A : Type u} [Finite A]
    {C : A → Y.IdealSheafData} {I : Finset A} (c : TameRootExtensionChart C I)
    (p : ℕ) (D : Y.IdealSheafData) : c.punctured p D ⟶ c.tower p :=
  pullback.fst _ _

/-- The actual structural map to W. Source: tame-boundary expansion, pullback of L
(blueprint: lem-sfb-tame-root-tower-extension). -/
def TameRootExtensionChart.toOpen {Y : Scheme.{u}} {A : Type u} [Finite A]
    {C : A → Y.IdealSheafData} {I : Finset A} (c : TameRootExtensionChart C I)
    (p : ℕ) (D : Y.IdealSheafData) : c.punctured p D ⟶ (tameBoundaryOpen D).toScheme :=
  pullback.snd _ _

/-- The continuous coefficient comparison with continuous sections, without arbitrary choices.
Source: HRS Example 3.1 and the tame-boundary expansion, matrix action
(blueprint: lem-sfb-tame-root-tower-extension). -/
@[irreducible] def tameCoefficientRealization (E : Type u) [NormedField E]
    [TotallyDisconnectedSpace E]
    (X : Scheme.{u}) :
    condensedRingObj (normContinuousRing E).X X ≅ ContinuousRingUniverse.coeff E X :=
  letI := ContinuousRingUniverse.comparison_isIso X E
  asIso (ContinuousRingUniverse.comparison X E)

/-- A continuous representation on the finite-dimensional product-norm space E^d.
Source: tame-boundary expansion, rho_alpha
(blueprint: lem-sfb-tame-root-tower-extension). -/
structure TameRootRepresentation (E : Type u) [NormedField E]
    (G : Profinite.{u}) [Group G] (d : ℕ) where
  representation : G →* Matrix.GeneralLinearGroup (Fin d) E
  continuous_entries : ∀ i j, Continuous (fun g ↦ (representation g).val i j)

/-- The punctured affine base. Source: tame-boundary expansion, U_alpha^circ
(blueprint: lem-sfb-tame-root-tower-extension). -/
abbrev TameRootExtensionChart.puncturedBase {Y : Scheme.{u}} {A : Type u} [Finite A]
    {C : A → Y.IdealSheafData} {I : Finset A} (c : TameRootExtensionChart C I)
    (D : Y.IdealSheafData) := pullback c.toBase (tameBoundaryOpen D).ι

/-- The map of punctured towers to punctured bases.
Source: tame-boundary expansion, torsor map
(blueprint: lem-sfb-tame-root-tower-extension). -/
def TameRootExtensionChart.toPuncturedBase {Y : Scheme.{u}} {A : Type u} [Finite A]
    {C : A → Y.IdealSheafData} {I : Finset A} (c : TameRootExtensionChart C I)
    (p : ℕ) (D : Y.IdealSheafData) : c.punctured p D ⟶ c.puncturedBase D :=
  pullback.lift (c.openInclusion p D ≫ c.towerMap p) (c.toOpen p D)
    (by simpa only [TameRootExtensionChart.openInclusion,
      TameRootExtensionChart.toOpen, TameRootExtensionChart.punctured, Category.assoc] using
      (pullback.condition (f := c.towerMap p ≫ c.toBase) (g := (tameBoundaryOpen D).ι)))

/-- The actual torsor comparison (x,g) maps to (x,gx).
Source: tame-boundary expansion, displayed torsor comparison
(blueprint: lem-sfb-tame-root-tower-extension). -/
def tameRootTorsorComparison {X B : Scheme.{u}} {G : Profinite.{u}}
    (a : coefficientParameter X G ⟶ X) (f : X ⟶ B)
    (h : a ≫ f = coefficientParameterProjection X G ≫ f) :
    coefficientParameter X G ⟶ pullback f f :=
  pullback.lift (coefficientParameterProjection X G) a h.symm

/-- Equivariance of a module isomorphism for specified family isomorphisms.
Source: tame-boundary expansion, equivariant identifications
(blueprint: lem-sfb-tame-root-tower-extension). -/
def IsTameRootEquivariantIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z : Scheme.{u}} (a b : Z ⟶ X)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (em : (CondensedRing.upperStar Λ a).obj M ≅ (CondensedRing.upperStar Λ b).obj M)
    (en : (CondensedRing.upperStar Λ a).obj N ≅ (CondensedRing.upperStar Λ b).obj N)
    (e : M ≅ N) : Prop :=
  (CondensedRing.upperStar Λ a).map e.hom ≫ en.hom =
    em.hom ≫ (CondensedRing.upperStar Λ b).map e.hom

/-- The matrix of a boundary family in the specified boundary basis, with the canonical
pullback comparisons and the canonical continuous-function coefficient realization.
Source: tame-boundary expansion, boundary representation
(blueprint: lem-sfb-tame-root-tower-extension). -/
@[irreducible] def tameRootBoundaryMatrix (E : Type u) [NormedField E]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (φ : ∀ X : Scheme.{u}, condensedRingObj Λ X ≅ ContinuousRingUniverse.coeff E X)
    {S : Scheme.{u}} (G : Profinite.{u}) (d : ℕ)
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S))
    (b : M ≅ Mod.finiteFree (condensedRingObj Λ S) d)
    (e : (CondensedRing.upperStar Λ
      (coefficientParameterProjection S G)).obj M ≅
      (CondensedRing.upperStar Λ
        (coefficientParameterProjection S G)).obj M) :
    Matrix (Fin d) (Fin d) C(coefficientParameter S G, E) :=
  coefficientFreeMatrix E (coefficientParameter S G) _
    (φ (coefficientParameter S G)) d
    (coefficientConjugateFreeEnd Λ
      (coefficientParameterProjection S G) d M b e)

/-- All the geometric, equivariant and boundary data on a chart. No higher direct image
occurs. The boundary module is E^d with its finite-dimensional product norm topology.
Source: tame-boundary expansion, conclusions after the displayed root tower
(blueprint: lem-sfb-tame-root-tower-extension). -/
structure TameRootChartGeometry (p : ℕ)
    {Y : Scheme.{u}} {A : Type u} [Finite A] {C : A → Y.IdealSheafData} {I : Finset A}
    (D : Y.IdealSheafData) (c : TameRootExtensionChart C I) where
  characters : ParameterRootCharacters p {a : A // a ∈ I} Γ(c.U, ⊤)
  action : ProfiniteCoefficientAction (c.tower p)
    (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ I}))
  overBase : action.act ≫ c.towerMap p =
    coefficientParameterProjection _ _ ≫ c.towerMap p
  rotations : ∀ (n : TameRootOrder p) (i : {a : A // a ∈ I})
    (Z : Scheme.{u}) (z : Z ⟶ coefficientParameter (c.tower p)
      (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ I})))
    (a : {a : A // a ∈ I} → ZMod n.val),
    (∀ x : Z, (characters.residue n
      (profiniteTestProjection _ _ (z x))).toAdd = a) →
    (z ≫ action.act).appTop (fullParameterRootSection p c.parameters n i) =
      (z ≫ coefficientParameterProjection _ _).appTop
        (fullParameterRootSection p c.parameters n i) *
      (z ≫ coefficientParameterProjection _ _ ≫ c.towerMap p).appTop
        (characters.roots n ^ (a i).val)
  openAction : ProfiniteCoefficientAction (c.punctured p D)
    (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ I}))
  openEquivariant : openAction.act ≫ c.openInclusion p D =
    coefficientParameterMap (c.openInclusion p D) _ ≫ action.act
  overQuotient : openAction.act ≫ c.toPuncturedBase p D =
    coefficientParameterProjection _ _ ≫ c.toPuncturedBase p D
  cover : Presieve.singleton (c.toPuncturedBase p D) ∈
    Scheme.proetalePrecoverage (c.puncturedBase D)
  torsor : IsIso (tameRootTorsorComparison openAction.act
    (c.toPuncturedBase p D) overQuotient)
  overOpen : openAction.act ≫ c.toOpen p D =
    coefficientParameterProjection _ _ ≫ c.toOpen p D

/-- The lisse module and its normalized equivariant open identification.
Source: tame-boundary expansion, extension clause
(blueprint: lem-sfb-tame-root-tower-extension). -/
structure TameRootChartExtensionBase (p : ℕ) (E : Type u) [NormedField E]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (φ : ∀ X : Scheme.{u}, condensedRingObj Λ X ≅ ContinuousRingUniverse.coeff E X)
    {Y : Scheme.{u}} {A : Type u} [Finite A]
    {C : A → Y.IdealSheafData} {I : Finset A} (D : Y.IdealSheafData)
    (L : Mod (Sheaf (Scheme.ProEt.topology (tameBoundaryOpen D).toScheme) Ab.{u + 1})
      (condensedRingObj Λ (tameBoundaryOpen D).toScheme))
    (c : TameRootExtensionChart C I) extends TameRootChartGeometry p D c where
  extension : Mod (Sheaf (Scheme.ProEt.topology (c.tower p)) Ab.{u + 1})
    (condensedRingObj Λ (c.tower p))
  lisse : IsLisseCoefficientModule Λ extension
  linearization : ProfiniteCoefficientLinearization Λ action extension
  restriction : (CondensedRing.upperStar Λ
    (c.openInclusion p D)).obj extension ≅
      (CondensedRing.upperStar Λ (c.toOpen p D)).obj L
  restriction_equivariant : IsTameRootEquivariantIso Λ
    openAction.act (coefficientParameterProjection _ _)
    (coefficientLinearizationRestriction Λ
      (X := c.punctured p D) (Y := c.tower p)
      (G := Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ I}))
      openAction.act action.act (c.openInclusion p D) openEquivariant
      (coefficientParameterProjectionCommutes (c.openInclusion p D) _)
      extension linearization.iso)
    (coefficientDeckDescent Λ
      (X := c.punctured p D) (W := (tameBoundaryOpen D).toScheme)
      (G := Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ I})) openAction.act (c.toOpen p D)
      overOpen L) restriction

/-- A finite-dimensional continuous representation model for a fixed boundary pullback.
Source: tame-boundary expansion, boundary linearization
(blueprint: lem-sfb-tame-root-tower-extension). -/
structure TameRootBoundaryModuleData (E : Type u) [NormedField E]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (φ : ∀ X : Scheme.{u}, condensedRingObj Λ X ≅ ContinuousRingUniverse.coeff E X)
    {S T : Scheme.{u}} (G : Profinite.{u}) [Group G]
    (N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (a : coefficientParameter T G ⟶ T) (i : S ⟶ T)
    (hf : coefficientParameterProjection S G ≫ i = coefficientParameterMap i G ≫ a)
    (lin : (CondensedRing.upperStar Λ a).obj N ≅
      (CondensedRing.upperStar Λ (coefficientParameterProjection T G)).obj N) where
  rank : ℕ
  boundaryBasis : (CondensedRing.upperStar Λ i).obj N ≅
    Mod.finiteFree (condensedRingObj Λ S) rank
  representation : TameRootRepresentation E G rank
  boundary_equivariant : ∀ (j k : Fin rank) (x : coefficientParameter S G),
    tameRootBoundaryMatrix E Λ φ G rank ((CondensedRing.upperStar Λ i).obj N) boundaryBasis
      (coefficientLinearizationRestriction Λ
        (coefficientParameterProjection S G) a i hf
        (coefficientParameterProjectionCommutes i G) N lin) j k x =
      (representation.representation (profiniteTestProjection S G x)).val j k

/-- Boundary identification with the continuous representation, including rank zero.
Source: tame-boundary expansion, boundary clause
(blueprint: lem-sfb-tame-root-tower-extension). -/
structure TameRootBoundaryData (p : ℕ) (E : Type u) [NormedField E]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (φ : ∀ X : Scheme.{u}, condensedRingObj Λ X ≅ ContinuousRingUniverse.coeff E X)
    {Y : Scheme.{u}} {A : Type u} [Finite A]
    {C : A → Y.IdealSheafData} {I : Finset A} (D : Y.IdealSheafData)
    (L : Mod (Sheaf (Scheme.ProEt.topology (tameBoundaryOpen D).toScheme) Ab.{u + 1})
      (condensedRingObj Λ (tameBoundaryOpen D).toScheme))
    (c : TameRootExtensionChart C I)
    (e : TameRootChartExtensionBase p E Λ φ D L c) where
  boundaryMap : c.boundary ⟶ c.tower p
  boundaryOver : boundaryMap ≫ c.towerMap p = c.boundaryToBase
  roots_zero : ∀ (n : TameRootOrder p) (i : {a : A // a ∈ I}),
    boundaryMap.appTop (fullParameterRootSection p c.parameters n i) = 0
  boundaryFixed : coefficientParameterProjection c.boundary
      (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ I})) ≫ boundaryMap =
    coefficientParameterMap boundaryMap
      (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ I})) ≫ e.action.act
  model : TameRootBoundaryModuleData E Λ φ
    (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ I}))
    e.extension e.action.act boundaryMap boundaryFixed e.linearization.iso
  empty_tower : I = ∅ → IsIso (c.towerMap p)

/-- The complete extension data, with the boundary in a separate dependent record.
Source: tame-boundary expansion, all chart conclusions
(blueprint: lem-sfb-tame-root-tower-extension). -/
structure TameRootChartExtension (p : ℕ) (E : Type u) [NormedField E]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (φ : ∀ X : Scheme.{u}, condensedRingObj Λ X ≅ ContinuousRingUniverse.coeff E X)
    {Y : Scheme.{u}} {A : Type u} [Finite A]
    {C : A → Y.IdealSheafData} {I : Finset A} (D : Y.IdealSheafData)
    (L : Mod (Sheaf (Scheme.ProEt.topology (tameBoundaryOpen D).toScheme) Ab.{u + 1})
      (condensedRingObj Λ (tameBoundaryOpen D).toScheme))
    (c : TameRootExtensionChart C I) where
  base : TameRootChartExtensionBase p E Λ φ D L c
  boundaryData : TameRootBoundaryData p E Λ φ D L c base

/-- Every actual root-compatible refinement inherits the extension and boundary action.
The isomorphism is normalized on the open part by the actual pullback of L.
Empty refinements are excluded: on the zero ring no root of order n > 1 is primitive
in Mathlib's sense, and an empty refinement carries no data.
Source: tame-boundary expansion, final refinement clause
(blueprint: lem-sfb-tame-root-tower-extension). -/
def TameRootChartExtension.Restricts
    {p : ℕ} {E : Type u} [NormedField E]
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    {φ : ∀ X : Scheme.{u}, condensedRingObj Λ X ≅ ContinuousRingUniverse.coeff E X}
    {Y : Scheme.{u}} {A : Type u} [Finite A] {C : A → Y.IdealSheafData} {I : Finset A}
    {D : Y.IdealSheafData}
    {L : Mod (Sheaf (Scheme.ProEt.topology (tameBoundaryOpen D).toScheme) Ab.{u + 1})
      (condensedRingObj Λ (tameBoundaryOpen D).toScheme)}
    {c : TameRootExtensionChart C I} (e : TameRootChartExtension p E Λ φ D L c) : Prop :=
  ∀ (c' : TameRootExtensionChart C I) (v : c'.U ⟶ c.U), Nonempty c'.U →
    WeaklyEtale v → IsAffineHom v → v ≫ c.toBase = c'.toBase →
    (∀ i, v.appTop (c.parameters i) = c'.parameters i) →
    ∀ (f : c'.tower p ⟶ c.tower p),
    f ≫ c.towerMap p = c'.towerMap p ≫ v →
    (∀ n i, f.appTop (fullParameterRootSection p c.parameters n i) =
      fullParameterRootSection p c'.parameters n i) →
    ∃ e' : TameRootChartExtension p E Λ φ D L c',
      (∀ n, e'.base.characters.roots n = v.appTop (e.base.characters.roots n)) ∧
      e'.boundaryData.model.rank = e.boundaryData.model.rank ∧
      HEq e'.boundaryData.model.representation e.boundaryData.model.representation ∧
      ∃ (q : e'.base.extension ≅ (CondensedRing.upperStar Λ f).obj e.base.extension)
        (ha : e'.base.action.act ≫ f = coefficientParameterMap f
          (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ I})) ≫ e.base.action.act),
      IsTameRootEquivariantIso Λ e'.base.action.act
        (coefficientParameterProjection (c'.tower p)
          (Profinite.of (ParameterRootDeckGroup p {a : A // a ∈ I})))
        e'.base.linearization.iso
        (coefficientLinearizationRestriction Λ e'.base.action.act e.base.action.act f ha
          (coefficientParameterProjectionCommutes f _)
          e.base.extension e.base.linearization.iso) q ∧
      (∃ (s : c'.boundary ⟶ c.boundary)
        (hi : e'.boundaryData.boundaryMap ≫ f = s ≫ e.boundaryData.boundaryMap),
        s ≫ c.boundaryToBase = c'.boundaryToBase ≫ v ∧
        s ≫ c.boundaryToStratum = c'.boundaryToStratum ∧
        HEq e'.boundaryData.model.boundaryBasis
          ((CondensedRing.upperStar Λ e'.boundaryData.boundaryMap).mapIso q ≪≫
            ((CondensedRing.upperStarComp Λ e'.boundaryData.boundaryMap f).app
              e.base.extension).symm ≪≫
            (CondensedRing.upperStarCongr Λ hi).app e.base.extension ≪≫
            (CondensedRing.upperStarComp Λ s e.boundaryData.boundaryMap).app e.base.extension ≪≫
            (CondensedRing.upperStar Λ s).mapIso e.boundaryData.model.boundaryBasis ≪≫
            coefficientFreePullbackIso Λ s e.boundaryData.model.rank)) ∧
      ∀ (fo : c'.punctured p D ⟶ c.punctured p D)
        (ho : c'.openInclusion p D ≫ f = fo ≫ c.openInclusion p D)
        (hw : fo ≫ c.toOpen p D = c'.toOpen p D),
        ((CondensedRing.upperStar Λ
          (c'.openInclusion p D)).mapIso q ≪≫
          ((CondensedRing.upperStarComp Λ
            (c'.openInclusion p D) f).app e.base.extension).symm ≪≫
          (CondensedRing.upperStarCongr Λ ho).app e.base.extension ≪≫
          (CondensedRing.upperStarComp Λ fo
            (c.openInclusion p D)).app e.base.extension ≪≫
          (CondensedRing.upperStar Λ fo).mapIso e.base.restriction ≪≫
          ((CondensedRing.upperStarComp Λ fo
            (c.toOpen p D)).app L).symm ≪≫
          (CondensedRing.upperStarCongr Λ hw).app L).hom =
            e'.base.restriction.hom

/-- The extension conclusion, using total disconnectedness derived from the given p-adic
norm rather than an additional hypothesis.
Source: tame-boundary expansion, all conclusions
(blueprint: lem-sfb-tame-root-tower-extension). -/
def TameRootTowerExtensionConclusion
    (p ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {Y : Scheme.{u}} {A : Type u} [Finite A] (D : Y.IdealSheafData) (C : A → Y.IdealSheafData)
    (L : Mod (Sheaf (Scheme.ProEt.topology (tameBoundaryOpen D).toScheme) Ab.{u + 1})
      (condensedRingObj (normContinuousRing E).X (tameBoundaryOpen D).toScheme))
    (I : Finset A) : Prop :=
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  ∃ (B : Scheme.Cover.{u} Scheme.proetalePrecoverage (ParameterStratum C I))
    (c : B.I₀ → TameRootExtensionChart C I)
    (b : ∀ a, B.X a ≅ (c a).boundary),
    (∀ a, (b a).hom ≫ (c a).boundaryToStratum = B.f a) ∧
    ∃ e : ∀ a, TameRootChartExtension p E (normContinuousRing E).X
      (tameCoefficientRealization E) D L (c a), ∀ a, (e a).Restricts

/-- Tame lisse finite-E coefficients extend continuously equivariantly over a covering
family of full parameter-root towers, with the stated boundary representations.
Source: blueprint main-20261015, ctf-stability direct-images proof (3), tame-boundary
expansion (blueprint: lem-sfb-tame-root-tower-extension).

Proof plan, following the node's ten steps:
1. Use lem-sfb-snc-universal-residual-charts for affine etale charts, their residual
pro-etale refinements, compatible roots and the covering of the whole reduced stratum.
2. Finite type over the field and the open-Noetherian lemma make W Noetherian; regular
implies normal. The internal/section-ring equivalence, continuous-field realization,
integral reduction equivalence and normal completed integral-model theorem give a
lisse lattice N and its normalized finite free quotients F_n.
3. On each punctured strict-local tower rational tameness trivializes L. The lattice
class sheaf GL_d(E)/GL_d(O_E), totally-disconnected realization and connectedness
make its lattice coset constant. Embedded-image normalization trivializes N and all
its finite reductions there; Cartesian coefficient pullback commutes with reduction.
4. Apply lem-sfb-snc-tame-finite-fibre-classification simultaneously to every F_n on
the same universal residual chart. Retain the actual compatible finite deck actions.
5. Apply lem-pod-adic-limit-finite-modules to Q_n. Lift compatible bases to show
Q = lim Q_n is finite free. The coordinatewise action is continuous; rationalizing
gives the continuous representation on M = E tensor Q, without a finite-image claim.
6. At each finite level root ratios are roots of unity. Comaximal factorization of
z^n-1 and Chinese remainders identify the actual torsor comparison; pass to the full
compatible-root limit. The deck group is the product of the q-adic integer groups.
7. The coefficient-section localization lemma identifies inverse image with slice
restriction, which preserves limits. Limit projections and reduction comparisons
identify L on T^circ with the continuous-function model of M, with its deck action.
8. Put the constant continuous M-model on all of T, and give it the representation
action. Setting all roots to zero defines i; rotations fix i, so boundary pullback
is exactly the same representation. This supplies the displayed matrix normalization.
9. Pointed refinements commute with every finite quotient and transition. The limit
universal property gives the restriction isomorphisms, normalized on the open part;
changes of compatible bases conjugate all matrices, giving isomorphic extensions.
10. With I empty the root algebra is the base ring and the group is trivial, so this
is a pro-etale trivialization. Zero rank, empty divisor, empty stratum and empty Y
are included, with the empty covering family when needed. -/
theorem tame_root_tower_extension
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra E Ω] [IsAlgClosure E Ω]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hY : IsRegularScheme Y)
    (A : Type u) [Finite A] (D : Y.IdealSheafData) (C : A → Y.IdealSheafData)
    (hD : IsStrictNormalCrossingsBoundary D)
    (hinj : Function.Injective (fun a ↦ (C a).support))
    (hcomp : ∀ a, IsIntegral (C a).subscheme ∧ IsRegularScheme (C a).subscheme)
    (hunion : D.support = ⨆ a, (C a).support)
    (hcross : ∀ J : Finset A, ∀ z : (⨆ a ∈ J, C a).subscheme,
      IsRegularScheme ((⨆ a ∈ J, C a).subscheme) ∧
      ringKrullDim (Y.presheaf.stalk ((⨆ a ∈ J, C a).subschemeι z)) =
        ringKrullDim ((⨆ a ∈ J, C a).subscheme.presheaf.stalk z) + (J.card : ℕ))
    (L : Mod (Sheaf (Scheme.ProEt.topology (tameBoundaryOpen D).toScheme) Ab.{u + 1})
      (condensedRingObj (normContinuousRing E).X (tameBoundaryOpen D).toScheme))
    (hL : IsLisseCoefficientModule (normContinuousRing E).X L)
    (htame : IsStrictLocalKummerTameModule p (normContinuousRing E).X D
      (tameBoundaryOpen D).ι L) (I : Finset A) :
    TameRootTowerExtensionConclusion p ℓ E D C L I := by
  sorry

end AlgebraicGeometry.ProEtale

