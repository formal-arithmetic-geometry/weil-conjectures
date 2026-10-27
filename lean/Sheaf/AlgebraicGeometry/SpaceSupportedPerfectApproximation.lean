/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Uniform supported perfect approximation on algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, Tags 08HI and 08HJ;
Cohomology on Sites, Tag 08FT
(blueprint: def-sfb-space-supported-perfect-approximation).

The existing small affine etale ringed model defines the derived category. Support
is tested on all etale charts lying in the complement, which is precisely vanishing
of the restriction to that open subspace. Quasi-compactness of the complement immersion
is tested by its inverse images in affine schemes. No quasi-compactness or separation
assumption on the space or its base is imposed by the definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Fixed-degree pseudo-coherence: a representative locally receives a bounded complex
of finite-free retracts, inducing cohomology isomorphisms above the given degree and
an epimorphism at that degree. Cover members have independent bounds and ranks.
Source: Stacks Project, Tag 08FT (and representative independence, Tag 08FU)
(blueprint: def-sfb-space-supported-perfect-approximation). -/
def IsMPseudoCoherent {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] (b : ℤ) (K : X.DerivedModules) : Prop :=
  ∃ E : CochainComplex X.SmallModules ℤ,
    Nonempty (K ≅ DerivedCategory.Q.obj E) ∧
    ∀ V : X.SmallEtaleModel, ∃ R : Sieve V, R ∈ X.smallEtaleModelTopology V ∧
      ∀ (U : X.SmallEtaleModel) (f : U ⟶ V), R f →
        ∃ F : CochainComplex (SheafOfModules.{u} (X.smallStructureRings.over U)) ℤ,
          (∃ a c : ℤ, ∀ n : ℤ, n < a ∨ c < n → IsZero (F.X n)) ∧
          Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite
            (X.smallStructureRings.over U) F) ∧
          ∃ α : F ⟶ ((SheafOfModules.overFunctor X.smallStructureRings U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E,
            (∀ i : ℤ, b < i → IsIso (HomologicalComplex.homologyMap α i)) ∧
            Epi (HomologicalComplex.homologyMap α b)

/-- A module sheaf vanishes outside `T` when its restriction to every etale chart
whose point image avoids `T` is zero. Such charts are exactly the small etale site
of the open complement; thus this is zero restriction, including for non-quasi-coherent
modules. The inverse model equivalence is the fixed one, not a choice of transport.
Source: Stacks Project, Tags 08HI, 08HJ and 03BZ
(blueprint: def-sfb-space-supported-perfect-approximation). -/
def ModuleSupportedOn {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Set (Point X.obj.obj)) (M : X.SmallModules) : Prop :=
  ∀ V : X.EtaleSite, Disjoint (Set.range (schemePointMap V.obj.hom)) T →
    IsZero ((X.etalePullback V).obj (X.smallModuleEquivalence.inverse.obj M))

/-- The supported approximation property A(X). For each closed support with
quasi-compact complement immersion, one integer works for every degree and every
quasi-coherent derived object satisfying the stated input bounds. The output is
perfect and supported in every degree; its cohomology map is epic at the cutoff.
Source: Stacks Project, Tags 08HI and 08HJ
(blueprint: def-sfb-space-supported-perfect-approximation). -/
def HasSupportedPerfectApproximation {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] : Prop :=
  ∀ T : Set (Point X.obj.obj), IsClosed T →
    (∀ (U : Over S), IsAffine U.left → ∀ a : yoneda.obj U ⟶ X.obj.obj,
      IsCompact (schemePointMap a ⁻¹' Tᶜ)) →
    ∃ r : ℤ, ∀ (m : ℤ) (F : X.DerivedModules),
      X.derivedQCohProperty F → X.IsMPseudoCoherent (m - r) F →
      (∀ i : ℤ, m - r ≤ i →
        X.ModuleSupportedOn T ((DerivedCategory.homologyFunctor X.SmallModules i).obj F)) →
      ∃ (P : X.DerivedModules) (v : P ⟶ F),
        SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
          X.smallStructureSheaf P ∧
        (∀ i : ℤ,
          X.ModuleSupportedOn T ((DerivedCategory.homologyFunctor X.SmallModules i).obj P)) ∧
        (∀ i : ℤ, m < i →
          IsIso ((DerivedCategory.homologyFunctor X.SmallModules i).map v)) ∧
        Epi ((DerivedCategory.homologyFunctor X.SmallModules m).map v)

end AlgebraicGeometry.AlgebraicSpace
