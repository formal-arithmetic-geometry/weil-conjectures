/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.Compactification.NagataDensityNormalizationSetup
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.ProEtaleModuleObjects
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.SheafificationTensorLocalIso
import Sheaf.CategoryTheory.SheafTensorStructure
import Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Extension by zero through the schematic closure

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-nagata-density-normalization/det-nagata-density-normalization-sheaves.md`.
(blueprint: det-nagata-density-normalization-sheaves).

The base-change inverse is fixed by its adjunction transpose, and the forward
comparison is the specified closed-pullback unit followed by that base change.
The complex and derived clauses use that very morphism, without boundedness.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Pullback composition for the actual schematic-image factorization j = j_Z ; i.
Source: blueprint density-normalization sheaves, base-change clause
(blueprint: det-nagata-density-normalization-sheaves).
This uses the existing coefficient-compatible pullback comparison, so its mate
is the canonical open-extension base change, rather than an arbitrary isomorphism. -/
noncomputable def nagataClosurePullbackComparison {X S : Scheme.{u}} {f : X ⟶ S}
    (c : Compactification f) :
    upperStar Λ c.i ≅ upperStar Λ c.i.imageι ⋙ upperStar Λ c.i.toImage :=
  eqToIso (congrArg (upperStar Λ) c.i.toImage_imageι.symm) ≪≫
    upperStarComp Λ c.i.toImage c.i.imageι

/-- Extension through the schematic closure, with the actual unit, canonical
base change, its natural comparison, and the same map on unbounded complexes and
in the derived category.
Source: blueprint main-20261015, density-normalization sheaves, entire statement
(blueprint: det-nagata-density-normalization-sheaves).

Proof: (1) nagataDensityNormalizationSetup supplies the qcqs schemes, complementary
open V, quasi-compact open j_Z, and Cartesian image square; Noetherian opens make
j and j_V quasi-compact. The condensed coefficients use the standing commutative
convention of the cited module operations. (2) Apply
sheafification_tensor_local_iso and sectionModuleEquivalence to the pulled-back
coefficient rings; internal_module_operations_transport identifies the additive
exact equivalences, operations, and actual adjunction units. (3) Transport
proEtale_openClosed_sequence_ring_sheaf to get exact i_*, j_!, j_Z,! and the
localization sequence 0 -> j_V,! j_V^* N -> N -> i_* i^* N -> 0. Closed pullback
is exact by closed_inverseImage_preserves_limits. (4) Open-extension base change
in the Cartesian image square gives beta; its inverse is the transpose of the
open unit followed by pullback composition, as explicitly normalized below.
(5) Base change to V gives j_V^* j_! M = 0 since X times V is empty. (6) Apply
the localization sequence to j_! M: the actual closed unit is mono and epi in
an abelian category and hence invertible. Compose with i_* beta to get theta,
natural in M. (7) Apply theta in every integer degree. Naturality makes it a
chain map and its inverse a chain map. Localization Q takes this very chain
isomorphism to an isomorphism in the unbounded derived category; equivalently
use exact-functor-derived-factorization and localization-universal-property.
-/
theorem nagataDensityNormalizationSheaves {X S : Scheme.{u}} (f : X ⟶ S)
    (c : Compactification f) [IsNoetherian c.Z]
    [HasDerivedCategory.{w}
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology c.Z) Ab.{u + 1})
        (condensedRingObj Λ c.Z))] :
    (∀ M, IsIso ((upperStarLowerStarAdjunction Λ c.i.imageι).unit.app
      ((openImmersionLowerShriek Λ c.i).obj M))) ∧
    ∃ β : openImmersionLowerShriek Λ c.i ⋙ upperStar Λ c.i.imageι ≅
        openImmersionLowerShriek Λ c.i.toImage,
      (∀ M, β.inv.app M =
        ((openImmersionLowerShriekUpperStarAdjunction Λ c.i.toImage).homEquiv M
          ((upperStar Λ c.i.imageι).obj ((openImmersionLowerShriek Λ c.i).obj M))).symm
            ((openImmersionLowerShriekUpperStarAdjunction Λ c.i).unit.app M ≫
              (nagataClosurePullbackComparison Λ c).hom.app
                ((openImmersionLowerShriek Λ c.i).obj M))) ∧
      ∃ θ : openImmersionLowerShriek Λ c.i ≅
          openImmersionLowerShriek Λ c.i.toImage ⋙ lowerStar Λ c.i.imageι,
        (∀ M, θ.hom.app M =
          (upperStarLowerStarAdjunction Λ c.i.imageι).unit.app
              ((openImmersionLowerShriek Λ c.i).obj M) ≫
            (lowerStar Λ c.i.imageι).map (β.hom.app M)) ∧
        ∀ K : CochainComplex
            (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj Λ X)) ℤ,
          IsIso ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K) ∧
          IsIso (DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
