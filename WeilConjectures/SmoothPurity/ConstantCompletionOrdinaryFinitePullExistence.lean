/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.RingTheory.Ideal.Defs
public import WeilConjectures.ProperBaseChange.ConstantCompletionCore
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionInverseImageSupplement
import all WeilConjectures.ProperBaseChange.ConstantCompletionOrdinaryPullComparison
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.ProperBaseChange.GeometricModuleConstruction
import WeilConjectures.ProperBaseChange.GeometricModuleTransport
import WeilConjectures.SmoothPurity.CochainInverseComparison
import WeilConjectures.SmoothPurity.CochainTensoratorExistence
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique

/-! A decomposition of the ordinary finite pullback comparison.
Source: Stacks Project, Tags 06YY and 099L.
(blueprint: lem-weil-pbc-constant-completion-ordinary-finite-pull-existence).
The existence and insertion-normalization part is isolated so that it can be
proved independently from the uniqueness argument. -/
@[expose] public noncomputable section
universe u
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)
variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]
attribute [local irreducible] completed derivedExtension SheafOfModules.monoidalCategory
  strictLimit ordinaryUnit quotientPresentation
attribute [local irreducible] derivedPull

-- Compose four normalization equations without unfolding any module constructions.
private theorem finiteInsertion_naturality {R S : Sheaf J CommRingCat.{u}}
    (c : R ⟶ S) {M N : Mod R} (f : M ⟶ N) :
    insertion c M ≫ (underlying S).map ((change c).map f) =
      (underlying R).map f ≫ insertion c N := by
  obtain ⟨am, h⟩ : ∃ am : change c ⊣ res c,
      ∀ M : Mod R, insertion c M = (underlying R).map (am.unit.app M) :=
    ⟨scalarAdj c, insertion_eq_unit c⟩
  rw [h, h]
  have hn := congrArg ((underlying R).map) (am.unit.naturality f)
  simp only [Functor.map_comp] at hn
  exact hn.symm

include V adj hL

set_option maxHeartbeats 800000 in
-- The proof forms two successive mates under four adjunctions.
end CategoryTheory.ConstantCompletion
