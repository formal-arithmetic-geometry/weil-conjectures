/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.CondensedHomogeneousFunctionsInjective
public import Sheaf.CategoryTheory.CondensedInternalBarResolution
public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.CategoryTheory.ProductActionExactForgetting
import Sheaf.CategoryTheory.InternalSectionTensorComparison

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace Profinite.CondensedAction

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
variable (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/--
The identity-coordinate transpose exists uniquely on the tensor of the free homogeneous
parameter with the source module. This is the construction and uniqueness part of the
five-step transpose-extension argument.

Source: the internal homogeneous-function helper for blueprint direct-image stability,
paragraph (3), Stacks Tags 03EV and 03EO.
(blueprint: lem-sfb-internal-homogeneous-transpose-alpha)

Proof: construct the slice map by evaluating the given homogeneous map at the identity
coordinate, extend it through the free-module and tensor--Hom adjunctions, and use free
generator detection on every profinite slice for uniqueness.
-/
theorem homogeneous_transpose_alpha
    (J : ActionModule R G) [Injective J.module] (n : ℕ)
    (H : HomogeneousFunctions R G J n) (N M : ActionModule R G)
    (i : N ⟶ M) [Mono i] (h : N ⟶ H.object) :
    Mono ((InternalBar.freePower R G n) ◁ i.val) ∧
    ∃ α : InternalBar.freePower R G n ⊗ N.module ⟶ J.module,
      (∀ (S : Profinite.{u}) (t : Fin n → C(S, G)) (x : sectionModule R N.module S),
        InternalBar.onSections R α S
            (InternalBar.pureTensor R _ _ S (InternalBar.generator R G n S t) x) =
          homogeneousEvaluate R G J n S
            ((H.internalHom.hom.val.app (op S)).hom
              (InternalBar.onSections R h.val S x))
            S (𝟙 S) (Fin.cons 1 t)) ∧
      (∀ α' : InternalBar.freePower R G n ⊗ N.module ⟶ J.module,
        (∀ (S : Profinite.{u}) (t : Fin n → C(S, G)) (x : sectionModule R N.module S),
          InternalBar.onSections R α' S
              (InternalBar.pureTensor R _ _ S (InternalBar.generator R G n S t) x) =
            homogeneousEvaluate R G J n S
              ((H.internalHom.hom.val.app (op S)).hom
                (InternalBar.onSections R h.val S x)) S (𝟙 S) (Fin.cons 1 t)) →
        α' = α) := by
  sorry

end Profinite.CondensedAction
