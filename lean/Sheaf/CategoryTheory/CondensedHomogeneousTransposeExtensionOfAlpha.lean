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
An identity-coordinate transpose extends along the tensorized underlying monomorphism.
This is the injective-extension and evaluation part of the transpose-extension argument.

Source: the internal homogeneous-function helper for blueprint direct-image stability,
paragraph (3), Stacks Tags 015Z and 03EV.
(blueprint: lem-sfb-internal-homogeneous-transpose-extension-of-alpha)

Proof: apply internal injectivity of the coefficient module to the monomorphism obtained
by tensoring the underlying equivariant monomorphism with the free parameter, then
 evaluate the resulting equality on canonical local pure tensors after every base change.
-/
theorem homogeneous_transpose_extension_of_alpha
    (J : ActionModule R G) [Injective J.module] (n : ℕ)
    (H : HomogeneousFunctions R G J n) (N M : ActionModule R G)
    (i : N ⟶ M) [Mono i] (h : N ⟶ H.object)
    (α : InternalBar.freePower R G n ⊗ N.module ⟶ J.module)
    (hα : ∀ (S : Profinite.{u}) (t : Fin n → C(S, G))
      (x : sectionModule R N.module S),
      InternalBar.onSections R α S
          (InternalBar.pureTensor R _ _ S (InternalBar.generator R G n S t) x) =
        homogeneousEvaluate R G J n S
          ((H.internalHom.hom.val.app (op S)).hom
            (InternalBar.onSections R h.val S x)) S (𝟙 S) (Fin.cons 1 t)) :
    ∃ β : InternalBar.freePower R G n ⊗ M.module ⟶ J.module,
      (InternalBar.freePower R G n) ◁ i.val ≫ β = α ∧
      ∀ (S T : Profinite.{u}) (f : T ⟶ S) (t : Fin n → C(T, G))
          (x : sectionModule R N.module S),
        InternalBar.onSections R β T
            (InternalBar.pureTensor R _ _ T (InternalBar.generator R G n T t)
              (InternalBar.onSections R i.val T
                ((N.module.X.obj.map f.op).hom x))) =
          homogeneousEvaluate R G J n S
            ((H.internalHom.hom.val.app (op S)).hom
              (InternalBar.onSections R h.val S x)) T f (Fin.cons 1 t) := by
  sorry

end Profinite.CondensedAction
