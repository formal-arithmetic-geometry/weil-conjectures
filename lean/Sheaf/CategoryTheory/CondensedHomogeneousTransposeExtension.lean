/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
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
import Sheaf.CategoryTheory.CondensedHomogeneousTransposeAlpha
import Sheaf.CategoryTheory.CondensedHomogeneousTransposeExtensionOfAlpha

/-! # Extending the identity-coordinate homogeneous transpose

Source: the internal homogeneous-function helper for blueprint direct-image stability,
paragraph (3); Stacks Tags 03EV, 03EO and 015Z
(blueprint: lem-sfb-internal-homogeneous-transpose-extension).

The free parameter, local pure tensors, normalized homogeneous model and whole-slice
Hom evaluations are the existing constructions. Injectivity is internal injectivity.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace Profinite.CondensedAction

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
variable (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The unique identity-coordinate transpose extends across the free-parameter tensor
of an equivariant monomorphism. Its extension formula holds on every profinite slice.

Source: blueprint direct-image stability, paragraph (3), internal homogeneous-function
helper; Stacks Tags 03EV (representable free-module flatness), 03EO (tensor-Hom
adjunction) and 015Z (injective extension)
(blueprint: lem-sfb-internal-homogeneous-transpose-extension).

Proof:
1. Apply lem-sfb-product-action-exact-forgetting to G to see that forgetting carries i
   to a monomorphism. Apply its free-module flatness to the profinite group G^n,
   including the trivial group for n = 0. Tensoring Ui with A[G^n] is therefore monic.
2. Identify H with its specified internal Hom. For x over S define a slice map on
   generators over each f : T → S by [t] ↦ h_T(f*x)(1,t). The free-module adjunction
   and lem-sfb-condensed-free-linearization-tensor extend this naturally and linearly
   through sheafification. It is linear in x because h and slice evaluation are linear.
3. Use lem-pe-internal-section-tensor-comparison and lem-pc-sheaf-modules-tensor-closed
   to transpose this map to alpha. Any other map with the displayed values has the
   same transpose on all generators on every slice, hence equals alpha by free
   generator detection and the bijective tensor-Hom adjunction.
4. Apply internal injectivity of UJ to alpha along the monomorphism of step 1. This
   supplies beta with (A[G^n] tensor Ui) followed by beta equal to alpha.
5. Evaluate the equality on the canonical local pure tensors. Tensor functoriality
   sends [t] tensor x to [t] tensor i(x); naturality of h and the slice evaluations
   gives the last formula after every base change T → S.
No sectionwise injectivity, projectivity, discreteness or finiteness is used.
-/
theorem homogeneous_transpose_extension
    (J : ActionModule R G) [Injective J.module] (n : ℕ)
    (H : HomogeneousFunctions R G J n) (N M : ActionModule R G)
    (i : N ⟶ M) [Mono i] (h : N ⟶ H.object) :
    Mono ((InternalBar.freePower R G n) ◁ i.val) ∧
    ∃ α : InternalBar.freePower R G n ⊗ N.module ⟶ J.module,
      (∀ (S : Profinite.{u}) (t : Fin n → C(S, G)) (x : sectionModule R N.module S),
        InternalBar.onSections R α S
            (InternalBar.pureTensor R _ _ S (InternalBar.generator R G n S t) x) =
          homogeneousEvaluate R G J n S
            ((H.internalHom.hom.val.app (op S)).hom (InternalBar.onSections R h.val S x))
            S (𝟙 S) (Fin.cons 1 t)) ∧
      (∀ α' : InternalBar.freePower R G n ⊗ N.module ⟶ J.module,
        (∀ (S : Profinite.{u}) (t : Fin n → C(S, G)) (x : sectionModule R N.module S),
          InternalBar.onSections R α' S
              (InternalBar.pureTensor R _ _ S (InternalBar.generator R G n S t) x) =
            homogeneousEvaluate R G J n S
              ((H.internalHom.hom.val.app (op S)).hom
                (InternalBar.onSections R h.val S x)) S (𝟙 S) (Fin.cons 1 t)) → α' = α) ∧
      ∃ β : InternalBar.freePower R G n ⊗ M.module ⟶ J.module,
        (InternalBar.freePower R G n) ◁ i.val ≫ β = α ∧
        ∀ (S T : Profinite.{u}) (f : T ⟶ S) (t : Fin n → C(T, G))
            (x : sectionModule R N.module S),
          InternalBar.onSections R β T
              (InternalBar.pureTensor R _ _ T (InternalBar.generator R G n T t)
                (InternalBar.onSections R i.val T ((N.module.X.obj.map f.op).hom x))) =
            homogeneousEvaluate R G J n S
              ((H.internalHom.hom.val.app (op S)).hom
                (InternalBar.onSections R h.val S x)) T f (Fin.cons 1 t) := by
  obtain ⟨hmono, ⟨α, hα, huniq⟩⟩ :=
    homogeneous_transpose_alpha R G J n H N M i h
  refine ⟨hmono, α, hα, huniq, ?_⟩
  exact homogeneous_transpose_extension_of_alpha R G J n H N M i h α hα

end Profinite.CondensedAction
