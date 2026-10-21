/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.CategoryTheory.CondensedDerivedInvariants
public import Sheaf.CategoryTheory.DerivedTensorRightExact
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Ordinary diagonal tensor on condensed internal actions

Source: main-20261015 direct-images proof (sk-thm-sf-ctf-stability-direct-images.proof.md),
paragraph (3), agent-formulated formal restriction and cup-product infrastructure;
exact reference wanted
(blueprint: def-sfb-condensed-action-tensor).

## Main definitions

* `ActionTensorData`, `actionTensor`: the relative internal-module tensor on actions of an
  arbitrary topological group, with diagonal action on generalized pure tensors, the strong
  forgetful comparison, ordinary symmetry, closed structure and flat resolutions.
* `TrivialTensorData`, `trivialTensor`: the strong tensor comparison of trivial inflation,
  identity on underlying module tensors and on the regular unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction (inflate trivial)
open CategoryTheory.CondensedBar
namespace CategoryTheory.CondensedDerivedRestriction
variable {A A' : CondensedBar.Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The pure-tensor section of the actual relative internal-module tensor product.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
def tensorSection {A : CondensedBar.Ring.{u}} (M N : Modules A) (S : Profinite.{u})
    (x : sections A M S) (y : sections A N S) : sections A (M ⊗ N) S :=
  (Mod.tensorObjπ M N).hom.app (op S)
    ((Functor.LaxMonoidal.μ
      (sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) M.X N.X).app
        (op S) (TensorProduct.tmul ℤ x y))


/-- The ordinary diagonal tensor on actions, specified by its underlying relative tensor
and its action on every generalized pure tensor. The strong forgetful comparison also
fixes associators and unitors; it is not a freely chosen tensor structure.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
structure ActionTensorData (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] where
  monoidal : MonoidalCategory (Equivariant A G)
  forgetCore : @Functor.CoreMonoidal (Equivariant A G) _ monoidal
    (Modules A) _ _ (CondensedBar.forgetAction (A := A) (G := G))
  diagonal : ∀ (M N : Equivariant A G) (S : Profinite.{u}) (g : C(S, G))
    (x : sections A M.module S) (y : sections A N.module S),
    (monoidal.tensorObj M N).act S g
      (((forgetCore.μIso M N).hom).hom.hom.app (op S)
        (tensorSection (A := A) M.module N.module S x y)) =
    ((forgetCore.μIso M N).hom).hom.hom.app (op S)
      (tensorSection (A := A) M.module N.module S (M.act S g x) (N.act S g y))
  symmetric : @SymmetricCategory (Equivariant A G) _ monoidal
  symmetry : ∀ M N : Equivariant A G,
    (forgetCore.μIso M N).hom ≫
        (@BraidedCategory.braiding (Equivariant A G) _ monoidal
          symmetric.toBraidedCategory M N).hom.val =
      (β_ M.module N.module).hom ≫ (forgetCore.μIso N M).hom
  closed : @MonoidalClosed (Equivariant A G) _ monoidal
  additive : @MonoidalPreadditive (Equivariant A G) _ _ monoidal
  flat : @Abelian.HasFunctorialFlatResolution (Equivariant A G) _ monoidal

/-- Existence of the usual diagonal tensor, closed structure, and functorial flat
resolutions on the action site. The tensor is determined up to the unique bilinear
comparison by the displayed pure-tensor and unit normalizations.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor).
Proof: tensor the underlying modules and give it the diagonal action; the universal
balanced bilinear map induces the action and its coherence. Internal Hom carries the
conjugation action and satisfies the tensor-Hom adjunction. On the action site sums of
free modules represented by test objects surject functorially and are flat; use these
for functorial flat resolutions. The signed total tensor and K-flat localization then
give the ordinary derived tensor, rather than a tensor on continuous cochains. -/
theorem actionTensorExist : Nonempty (ActionTensorData A G) := by
  sorry

/-- Choose the diagonal tensor with its displayed universal-property comparisons.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
def actionTensor (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : ActionTensorData A G :=
  Classical.choice (actionTensorExist (A := A) (G := G))

/-- The diagonal action tensor, with its ordinary internal-module tensor underneath.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance actionMonoidal : MonoidalCategory (Equivariant A G) := (actionTensor A G).monoidal

/-- Closedness is the ordinary internal Hom with conjugation action.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance actionClosed : MonoidalClosed (Equivariant A G) := (actionTensor A G).closed

/-- Symmetry is the ordinary interchange of the two module factors.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance actionSymmetric : SymmetricCategory (Equivariant A G) := (actionTensor A G).symmetric

/-- The tensor is additive on the original action-category morphisms.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance actionTensorAdditive : MonoidalPreadditive (Equivariant A G) :=
  (actionTensor A G).additive

/-- Flat resolutions on the action site for the specified tensor.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance actionFlat : Abelian.HasFunctorialFlatResolution (Equivariant A G) :=
  (actionTensor A G).flat


/-- Ordinary trivial action with its strong diagonal-tensor comparison. The comparison
is identity on the underlying module tensor and on the regular module.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
structure TrivialTensorData (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] where
  core : (trivial (R := A.toMon) (P := G)).CoreMonoidal
  tensor : ∀ M N, (core.μIso M N).hom.val =
      ((actionTensor A G).forgetCore.μIso
        ((trivial (R := A.toMon) (P := G)).obj M)
        ((trivial (R := A.toMon) (P := G)).obj N)).inv
  unit : core.εIso.hom.val = (actionTensor A G).forgetCore.εIso.inv

/-- The strong monoidal comparison for trivial action is fixed by its underlying tensor.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor).
Proof: both sides have trivial action on the ordinary tensor; the balanced bilinear
identity gives the tensor comparison, the regular-module identity gives the unit.
Coherence follows after forgetting the action, which is faithful. -/
theorem trivialTensorExist : Nonempty (TrivialTensorData A G) := by
  sorry

/-- Ordinary tensor comparison for trivial inflation, with identity underlying maps.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
def trivialTensor (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : TrivialTensorData A G :=
  Classical.choice (trivialTensorExist (A := A) (G := G))

/-- The usual strong monoidal trivial inflation.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance trivialMonoidal : (trivial (R := A.toMon) (P := G)).Monoidal :=
  (trivialTensor A G).core.toMonoidal

/-- Trivial action preserves colimits, computed on the underlying modules.
Source: paragraph (3), action-site presentation
(blueprint: def-sfb-condensed-action-tensor).
Proof: the action on the colimit of a diagram of trivial actions is trivial, and the
underlying colimit universal property is the equivariant universal property. -/
@[instance] theorem trivialColimitsAll :
    PreservesColimitsOfSize.{u + 1, u + 1} (trivial (R := A.toMon) (P := G)) := by
  sorry

/-- The small colimits used by total tensor comparisons are preserved by trivial action.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor).
Proof: shrink the underlying module colimit; the trivial-action colimit universal
property is the same equivariant universal property. -/
@[instance] theorem trivialSmallColimits :
    PreservesColimitsOfSize.{0, 0} (trivial (R := A.toMon) (P := G)) := by
  sorry


/-- Small colimits for the ordinary total tensor sums.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance moduleSmallColimits : HasColimitsOfSize.{0, 0} (Modules A) :=
  hasColimitsOfSizeShrink _

/-- Small colimits for the ordinary total tensor sums.
Source: paragraph (3) (blueprint: def-sfb-condensed-action-tensor). -/
instance actionSmallColimits : HasColimitsOfSize.{0, 0} (Equivariant A G) :=
  hasColimitsOfSizeShrink _

end CategoryTheory.CondensedDerivedRestriction
