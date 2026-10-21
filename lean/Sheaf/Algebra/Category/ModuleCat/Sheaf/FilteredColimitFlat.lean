/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Category.Preorder
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-! # Filtered colimits of flat module sheaves

Source: Stacks Project, Modules on Sites, Tag 03EU, part (2), and Tag 03EP, part (2)
(blueprint: lem-sfb-filtered-colimit-flat-module-sheaves).

The cocone is arbitrary. The comparison uses the canonical localized sheaf tensor,
and its finite index category is allowed to be empty.
-/

@[expose] public section

universe uC vC w uK

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

set_option autoImplicit false

/-- A directed colimit of flat module sheaves is flat, and its left tensor functor
has invertible canonical finite-limit comparisons, including for the empty diagram.
Source: Stacks Project, Modules on Sites, Tag 03EU, part (2), using Tag 03EP, part (2)
(blueprint: lem-sfb-filtered-colimit-flat-module-sheaves).

Proof:
1. The small-site Grothendieck clause of `prop-pur-kinjective-resolutions-exist`
   makes module sheaves Grothendieck abelian with coefficient-small Hom sets.
   A nonempty directed poset is filtered, so
   `lem-sfb-grothendieck-filtered-finite-limits` says its colimit functor preserves
   finite limits (`def-weil-pbc-category-colimit`).
2. Tensor preservation of coefficient-small colimits
   (`lem-weil-pbc-independent-sheaf-tensor-colimits`), followed by symmetry
   (`lem-pc-sheaf-modules-tensor-closed`), identifies colim_i (F_i tensor X)
   canonically with c.pt tensor X. Checking on each colimit leg proves naturality in X.
3. Each flat stage preserves finite limits (`def-pc-flat-sheaf-modules`).
   Symmetry puts the stage on the left. The finite-limit comparisons commute with
   transitions: their projections are the transition tensored with the limit projection.
4. Compose the inverse tensor-colimit comparison, the colimit of the stage
   finite-limit comparisons, the filtered-colimit/finite-limit comparison, and
   the limit of the tensor-colimit comparisons. Each is an isomorphism.
5. Checking each projection after each colimit leg identifies this composite with
   `limit.post`. For an empty diagram the same limit uniqueness argument has no
   projection equations; preservation of the terminal object is included
   (`def-galois-finite-limits-colimits`).
6. Tensor preserves finite colimits by `lem-weil-pbc-independent-sheaf-tensor-colimits`.
   Together with finite-limit preservation this gives exactness; symmetry yields
   the right-tensor exactness defining `IsFlatOnSite`. All tensors and colimits
   are those of module sheaves (`def-pur-sheaf-tensor-product`), so no points or
   sectionwise-flatness assumption is used. -/
theorem isFlatOnSite_of_isColimit_directed
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    {I : Type w} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (c : Cocone F) (hc : IsColimit c)
    (hflat : ∀ i : I, IsFlatOnSite (J := J) (R := R) (F.obj i)) :
    IsFlatOnSite (J := J) (R := R) c.pt ∧
      ∀ (K : Type uK) [SmallCategory K] [FinCategory K]
        (D : K ⥤ SheafOfModules.{w}
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)),
        IsIso (limit.post D (tensorLeft c.pt)) := by
  sorry

end SheafOfModules
