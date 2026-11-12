/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Generator.Basic

/-!
# Grothendieck abelian categories of ind-objects

Let `A` be a Grothendieck abelian category and `P` an essentially small property of objects of
`A`. If `P.ind` (the filtered colimits of objects satisfying `P`) contains zero and is closed under
kernels, cokernels, finite products and coproducts in `A`, then the full subcategory of `A`
defined by `P.ind` is Grothendieck abelian
(`CategoryTheory.ObjectProperty.isGrothendieckAbelian_ind_fullSubcategory`): it is abelian with
all small colimits computed in `A` (coproducts and cokernels), filtered colimits are exact since
they are computed in `A` and the inclusion is exact, and the objects satisfying `P` form a small
separating family, since every object of `P.ind` is a filtered colimit of such objects.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {A : Type u} [Category.{v} A] [Abelian A] (P : ObjectProperty A)

/-- If the filtered colimits of an essentially small family of objects of a Grothendieck abelian
category `A` form a subcategory containing zero and closed under kernels, cokernels, finite
products and coproducts, then this full subcategory is a Grothendieck abelian category
(blueprint `proposition-ind-constructible-sheaves--8`, abstract form). -/
theorem isGrothendieckAbelian_ind_fullSubcategory [IsGrothendieckAbelian.{w} A]
    [ObjectProperty.EssentiallySmall.{w} P] [(ind.{w} P).ContainsZero]
    [(ind.{w} P).IsClosedUnderKernels] [(ind.{w} P).IsClosedUnderCokernels]
    [(ind.{w} P).IsClosedUnderFiniteProducts]
    [∀ J : Type w, (ind.{w} P).IsClosedUnderColimitsOfShape (Discrete J)] :
    IsGrothendieckAbelian.{w} (ind.{w} P).FullSubcategory := by
  let Q := ind.{w} P
  have : HasColimitsOfSize.{w, w} A := IsGrothendieckAbelian.hasColimits.{w} A
  have : HasCoproducts.{w} Q.FullSubcategory := fun J ↦
    hasColimitsOfShape_of_closedUnderColimits (Discrete J) Q
  have : HasColimitsOfSize.{w, w} Q.FullSubcategory :=
    has_colimits_of_hasCoequalizers_and_coproducts
  have : ∀ ⦃X Y : Q.FullSubcategory⦄ (f : X ⟶ Y), PreservesLimit (parallelPair f 0) Q.ι :=
    Q.preservesKernels_ι
  have : ∀ ⦃X Y : Q.FullSubcategory⦄ (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) Q.ι :=
    Q.preservesCokernels_ι
  have : PreservesFiniteLimits Q.ι := Functor.preservesFiniteLimits_of_preservesKernels _
  have : PreservesFiniteColimits Q.ι := Functor.preservesFiniteColimits_of_preservesCokernels _
  have : PreservesColimitsOfSize.{w, w} Q.ι :=
    preservesColimits_of_preservesCoequalizers_and_coproducts _
  have hsep : HasSeparator Q.FullSubcategory := by
    obtain ⟨S, _, hSP, hPS⟩ := EssentiallySmall.exists_small_le.{w} P
    obtain ⟨ι, X, rfl⟩ := Small.exists_eq_ofObj.{w} S
    let G : ι → Q.FullSubcategory := fun i ↦ ⟨X i, le_ind _ _ (hSP _ (ofObj_apply X i))⟩
    refine ⟨∐ G, IsSeparating.isSeparator_coproduct fun Y Z f g hfg ↦ ?_⟩
    obtain ⟨J, _, _, pres, hpres⟩ := Y.property
    refine Q.hom_ext (pres.isColimit.hom_ext fun j ↦ ?_)
    obtain ⟨_, ⟨i⟩, ⟨e⟩⟩ := hPS _ (hpres j)
    have := hfg (G i) (ofObj_apply G i) (Q.homMk (e.inv ≫ pres.ι.app j))
    rw [← cancel_epi e.inv]
    simpa [FullSubcategory.comp_hom] using congrArg InducedCategory.Hom.hom this
  refine { hasSeparator := hsep, ab5OfSize := ⟨fun J _ _ ↦ ?_⟩ }
  exact HasExactColimitsOfShape.domain_of_functor J Q.ι

end CategoryTheory.ObjectProperty
