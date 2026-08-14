/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Transport of `HasSheafCompose` along a `1`-hypercover dense subsite

Let `F₀ : C₀ ⥤ C` be a `1`-hypercover dense subsite for topologies `J₀` on `C₀` and
`J` on `C`, and let `F : A ⥤ B` be a functor. If postcomposition with `F` preserves
`J₀`-sheaves and `F` preserves the limits appearing in the `1`-hypercover sheaf
conditions, then postcomposition with `F` also preserves `J`-sheaves.

This applies in particular when `(C, J)` is a large site admitting a `1`-hypercover
dense subsite indexed by an essentially small category, such as the small étale site
of a scheme with its small affine étale subsite: the instance
`hasSheafCompose_of_preservesLimitsOfSize` does not apply directly to `J` because the
covering sieves of `J` are indexed by a large type, but it does apply to `J₀`, and
this file transports the conclusion to `J`.

## Main results

- `CategoryTheory.PreOneHypercover.multicospanComp`: the multicospan attached to a
  pre-`1`-hypercover and a presheaf of the form `P ⋙ F` is isomorphic to the
  composition with `F` of the multicospan attached to `P`.
- `CategoryTheory.GrothendieckTopology.hasSheafCompose_of_isOneHypercoverDense`:
  the transport of `HasSheafCompose` described above.

-/

@[expose] public section

universe w v₀ v v₁ v₂ u₀ u u₁ u₂

namespace CategoryTheory

open Limits Opposite

namespace PreOneHypercover

variable {C : Type u} [Category.{v} C] {S : C} (E : PreOneHypercover.{w} S)
  {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  (F : A ⥤ B) (P : Cᵒᵖ ⥤ A)

/-- The multicospan associated to a pre-`1`-hypercover `E` and a presheaf of the form
`P ⋙ F` is isomorphic to the composition of the multicospan associated to `E` and `P`,
composed with `F`. -/
@[simps!]
def multicospanComp : (E.multicospanIndex (P ⋙ F)).multicospan ≅
    (E.multicospanIndex P).multicospan ⋙ F :=
  NatIso.ofComponents
    (fun t => match t with
      | WalkingMulticospan.left _ => Iso.refl _
      | WalkingMulticospan.right _ => Iso.refl _)
    (by
      rintro (a | b) (a | b) (f | f | f)
      all_goals cat_disch)

/-- Mapping the multifork associated to a pre-`1`-hypercover `E` and a presheaf `P`
with respect to a functor `F` is isomorphic (up to a natural isomorphism of the
underlying functors) to the multifork associated to `E` and `P ⋙ F`. -/
def mapMultifork :
    F.mapCone (E.multifork P) ≅
      (Limits.Cone.postcompose (E.multicospanComp F P).hom).obj (E.multifork (P ⋙ F)) :=
  Cone.ext (Iso.refl _) (by
    rintro (a | b)
    all_goals
      simp [multicospanComp])

end PreOneHypercover

namespace GrothendieckTopology

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C : Type u} [Category.{v} C]
  (F₀ : C₀ ⥤ C) (J₀ : GrothendieckTopology C₀) (J : GrothendieckTopology C)
  {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- Transport of `HasSheafCompose` along a `1`-hypercover dense subsite: if
`F₀ : C₀ ⥤ C` is a `1`-hypercover dense subsite and postcomposition with `F : A ⥤ B`
preserves sheaves on `(C₀, J₀)`, then it preserves sheaves on `(C, J)`, provided `F`
preserves the limits appearing in the `1`-hypercover sheaf conditions. -/
lemma hasSheafCompose_of_isOneHypercoverDense
    [F₀.IsOneHypercoverDense.{w} J₀ J] [F₀.IsDenseSubsite J₀ J]
    (F : A ⥤ B) [J₀.HasSheafCompose F] [PreservesLimitsOfSize.{w, w} F] :
    J.HasSheafCompose F where
  isSheaf P hP := by
    rw [Functor.OneHypercoverDenseData.isSheaf_iff
      (fun X => F₀.oneHypercoverDenseData J₀ J X)] at hP ⊢
    obtain ⟨hP₀, hlim⟩ := hP
    refine ⟨GrothendieckTopology.HasSheafCompose.isSheaf (F := F) _ hP₀, fun X => ?_⟩
    obtain ⟨h⟩ := hlim X
    replace h := isLimitOfPreserves F h
    replace h := Limits.IsLimit.ofIsoLimit h
      (((F₀.oneHypercoverDenseData J₀ J X).toOneHypercover.toPreOneHypercover).mapMultifork F P)
    exact ⟨Limits.IsLimit.postcomposeHomEquiv
      (((F₀.oneHypercoverDenseData J₀ J X).toOneHypercover.toPreOneHypercover).multicospanComp
        F P) _ h⟩

end GrothendieckTopology

end CategoryTheory
