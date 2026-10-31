/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBase

/-!

# Extending the coefficients of a trait model over the generic base to its total space

Let `M` be a trait model of `X₁` over the generic base
(`NearbyCyclesModel.IsTraitModelOfGenericBase`): its generic fibre `𝒳_η` is an open of
`X₁ ×_F η`, and the identification `ε` of its geometric generic fibre factors through
`𝒳_η ⟶ X₁`. For a bounded constructible complex `A` on `X₁`, the
extension by zero along the open immersion `𝒳_η ⟶ 𝒳` of the pullback of `A` to `𝒳_η` is a
bounded constructible complex `B` on the total space with `j^* B ≅ ε^* A`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_extension_total`). This is the form of the
coefficients required by the generic-slicing identification
`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_traitSlice`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **The coefficients extend to the total space**: for a trait model `M` of `X₁` over the
generic base and a bounded constructible complex `A` on `X₁`, there is a bounded constructible
complex `B` on the total space `𝒳` with `j^* B ≅ ε^* A`: the extension by zero, along the open
immersion `𝒳_η ⟶ 𝒳` of the generic fibre, of the pullback of `A` along `𝒳_η ⟶ X₁`. -/
theorem IsTraitModelOfGenericBase.exists_extension_total
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁.left) Ab.{u + 1})
      (condensedRingObj Λ X₁.left))}
    (hA : boundedConstructible (condensedRingObj Λ X₁.left) A) :
    ∃ B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
        (condensedRingObj Λ M.total)),
      boundedConstructible (condensedRingObj Λ M.total) B ∧
        Nonempty (L((M.j)^*⟦Λ⟧).obj B ≅ L((M.ε)^*⟦Λ⟧).obj A) := by
  have hM := h.isTraitModelOver
  obtain ⟨w, -, -, hw⟩ := h.exists_openImmersion_genericFibre
  have := hM.isTraitModel.isNoetherian_total
  let a : pullback q (traitGenericSpec k') ⟶ M.total := pullback.fst _ _
  let s := genericFibreInclusion M q g hM.isPullback_j.w
  let e := w ≫ pullback.fst X₁.hom ι
  have hs : s ≫ a = M.j := genericFibreInclusion_fst _ _ _ _
  refine ⟨D((a)_!open⟦Λ⟧).obj (L((e)^*⟦Λ⟧).obj A),
    boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj Λ a _
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ e A hA), ⟨?_⟩⟩
  exact (leftDerivedUpperStarCompOfEq Λ hs).app _ ≪≫
    (L((s)^*⟦Λ⟧)).mapIso (asIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction'
      Λ a).unit.app _)).symm ≪≫ ((leftDerivedUpperStarCompOfEq Λ hw).app A).symm

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
