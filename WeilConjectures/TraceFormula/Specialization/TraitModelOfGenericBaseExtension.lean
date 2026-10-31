/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBaseFiniteness

/-!

# Extension of complexes on the base of a trait model over a generic base

Let `M` be a trait model of an `F`-scheme `X₁` over the generic base `(F, X₁)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase`). For a bounded constructible complex `K` on `X₁`,
the restriction `Lε^* K` to the geometric generic fibre extends to a bounded constructible complex
on the total space `𝒳`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_boundedConstructible_extension`): the extension
by zero `B = v_! A` along the open immersion `v : 𝒳_η ⟶ 𝒳` of the pullback `A` of `K` to the
generic fibre, as in the proof of
`NearbyCyclesModel.IsTraitModelOfGenericBase.preservesBoundedConstructible`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] {X' : Over (Spec (.of k'))}
  {F : Type u} [Field F]

set_option maxHeartbeats 1000000 in
-- the chain of identifications of derived pullbacks is a large term
/-- **Complexes on the base of a trait model over a generic base extend to the total space**: for
bounded constructible `K` on `X₁`, there is a bounded constructible `B` on the total space `𝒳`
with `Lj^* B ≅ Lε^* K`. It is the extension by zero `B = v_! A` along the open immersion
`v : 𝒳_η ⟶ 𝒳` of the pullback `A` of `K` to the generic fibre: `j` factors through `v` and
`Lv^* v_! A ≅ A`. -/
theorem IsTraitModelOfGenericBase.exists_boundedConstructible_extension
    {X₁ : Over (Spec (.of F))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
    {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X₁.left))}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X₁.left) K) :
    ∃ B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total)),
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total) B ∧
        Nonempty (L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B ≅
          L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K) := by
  obtain ⟨w, -, -, hw⟩ := h.exists_openImmersion_genericFibre
  have hM := h.isTraitModelOver.isTraitModel
  have := hM.isNoetherian_total
  let v := pullback.fst q (traitGenericSpec k')
  let s := genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w
  let A := (L((w ≫ pullback.fst _ _)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K
  have hB := boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj
    (Profinite.padicAlgClRingObj ℓ) v A
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ K hK)
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) v).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have e₁ := (nonempty_leftDerivedUpperStar_obj_iso_of_eq (Profinite.padicAlgClRingObj ℓ)
    (genericFibreInclusion_fst M q g h.isTraitModelOver.isPullback_j.w).symm
    ((D((v)_!open⟦Profinite.padicAlgClRingObj ℓ⟧)).obj A)).some
  have e₂ := (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) s v).app
    ((D((v)_!open⟦Profinite.padicAlgClRingObj ℓ⟧)).obj A)
  have e₃ := (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion
    (Profinite.padicAlgClRingObj ℓ) v).app ((D((v)_!open⟦Profinite.padicAlgClRingObj ℓ⟧)).obj A)
  have e₄ := asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj ℓ) v).unit.app A)
  have e₅ := (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) s
    (w ≫ pullback.fst _ _)).app K
  have e₆ := (nonempty_leftDerivedUpperStar_obj_iso_of_eq (Profinite.padicAlgClRingObj ℓ) hw K).some
  refine ⟨(D((v)_!open⟦Profinite.padicAlgClRingObj ℓ⟧)).obj A, hB, ⟨?_⟩⟩
  exact e₁ ≪≫ e₂ ≪≫
    (L((s)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso (e₃ ≪≫ e₄.symm) ≪≫ e₅.symm ≪≫ e₆

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
