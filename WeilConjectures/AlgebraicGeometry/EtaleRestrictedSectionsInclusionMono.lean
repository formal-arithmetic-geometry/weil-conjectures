/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleRestrictedTotalConstruction

/-! # Degreewise monicity of restricted sections

Source: Stacks Project, Tag 015J, total-complex comparison.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- The restricted sections inclusion is monic degreewise.
Source: Stacks Project, Tag 015J. -/
theorem etaleRestrictedSectionsInclusion_mono_component
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q n : ℤ) :
    Mono ((etaleRestrictedSectionsInclusion X K T q).f n) := by
  classical
  let F := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (ComplexShape.up ℕ) ⋙ ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}
  let J := ((CartanEilenbergPresentation.mappedFunctor
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})).obj
      (etaleRestrictedBicomplex X K T q)).flip
  let J₀ := ((CartanEilenbergPresentation.mappedFunctor
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})).obj T.I).flip
  let r := J₀.totalDesc (c₁₂ := ComplexShape.up ℤ) (i₁₂ := n)
    (fun a b h ↦ (F.map (T.I.πStupidTruncf (ComplexShape.embeddingUpIntGE q) b)).f a ≫
      J.ιTotal (ComplexShape.up ℤ) a b n h)
  have hr : (etaleRestrictedMappedInclusion X K T q).f n ≫ r = 𝟙 _ := by
    apply HomologicalComplex₂.total.hom_ext
    intro a b h
    dsimp [etaleRestrictedMappedInclusion]
    rw [HomologicalComplex₂.ιTotal_map_assoc]
    change (F.map (T.I.ιStupidTruncf (ComplexShape.embeddingUpIntGE q) b)).f a ≫
      (J₀.ιTotal (ComplexShape.up ℤ) a b n h ≫ r) =
      J.ιTotal (ComplexShape.up ℤ) a b n h ≫ 𝟙 _
    rw [HomologicalComplex₂.ι_totalDesc]
    rw [← Category.assoc, ← HomologicalComplex.comp_f, ← F.map_comp,
      HomologicalComplex.ιStupidTruncf_πStupidTruncf, F.map_id]
    simp
  have : Mono ((etaleRestrictedMappedInclusion X K T q).f n) :=
    mono_of_mono_fac hr
  dsimp [etaleRestrictedSectionsInclusion]
  infer_instance

end AlgebraicGeometry.Etale
