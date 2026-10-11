/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTransport
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# Restriction of `𝔾ₘ`, `μₙ`, the Kummer sequence and line bundles along an étale monomorphism

Let `f : X ⟶ Y` be an étale monomorphism, for instance an isomorphism, and `R` the restriction
of étale sheaves along `f` (`AlgebraicGeometry.Scheme.etaleRestriction`). Then `R 𝔾ₘ = 𝔾ₘ`
(definitionally), `R μₙ ≅ μₙ` (`AlgebraicGeometry.Scheme.rootsOfUnityRestrictionIso`), and the
induced maps on cohomology `H^q(Y, -) ⟶ H^q(X, -)` commute with the Kummer maps
(`AlgebraicGeometry.Scheme.kummerδ₁_etaleRestrictionH`) and with the identification
`Pic = H¹(-, 𝔾ₘ)`, under which they are the pullback of line bundles
(`AlgebraicGeometry.Scheme.etaleRestrictionH_toCohomologicalPicardGroup`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]

lemma etaleRestriction_obj_gmSheaf : (etaleRestriction f).obj Y.gmSheaf = X.gmSheaf :=
  rfl

variable [Mono f]

/-- The restriction of `μₙ` is `μₙ`. -/
noncomputable def rootsOfUnityRestrictionIso (n : ℕ) :
    (etaleRestriction f).obj (Y.rootsOfUnitySheaf n) ≅ X.rootsOfUnitySheaf n :=
  PreservesKernel.iso (etaleRestriction f) (n • 𝟙 Y.gmSheaf) ≪≫
    kernelIsoOfEq (by rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]; rfl)

@[reassoc (attr := simp)]
lemma rootsOfUnityRestrictionIso_hom_ι (n : ℕ) :
    (rootsOfUnityRestrictionIso f n).hom ≫ kernel.ι (n • 𝟙 X.gmSheaf) =
      (etaleRestriction f).map (kernel.ι (n • 𝟙 Y.gmSheaf)) := by
  rw [rootsOfUnityRestrictionIso, Iso.trans_hom, Category.assoc, kernelIsoOfEq_hom_comp_ι,
    PreservesKernel.iso_hom, kernelComparison_comp_ι]

/-- The morphism from the restriction of the Kummer sequence of `Y` to that of `X`. -/
noncomputable def kummerSequenceRestriction (n : ℕ) :
    (Y.kummerSequence n).map (etaleRestriction f) ⟶ X.kummerSequence n where
  τ₁ := (rootsOfUnityRestrictionIso f n).hom
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := by
    change _ ≫ kernel.ι _ = (etaleRestriction f).map (kernel.ι _) ≫ 𝟙 _
    rw [Category.comp_id, rootsOfUnityRestrictionIso_hom_ι]
  comm₂₃ := by
    change 𝟙 _ ≫ (n • 𝟙 _) = (etaleRestriction f).map (n • 𝟙 _) ≫ 𝟙 _
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end AlgebraicGeometry.Scheme
