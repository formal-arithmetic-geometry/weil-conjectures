/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-! # Detection of filtered colimits on the affine etale basis

## References

* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Affine etale evaluation detects a colimit cocone of module sheaves. -/
theorem nonempty_isColimit_of_affine_etale
    (Λ : Type (u + 1)) [CommRing Λ] (S : Scheme.{u})
    {J : Type u} [Category.{u} J]
    (K : J ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (B : Cocone K)
    (h : ∀ (V : S.Etale) [IsAffine V.left], Nonempty (IsColimit
      ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        (evaluation S.Etaleᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op V)).mapCocone B))) :
    Nonempty (IsColimit B) := by
  classical
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  let R := (Scheme.AffineEtale.Spec S).sheafPushforwardContinuous
    (ModuleCat.{u + 1} Λ) (Scheme.AffineEtale.topology S) S.smallEtaleTopology
  have : R.IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense.{u} (Scheme.AffineEtale.Spec S)
      (Scheme.AffineEtale.topology S) S.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let U := sheafToPresheaf (Scheme.AffineEtale.topology S) (ModuleCat.{u + 1} Λ)
  refine ⟨isColimitOfReflects R (isColimitOfReflects U ?_)⟩
  apply evaluationJointlyReflectsColimits
  intro V
  have : IsAffine ((Scheme.AffineEtale.Spec S).obj V.unop).left := by
    rw [Scheme.AffineEtale.Spec_obj_left]
    infer_instance
  exact (h ((Scheme.AffineEtale.Spec S).obj V.unop)).some

end AlgebraicGeometry.Etale
