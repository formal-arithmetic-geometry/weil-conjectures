/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.FiniteSiteInternalHomComparisonAffine
import WeilConjectures.AlgebraicGeometry.SixFunctors.SiteHomComparisonThick
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.DerivedCategory

open Scheme

/-- Invertibility of the comparison on an open implies invertibility of its restriction
from the ambient scheme. Use the canonical restriction equation and cancel its
internal-Hom and pullback identifications (Stacks Tags 08JB, 07A4). -/
private theorem isIso_comparison_restriction
    (A : Type (u + 1)) [CommRing A] [Finite A] {T : Scheme.{u}} (U : T.Opens)
    (K M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (h : IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) U
      ((Etale.upperStar (ModuleCat.{u + 1} A) U.ι).mapDerivedCategory.obj K)
      ((Etale.upperStar (ModuleCat.{u + 1} A) U.ι).mapDerivedCategory.obj M))) :
    IsIso ((ProEtale.upperStar (ModuleCat.{u + 1} A) U.ι).mapDerivedCategory.map
      (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K M)) := by
  let V : T.Etale := MorphismProperty.Over.mk ⊤ U.ι inferInstance
  obtain ⟨he, hp, hs⟩ := siteHomComparison_restriction A T V K M
  let e := siteHomRestrictionSquare A T V
  have hV : IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) V.left
      ((siteHomEtaleRestriction A T V).obj K)
      ((siteHomEtaleRestriction A T V).obj M)) := h
  have hcomp : IsIso (e.hom.app (((Etale.derivedHom (ModuleCat.{u + 1} A) T).obj
      (op K)).obj M) ≫
      (siteHomProEtaleRestriction A T V).map
        (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K M) ≫
      siteHomProEtaleRestrictionHom A T V
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj K)
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M)) := by
    rw [← hs]
    infer_instance
  have hrest : IsIso ((siteHomProEtaleRestriction A T V).map
      (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K M) ≫
      siteHomProEtaleRestrictionHom A T V
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj K)
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M)) :=
    IsIso.of_isIso_comp_left (e.hom.app _) _
  exact (isIso_comp_right_iff _
    (siteHomProEtaleRestrictionHom A T V
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj K)
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M))).1 hrest

/-- Local-to-global step of the finite-site internal-Hom comparison: if the comparison of the
restrictions is an isomorphism on every affine open of `T`, it is an isomorphism on `T`.

Source: Bhatt--Scholze, The pro-étale topology for schemes, Lemma 6.3.16, printed p. 48
(blueprint: new-sfb-finite-site-internal-hom-local; step 2 of
lem-sfb-finite-site-internal-hom-comparison).

Proof in words. Being an isomorphism in `D(T_proet, A)` is local on `T`: the cohomology
sheaves of the cone vanish iff they vanish on each member of an affine open cover. Restriction
to the slice `T_proet/X ≃ X_proet` is exact with exact left adjoint (extension by zero), and by
the weakly-étale localization and the pullback-comparison coherence `c_r` it carries the
comparison `γ_{K,M}` to the comparison `γ_{K|_X, M|_X}` of the affine open `X`, up to the
canonical identifications of `(ν_T^* -)|_X` with `ν_X^*(-|_X)` and of the restricted internal
Homs. Hence `γ_{K,M}|_X` is an isomorphism for every affine open `X`, and so is `γ_{K,M}`. -/
theorem isIso_finiteSiteInternalHomComparison_of_affine_opens
    (A : Type (u + 1)) [CommRing A] [Finite A] {T : Scheme.{u}} [IsNoetherian T]
    (K M : _root_.DerivedCategory
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : Etale.DerivedCategory.isBoundedConstructible A T K)
    (hKtor : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn A T a b K)
    (hM : ∃ N : ℤ, M.IsGE N)
    (hAffine : ∀ (X : T.Opens), IsAffine X →
      IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X
        ((Etale.upperStar (ModuleCat.{u + 1} A) X.ι).mapDerivedCategory.obj K)
        ((Etale.upperStar (ModuleCat.{u + 1} A) X.ι).mapDerivedCategory.obj M))) :
    IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K M) := by
  have _ := hK
  have _ := hKtor
  have _ := hM
  let U : T.affineOpens → T.Opens := fun i ↦ i.1
  have hU : ∀ x : T, ∃ i, x ∈ U i := fun x ↦
    TopologicalSpace.Opens.mem_iSup.mp ((iSup_affineOpens_eq_top T).ge (Set.mem_univ x))
  obtain ⟨C, g, δ, hC⟩ := Pretriangulated.distinguished_cocone_triangle
    (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) T K M)
  apply (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hC).1
  apply isZero_of_forall_isZero_mapDerivedCategory_upperStar (ModuleCat.{u + 1} A) U hU
  intro i
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
    ((ProEtale.upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategory.map_distinguished
      _ hC)).2 (isIso_comparison_restriction A (U i) K M (hAffine (U i) i.2))

end AlgebraicGeometry.ProEtale.DerivedCategory
