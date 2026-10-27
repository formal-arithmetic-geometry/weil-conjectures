/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import Sheaf.AlgebraicGeometry.EtaleAffineLinePullbackFull
import Sheaf.AlgebraicGeometry.EtaleSheafHomFamilyGluing

/-! # Existence of normalized shifted-line comparisons

This is the existence part of the gluing argument in the blueprint, separated from
rigidity and independence of comparisons. Affine-line fullness makes this existence
result valid for arbitrary sheaves placed in a common degree and arbitrary rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

namespace AlgebraicGeometry.Etale

/-- For arbitrary sheaves placed in a common degree, normalized local comparisons give
a normalized global comparison with the prescribed restrictions.
Source: blueprint sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md, Gluing;
Stacks Tags 0A3H, 015F, 06XS, 03EM, and 04TQ.
(blueprint: lem-trf-etale-shifted-line-comparison-existence).

Proof: shift both objects by -m and identify them with the sheaves in the hypotheses.
Exact inverse image preserves these single complexes and its compositors. Full faithfulness
of the single functor therefore turns the local isomorphisms into sheaf isomorphisms.
On the affine line over each pairwise fibre product, the ratio of the two comparisons
restricts to the identity at the unit section. Fullness of affine-line inverse image
lifts this ratio to an endomorphism on the base; its section restriction makes that
endomorphism the identity. Thus both the maps and their inverses agree on overlaps.
The affine-line base changes form an etale cover, so glue the maps and the inverses
by the sheaf morphism gluing theorem. Its uniqueness proves the inverse identities.
Testing on the original base cover proves normalization of the glued map. Undo the
shift and the chosen single-complex identifications to obtain the asserted comparison.
The sheaf gluing theorem includes the empty cover, and this proof uses no nonzero-ring
or reducedness hypothesis. -/
theorem exists_normalized_shifted_line_comparison (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u})
    (m : ℤ) (C : DerivedCategoryModule A S)
    (F : DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S))
    (hC : ∃ Q : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty (C⟦-m⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj Q))
    (hF : ∃ P : Sheaf (AffineSpace (ULift.{u} (Fin 1)) S).smallEtaleTopology
        (ModuleCat.{u + 1} A),
      Nonempty (F⟦-m⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj P))
    (θ : (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj F ≅ C)
    (cover : Scheme.Cover.{u} Scheme.etalePrecoverage S)
    (localIso : ∀ i : cover.I₀,
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))).leftDerivedFunctor.obj F ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) (cover.X i) ↘ cover.X i)).leftDerivedFunctor.obj
          ((upperStar (ModuleCat.{u + 1} A) (cover.f i)).leftDerivedFunctor.obj C))
    (hlocal : ∀ i : cover.I₀, sectionRestrictionIso (ModuleCat.{u + 1} A) (cover.f i)
      (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
      (AffineSpace.oneSection_comp_map (cover.f i))
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) (cover.X i))
      θ (localIso i) = Iso.refl _) :
    ∃ κ : F ≅ (L((AffineSpace (ULift.{u} (Fin 1)) S ↘ S)^*[ModuleCat.{u + 1} A])).obj C,
      (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) S)^*[ModuleCat.{u + 1} A])).map κ.hom ≫
        (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
          (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)).hom.app C = θ.hom ∧
      ∀ i : cover.I₀,
        (L((AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))^*[ModuleCat.{u + 1} A])).mapIso κ ≪≫
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
            (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i))
            (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).app C).symm ≪≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
            (AffineSpace (ULift.{u} (Fin 1)) (cover.X i) ↘ cover.X i) (cover.f i)
            (AffineSpace.map (ULift.{u} (Fin 1)) (cover.f i) ≫
              AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
            (AffineSpace.map_over (cover.f i))).app C = localIso i := by sorry

end AlgebraicGeometry.Etale
