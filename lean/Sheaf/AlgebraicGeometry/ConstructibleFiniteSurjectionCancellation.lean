/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Constructibility descends through a finite surjection

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`lem-finrepair-finite-surjection-cancellation.md`, order 1598
(blueprint: lem-finrepair-finite-surjection-cancellation).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Constructibility of higher direct images descends through a finite surjection.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`,
`lem-finrepair-finite-surjection-cancellation.md`, statement and proof
(blueprint: lem-finrepair-finite-surjection-cancellation).

Proof plan:
1. For any module sheaf `Q`, the unit `Q → π_*π^*Q` is monic. On geometric stalks,
   `lemma-weil-pbc-finite-stalk-formula` and `lem-weil-pbc-inverse-image-stalk-germ`
   identify it with the diagonal into a nonempty finite product. Surjectivity supplies
   a lift of each geometric point. Exactness and conservativity of geometric stalks
   (`prop-weil-pbc-geometric-stalks-exact`, `lemma-weil-pbc-geometric-stalk-conservative`)
   detect the zero kernel, also in modules because kernels are computed sectionwise.
2. The finite map makes `Y` finite type over `k`. Starting with a constructible `F`,
   set `Q₀ = F`, `Gᵃ = π_*π^*Qₐ` and `Qₐ₊₁ = coker(Qₐ → Gᵃ)`. Constructible pullback,
   `lem-fin-finite-morphism`, and `thm-constructible-serre` keep all terms constructible.
   Quotient followed by the next unit defines an exact augmented resolution of `F`.
3. The composition spectral sequence (`lem-weil-pbc-grothendieck-spectral-sequence`)
   collapses because `lem-fin-finite-morphism` kills the positive higher direct images
   of the constructible sheaves `π^*Qₐ`. Hence `Rᵇf_*Gᵃ ≅ Rᵇ(fπ)_*π^*Qₐ`.
4. The Grothendieck abelian and enough-injectives nodes for module sheaves permit
   `lem-sp-cartan-eilenberg-exists` and `thm-sp-if-e1` to give the first-quadrant
   spectral sequence `E₁ᵃᵇ = Rᵇf_*Gᵃ` abutting to `Rᵃ⁺ᵇf_*F`.
5. The hypothesis `C(fπ)` makes every first-page term constructible.
6. By `thm-constructible-serre`, kernels, images and cokernels keep every later page
   constructible. At `(a,b)`, all differentials vanish for `r > max(a,b+1)`.
   Convergence (`def-sp-convergence`) gives, in each total degree, a finite filtration
   with constructible stable terms. Extension closure proves constructibility of
   the abutment. There is no uniform vanishing assertion. -/
theorem hasConstructibleHigherDirectImages_of_finite_surjective
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [S.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (hX : IsSmoothBaseChangeCoefficients N Λ X)
    (hS : IsSmoothBaseChangeCoefficients N Λ S)
    (hY : IsSmoothBaseChangeCoefficients N Λ Y)
    (f : X ⟶ S) (π : Y ⟶ X) [IsFinite π] [Surjective π]
    (h : HasConstructibleHigherDirectImages k N Λ hY hS (π ≫ f)) :
    HasConstructibleHigherDirectImages k N Λ hX hS f := by
  -- Convert to the source-library predicate, which uses finite-stalk constructibility
  -- and the unbounded derived functor in every integer degree.
  have hc : HasConstructibleDirectImages Λ (π ≫ f) := by
    intro F hF q
    have : Scheme.IsConstructibleSheaf F := hF
    by_cases hq : q < 0
    · exact Scheme.IsConstructibleSheaf.of_isZero
        (_root_.DerivedCategory.isZero_of_isGE _ 0 q hq
          (hX := Functor.isGE_rightDerivedFunctor_obj_singleFunctor _ F))
    · have hF' := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).2 hF
      have hq' := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
        (h q.toNat F hF')
      have : Scheme.IsConstructibleSheaf
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            (((lowerStar (ModuleCat.{u + 1} Λ) (π ≫ f)).rightDerivedFunctorPlus ⋙
              _root_.DerivedCategory.Plus.ι).obj
                ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
        change Scheme.IsConstructibleSheaf (higherDirectImage Λ (π ≫ f) q F)
        simpa only [Int.toNat_of_nonneg (le_of_not_gt hq)] using hq'
      exact Scheme.IsConstructibleSheaf.of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
          ((lowerStar (ModuleCat.{u + 1} Λ) (π ≫ f)).rightDerivedFunctorPlusCompatibility.app
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)))
  -- Resolve to finite order by the constructible sheaves π_*π^*Q. The general source
  -- resolution principle avoids constructing a full Cartan--Eilenberg spectral sequence.
  have hf : HasConstructibleDirectImages Λ f := by
    refine hasConstructibleDirectImages_of_exists_mono f fun Q hQ ↦ ?_
    have : Scheme.IsConstructibleSheaf Q := hQ
    have hG : Scheme.IsConstructibleSheaf
        ((upperStar (ModuleCat.{u + 1} Λ) π).obj Q) :=
      Scheme.IsConstructibleSheaf.upperStar π Q
    have hG' := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 hG
    have hpush := (finite_directImage_constructible_and_higher_vanishing
      k π N Λ hX _ hG').1
    have hpush' := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 hpush
    refine ⟨_, (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app Q,
      mono_unit_app_of_surjective Λ π π.surjective Q, hpush', ?_⟩
    -- Finite direct image is exact, so its ordinary and derived functors agree.
    let G := (upperStar (ModuleCat.{u + 1} Λ) π).obj Q
    let e := (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.mapIso
        (((lowerStar (ModuleCat.{u + 1} Λ) π).mapDerivedCategorySingleFunctor 0).app G).symm ≪≫
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.mapIso
        ((rightDerivedFunctorLowerStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} Λ) π).app _).symm ≪≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) π f).app _
    exact (Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S).prop_of_iso
      e.symm (hc _ hG)
  intro q F hF
  have hF' := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).1 hF
  have : Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((_root_.DerivedCategory.Plus.ι ⋙
          (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))) := hf F hF' q
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
  exact Scheme.IsConstructibleSheaf.of_iso
    ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusCompatibility.app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)).symm)

end AlgebraicGeometry.Etale
