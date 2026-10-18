/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteBoundary
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Recovering bounded constructibility at a finite boundary

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-boundary-reconstruction.md`
(blueprint: lem-fin-finite-boundary-reconstruction).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A bounded below étale complex is bounded constructible if its open restriction and
proper direct image are bounded constructible, and the closed boundary is finite over the
base. Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`lem-fin-finite-boundary-reconstruction.md`
(blueprint: lem-fin-finite-boundary-reconstruction).

Proof plan:
1. The finite-type schemes over the field are Noetherian; so is the finite boundary over S
   (`lem-weil-pbc-finite-type-over-noetherian`, `def-weil-finite-integral-morphism`).
2. Open-closed recollement gives the triangle A → K → C → A[1], with A = a_!a^*K and
   C = i_*i^*K (`lem-cbc-open-closed-recollement`). Exact inverse image and closed direct
   image identify C with Ri_*i^*K (`prop-weil-pbc-inverse-image-modules-exact`,
   `lem-weil-pbc-exact-functor-derived-functor`).
3. Exact extension by zero preserves the cohomology and finite support interval of a^*K,
   making A bounded constructible (`lem-fin-extension-by-zero`,
   `lem-weil-pbc-extension-by-zero-exact`, `lem-weil-pbc-exact-functor-complex-cohomology`).
4. Apply Rb_* to the triangle. K-injective resolutions on a small-site skeleton and bounded
   below injective representatives identify the triangulated right derived functor with
   the bounded below pushforward (`lem-pc-right-derived-functor-triangulated`,
   `def-weil-size-convention`, `prop-pur-kinjective-resolutions-exist`,
   `lem-weil-pbc-kinjective-total-derived`, `lem-weil-pbc-dplus-injective-representative`,
   `def-weil-pbc-direct-image`). Derived composition identifies the third term with
   R(bi)_*i^*K (`lem-weil-derived-direct-image-composition`, ordinary étale clause).
5. Proper pushforward makes Rb_*A bounded constructible
   (`lem-fin-proper-bounded-constructible`). Together with the hypothesis on Rb_*K, the
   long exact cohomology sequence bounds the third term: if both supports lie in [r,s],
   its support lies in [r-1,s] (`lem-sf-derived-homology-long-exact`). Now use the
   triangulated constructible subcategory (`prop-constructible-derived-subcategory`).
6. Exact inverse image preserves the lower bound of K. Finite reflection therefore makes
   i^*K bounded constructible (`lem-fin-finite-reflects-derived`).
7. Exact closed direct image makes C bounded constructible (`lem-fin-closed-immersion`).
   The original triangle first bounds K by the cohomology long exact sequence and then
   proves its constructibility by the triangulated constructible subcategory. -/
theorem isBoundedConstructible_of_finite_boundary
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {Y S G Z : Scheme.{u}}
    [Y.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (b : Y ⟶ S) [b.IsOver (Spec (.of k))] [IsProper b]
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ S)
    (a : G ⟶ Y) [IsOpenImmersion a] (i : Z ⟶ Y) [IsClosedImmersion i]
    (hcomplement : Set.range i.base = (Set.range a.base)ᶜ) [IsFinite (i ≫ b)]
    (K : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hopen : DerivedCategory.isBoundedConstructible Λ G
      ((upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategory.obj K.obj))
    (hpush : DerivedCategory.isBoundedConstructible Λ S
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) b).obj K).obj) :
    DerivedCategory.isBoundedConstructible Λ Y K.obj := by
  have hiff (T : Scheme.{u}) (L : DerivedCategoryModule Λ T) :
      DerivedCategory.isBoundedConstructible Λ T L ↔
        DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T L := by
    constructor
    · rintro ⟨hc, r, s, hrs, hv⟩
      refine ⟨⟨⟨r, ?_⟩, ⟨s, ?_⟩⟩, fun q ↦
        (Scheme.isConstructibleEtaleModuleSheaf_iff _).1 (hc q)⟩
      · exact (_root_.DerivedCategory.isGE_iff L r).2 fun q hq ↦ hv q (Or.inl hq)
      · exact (_root_.DerivedCategory.isLE_iff L s).2 fun q hq ↦ hv q (Or.inr hq)
    · rintro ⟨⟨⟨r, hr⟩, ⟨s, hs⟩⟩, hc⟩
      refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff _).2 (hc q),
        min r s, max r s, min_le_max, fun q hq ↦ ?_⟩
      rcases hq with hq | hq
      · exact (_root_.DerivedCategory.isGE_iff L r).1 hr q
          (lt_of_lt_of_le hq (min_le_left _ _))
      · exact (_root_.DerivedCategory.isLE_iff L s).1 hs q
          (lt_of_le_of_lt (le_max_right _ _) hq)
  have : HasInvertibleExponent Λ S := ⟨N, hcoeff.1, hcoeff.2.2.1, hcoeff.2.2.2⟩
  have hp := (hiff _ _).1 hpush
  have hp' : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S
      ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) b).obj K.obj) :=
    (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S).prop_of_iso
      (((lowerStar (ModuleCat.{u + 1} Λ) b).rightDerivedFunctorPlusCompatibility).app K) hp
  exact (hiff _ _).2
    (boundedConstructible_of_upperStar_of_rightDerivedLowerStar Λ (S ↘ Spec (.of k))
      b a i hcomplement K.obj K.property ((hiff _ _).1 hopen) hp')

end AlgebraicGeometry.Etale
