/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeArrowLocalization
public import Sheaf.AlgebraicGeometry.DerivedLocalizationComparisonData
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Sheaf.Paper.RingedDerivedSliceLocalization
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Derived base-change arrow under étale localization

Source: Stacks Project, Étale Cohomology, Tag 0EZR, compatibility of derived
counit-transpose maps (blueprint: lem-sbc-derived-base-change-arrow-localization).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Restrict the cohomology of a derived arrow, transported by the canonical exact-functor
cohomology comparisons. For étale `a`, inverse image is restriction.
Source: Stacks Tag 010N; Étale Cohomology 0EZR
(blueprint: lem-sbc-derived-base-change-arrow-localization). -/
noncomputable def restrictedDerivedCohomologyArrow
    {X U : Scheme.{u}} (a : U ⟶ X) (q : ℤ)
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (φ : K ⟶ L) :
    (DerivedCategory.homologyFunctor
      (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        (D((a)^*[AddCommGrpCat.{u + 1}]).obj K) ⟶
      (DerivedCategory.homologyFunctor
        (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          (D((a)^*[AddCommGrpCat.{u + 1}]).obj L) :=
  (((a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryHomologyFunctorIso q).inv.app K ≫
    ((a)^*[AddCommGrpCat.{u + 1}]).map
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).map φ) ≫
    (((a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryHomologyFunctorIso q).hom.app L

open BaseChangeLocalization in
/-- The canonical derived localization comparisons are invertible and intertwine
base-change arrows, naturally in every unbounded complex and in every integer degree.
Source: Stacks Project, Étale Cohomology, Tag 0EZR; Cohomology on Sites, Tags 0D6G and
07A7 (blueprint: lem-sbc-derived-base-change-arrow-localization).

Proof:
1. The pullback projections identify `Y_U` with `U ×_B T_B`, and the pullbacks of
   the étale maps are étale (lem-weil-pbc-etale-base-change-finite-limits).
   Identify small étale sites with slices (lem-weil-pbc-etale-site-localization-open)
   and étale inverse image with restriction (lem-weil-pbc-etale-inverse-image-restriction).
   The canonical derived slice comparisons for g and h are invertible on all of D,
   with compatible units and counits (lem-weil-pbc-ringed-derived-slice-localization).
   Thus the explicitly constructed C_L^D and C_R^D are invertible.
2. The inverse-image composition comparisons are normalized by their adjunction units
   (lem-weil-pbc-inverse-image-composition). Their coherence follows from the
   direct-image associativity (lem-weil-pbc-direct-image-composition-coherence) and
   adjoint-composition coherence (lem-trf-adjoint-composition-coherence). Apply the
   resulting square equation termwise and descend along Q, using exact inverse image,
   exact restriction, cohomology comparison and the localization universal property.
3. Use the slice counit equation for g. The square equation in step 2 identifies the
   restriction of the global transpose `e^* ε_g ∘ θ` with the local transpose composed
   with `h_U^* C_L^D` and the comparison for restriction of `h^*`.
4. Use the slice counit equation for h. The transpose of `C_R^D ∘ r_U(v)` is the
   restriction of the transpose of v, followed by the inverse-image comparisons.
   Set v equal to the counit-transpose base-change arrow of sbc-def-base-change-map.
5. Both resulting transposes equal the local transpose after `h_U^* C_L^D`.
   The adjunction hom-bijection (def-weil-pbc-adjunction-mate) gives the arrow equality.
   All constructions are natural in K, giving the displayed naturality equation.
6. Apply H^q for every integer q. The natural exact-functor cohomology comparison
   (lem-weil-pbc-exact-functor-complex-cohomology), descended along Q, identifies
   H^q of restriction with restriction of H^q, including on arrows. This gives the
   last equation. No boundedness, positivity or qcqs assumption enters.
-/
theorem derivedBaseChangeArrow_localization
    {X Y S T U B : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g)
    {a : U ⟶ X} [Etale a] {b : B ⟶ S} [Etale b]
    {fU : U ⟶ B} (fac : a ≫ f = fU ≫ b) :
    IsIso (derivedLeftComparison (g := g) a b fU fac) ∧
      IsIso (derivedRightComparison sq a b fU fac) ∧
      (∀ K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}),
        D((a)^*[AddCommGrpCat.{u + 1}]).map (abelianDerivedBaseChangeArrow sq K) ≫
            (derivedRightComparison sq a b fU fac).app K =
          (derivedLeftComparison (g := g) a b fU fac).app K ≫
            abelianDerivedBaseChangeArrow (localSquare sq a b fU fac)
              (D((pullback.snd b g)^*[AddCommGrpCat.{u + 1}]).obj K)) ∧
      (∀ (K L : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (φ : K ⟶ L),
        (R((g)_*[AddCommGrpCat.{u + 1}]) ⋙ D((f)^*[AddCommGrpCat.{u + 1}]) ⋙
          D((a)^*[AddCommGrpCat.{u + 1}])).map φ ≫
            D((a)^*[AddCommGrpCat.{u + 1}]).map (abelianDerivedBaseChangeArrow sq L) ≫
              (derivedRightComparison sq a b fU fac).app L =
          (D((a)^*[AddCommGrpCat.{u + 1}]).map (abelianDerivedBaseChangeArrow sq K) ≫
            (derivedRightComparison sq a b fU fac).app K) ≫
              (D((pullback.snd b g)^*[AddCommGrpCat.{u + 1}]) ⋙
                D((localArrow sq a b fU fac)^*[AddCommGrpCat.{u + 1}]) ⋙
                R((pullback.fst a h)_*[AddCommGrpCat.{u + 1}])).map φ) ∧
      ∀ (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) (q : ℤ),
        restrictedDerivedCohomologyArrow a q (abelianDerivedBaseChangeArrow sq K) ≫
          (DerivedCategory.homologyFunctor
            (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) q).map
              ((derivedRightComparison sq a b fU fac).app K) =
          (DerivedCategory.homologyFunctor
            (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) q).map
              ((derivedLeftComparison (g := g) a b fU fac).app K) ≫
            (DerivedCategory.homologyFunctor
              (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) q).map
                (abelianDerivedBaseChangeArrow (localSquare sq a b fU fac)
                  (D((pullback.snd b g)^*[AddCommGrpCat.{u + 1}]).obj K)) := by
  sorry

end AlgebraicGeometry.Etale
