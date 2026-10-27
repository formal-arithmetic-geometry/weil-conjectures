/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.SfExchanges
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Paper.FiniteHorizontalShriekComposition
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport
import Sheaf.AlgebraicGeometry.ProperOpenSiteTransport

import Sheaf.Paper.ExchangeFunctoriality
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.AlgebraicGeometry.ProperCoincidenceNormalized
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.OpenBaseChangeSiteTransport
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality

/-!
# Compact-support exchange along finite horizontal arrows

Source: blueprint main-20261015, trace formula, proof (β) of
`lem-trf-weil-shriek-operator-fibres`; Stacks Tags 0F7B, 0F7J and 0F7L
(blueprint: lem-trf-finite-horizontal-shriek-mate).

The comparison below is the normalized compact-support compositor with proper horizontal
factors, written in its proper/open model. All operations use the actual intrinsic
constant-ring module categories, with ordinary uncompleted inverse-image adjunctions.

## Main definitions and statements

* `finiteHorizontalShriekMate`: its finite-horizontal square-mate identity.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Compact-support exchange is the inverse horizontal square mate of χ.
Source: blueprint main-20261015, proof (β) of `lem-trf-weil-shriek-operator-fibres`,
generalized to a finite horizontal base map
(blueprint: lem-trf-finite-horizontal-shriek-mate).

Proof (the twelve steps of the node):
1. Write c as j followed by b, with base change j',b' and horizontal q. Finiteness
   is stable under base change, so p and q are finite and proper. Finite type over
   the base field makes the corners Noetherian and the diagram qcqs.
   Uses lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-finite-proper,
   lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated
   and lem-weil-pbc-qcqs-morphism-permanence.
2. Use the proper-support-normalized étale interchange γ: j! Rp* ≅ Rq* j'!.
   On a K-injective representative its map is the proper-support identification
   followed by the image of the resolution j'!J to I (Tag 0F7B).
   Uses lem-cbc-proper-open-interchange-coherence and lem-cbc-proper-support-sheaf-composition.
3. Direct image for finite morphisms on the étale site is exact, also for constant
   modules by forgetting the action. Thus its derived maps and units are termwise.
   The same holds for open
   extension and constant-module inverse image. Uses lemma-weil-pbc-finite-direct-image-exact,
   def-weil-sheaf-of-modules-category, lem-weil-pbc-module-abelian-derived-direct-image-comparison,
   def-cbc-exchange-map and lem-cbc-extension-zero-base-change.
4. Evaluate on an étale test V. Both q_*(β) after ηq and γ after j!(ηp) pull the
   same proper-support section to V times_Z X'. This gives equation (O) on complexes.
   Uses the proper-support, extension-zero base-change and proper/open coherence nodes in 2–3.
5. For the proper square the ordinary exchange E is the inverse horizontal mate
   of the canonical direct-image composition σ. Adjunction and its triangles give
   Rg_*(E) after ηg = σ after Rb_*(ηq), equation (P).
   Uses def-kun-unbounded-exchange, def-weil-pbc-adjunction-mate,
   def-weil-pbc-adjunction-conjugate, def-weil-pbc-composite-adjunction,
   lem-weil-pbc-mate-pasting and lem-weil-pbc-ringed-topoi-derived-pushforward-composition.
6. Proper-input compact-support composition and identity-open proper coincidence
   give χ = σ after Rb_*(γ), equation (C), exactly the definition above.
   Uses def-cbc-exchange-map, lem-sf-unbounded-compact-support-proper-composition,
   lem-cbc-proper-open-interchange-coherence, lem-weil-derived-direct-image-composition
   and cor-cbc-proper-coincidence.
7. Apply (P) to j!K, then naturality of σ and (O), to obtain the required unit equation.
8. Choose a bounded constructible étale origin. The canonical direct-image comparison
   is the mate of inverse pullback comparison. The square-mate unit identity therefore
   identifies transported horizontal units with the actual pro-etale units.
   Uses lem-sf-proetale-constructible-origin,
   lem-weil-pbc-comparison-direct-image-canonical-mate and lem-pur-mate-unit-compatibility.
9. The open-base-change and finite proper/open site-transport equations identify
   the specified β and γ. Ordinary exchange transport identifies E as well, so the
   transported composite is the actual compactification-defined pro-etale Ex!.
   Uses lem-trf-open-base-change-site-transport, lem-trf-proper-open-site-transport,
   prop-weil-pbc-comparison-direct-image, lem-weil-pbc-transport-identifies-exchange
   and thm-cbc-finite-level-proetale.
10. Proper-factor composition site transport for (p,f) and (f',g), with identity-open
    normalization, identifies the transported χ with this χ. Clause (4) of
    fix-lem-exchanges gives compactification independence on the stated domain.
    Uses lem-trf-proper-composition-site-transport and prop-functor-package.
11. Transport the étale unit equation by site comparison and cancel adjacent inverse
    comparisons. Naturality in the origin isomorphism gives the equation for K.
12. The inverse square mate is εg after Lg*(χ after Rf!(ηp)). The adjunction Hom
    bijection identifies its transpose with the proved unit equation, yielding the
    equivalent inverse-mate formulation of this same equation.
-/
theorem finiteHorizontalShriekMate
    (T : TraceFormulaCoefficientConventions.{u})
    {X' X Y' Y : Scheme.{u}}
    [X'.Over (Spec (.of T.datum.k))] [X.Over (Spec (.of T.datum.k))]
    [Y'.Over (Spec (.of T.datum.k))] [Y.Over (Spec (.of T.datum.k))]
    [IsSeparated (X' ↘ Spec (.of T.datum.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of T.datum.k))]
    [QuasiCompact (X' ↘ Spec (.of T.datum.k))]
    [IsSeparated (X ↘ Spec (.of T.datum.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of T.datum.k))]
    [QuasiCompact (X ↘ Spec (.of T.datum.k))]
    [IsSeparated (Y' ↘ Spec (.of T.datum.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of T.datum.k))]
    [QuasiCompact (Y' ↘ Spec (.of T.datum.k))]
    [IsSeparated (Y ↘ Spec (.of T.datum.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of T.datum.k))]
    [QuasiCompact (Y ↘ Spec (.of T.datum.k))]
    (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X' ⟶ X) (g : Y' ⟶ Y)
    [f.IsOver (Spec (.of T.datum.k))] [f'.IsOver (Spec (.of T.datum.k))]
    [p.IsOver (Spec (.of T.datum.k))] [g.IsOver (Spec (.of T.datum.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsFinite g]
    (sq : ChosenCartesianSquare p f' f g) (c : Compactification f) :
    letI : Finite T.coefficientRing :=
      Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField T.level T.level_pos
    IsFinite p ∧
      ∀ K : (finiteHorizontalFiniteTorConstructible T.coefficients.l T.coefficientField T.level
          T.level_pos X).FullSubcategory,
        (CategoryTheory.Adjunction.unit
          ((sfIntrinsicConstantModuleAdjunction g
            T.coefficientRing).mapDerivedCategoryRightDerivedAdjunction)).app
              ((sfIntrinsicCompactSupport c T.coefficientRing).obj K.obj) ≫
          (proEtaleConstantDerivedDirectImage g T.coefficientRing).map
            ((sfExchangeShriek T.coefficients.l T.coefficientField T.level T.level_pos c
              (c.ofIsPullback (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback
                sq.hom_fst sq.hom_snd)) (pullback.fst c.g g)
              (c.isPullback_g_ofIsPullback (IsPullback.of_iso_pullback sq.toCommSq
                sq.isoPullback sq.hom_fst sq.hom_snd)).flip
              (c.isPullback_i_ofIsPullback (IsPullback.of_iso_pullback sq.toCommSq
                sq.isoPullback sq.hom_fst sq.hom_snd))).app K.obj) =
        (sfIntrinsicCompactSupport c T.coefficientRing).map
            ((CategoryTheory.Adjunction.unit
              ((sfIntrinsicConstantModuleAdjunction p
                T.coefficientRing).mapDerivedCategoryRightDerivedAdjunction)).app
                K.obj) ≫
          (finiteHorizontalShriekComposition T.coefficientRing
            (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)
            c).app ((sfIntrinsicDerivedPullback T.coefficientRing p).obj K.obj) := by
  sorry

end WeilConjectures
