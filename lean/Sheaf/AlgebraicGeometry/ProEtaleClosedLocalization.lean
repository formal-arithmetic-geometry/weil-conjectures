/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed-site operations under weakly etale localization

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-open-closed-triangle`,
node `lem-exc-closed-localization`, order 1846 (blueprint: lem-exc-closed-localization).

We use constant-coefficient module sheaves, as in the source's site convention.
The first comparison is normalized on every section by the canonical map of fibre
products. The two final equations express compatibility with the closed adjunction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Restriction commutes with closed direct image and closed inverse image, preserving
the unit and counit. Here `pullback i W.hom` is `Z_W`, with projections `v_Z` and `i_W`.
The section formula fixes the direct-image identification; together with the unit and
counit formulas it fixes the inverse-image identification as its adjoint comparison.

Source: Weil conjectures blueprint, smooth purity, order 1846
(blueprint: lem-exc-closed-localization).

Proof plan:
1. Use the slice identification of `lem-weil-pbc-proetale-restriction-injectives`.
   On `T` over `W`, the two direct images evaluate `G` on `T ×_X Z` and
   `T ×_W (Z ×_X W)`. The fibre-product comparison is an isomorphism and is natural
   in `T` and `G`. Its restriction map is linear over the same constant coefficient ring.
2. Use the comma-colimit and sheafification construction of
   `def-weil-proetale-inverse-image`. Replace a global index `(V, phi)` by
   `V ×_X W`, lifting `phi` with the given map to `W`. A local index gives a global
   one by forgetting its `W`-structure. Projection and graph indexing arrows identify
   both composites with the original representative. These maps commute with
   restrictions, sheafification, and scalar multiplication, yielding `beta`.
3. The unit sends a section to the identity-indexed class. Base change sends this
   representative to the local unit representative. The counit sends `(phi, s)` to
   `phi^* s`; the lifted `phi` followed by projection is the original `phi`, so the
   same restriction results. These are the canonical adjunction maps of
   `def-weil-pbc-proetale-operations`, giving the two displayed equations. -/
theorem proEtale_closed_localization {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (W : X.ProEt) (Λ : Type (u + 1)) [CommRing Λ] :
    ∃ alpha : lowerStar (ModuleCat.{u + 1} Λ) i ⋙
          localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop ≅
        localizationRestriction (ModuleCat.{u + 1} Λ)
            (pullback.fst i W.hom) inferInstance ⋙
          lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom),
      ∃ beta : upperStar (ModuleCat.{u + 1} Λ) i ⋙
            localizationRestriction (ModuleCat.{u + 1} Λ)
              (pullback.fst i W.hom) inferInstance ≅
          localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop ⋙
            upperStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom),
        (∀ (G : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)) (T : W.left.ProEt),
          (alpha.hom.app G).hom.app (op T) =
            G.obj.map (((MorphismProperty.Over.pullbackMapComparison W.prop
              (inferInstance : WeaklyEtale (pullback.fst i W.hom))
              (IsPullback.of_hasPullback i W.hom).flip.toCommSq).app T).op)) ∧
        (∀ F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ),
          (localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop).map
              ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F) ≫
            alpha.hom.app ((upperStar (ModuleCat.{u + 1} Λ) i).obj F) ≫
            (lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).map
              (beta.hom.app F) =
            (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
              (pullback.snd i W.hom)).unit.app
                ((localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop).obj F)) ∧
        (∀ G : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ),
          (upperStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).map
              (alpha.inv.app G) ≫
            beta.inv.app ((lowerStar (ModuleCat.{u + 1} Λ) i).obj G) ≫
            (localizationRestriction (ModuleCat.{u + 1} Λ)
                (pullback.fst i W.hom) inferInstance).map
              ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit.app G) =
            (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
              (pullback.snd i W.hom)).counit.app
                ((localizationRestriction (ModuleCat.{u + 1} Λ)
                  (pullback.fst i W.hom) inferInstance).obj G)) := by
  sorry

end AlgebraicGeometry.ProEtale
