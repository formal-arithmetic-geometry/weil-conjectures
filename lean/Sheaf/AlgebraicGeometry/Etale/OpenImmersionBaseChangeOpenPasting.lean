/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.AlgebraicGeometry.Etale.OpenInverseImageRestrictionComposition
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Open-immersion pasting for extension-by-zero base change

Source: Stacks Project, Etale Cohomology, Tag 03S6 (lemma-shriek-base-change), and
blueprint main-20261015, cor-cbc-derived-extension-zero-base-change.proof.md,
final pasting clause (blueprint: lem-cbc-derived-extension-zero-base-change-open-pasting).

The upstream base-change transformation and composition comparison both have the
opposite orientation to the node's maps, so the statement uses their inverses.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Canonical underived extension-by-zero base change commutes with composing open
immersions. Source: Stacks Tag 03S6 and the blueprint's open-immersion pasting clause
(blueprint: lem-cbc-derived-extension-zero-base-change-open-pasting).

Proof plan, following the six steps of the node:
1. Use lem-weil-pbc-extension-by-zero-adjunction to write the extension/restriction
adjunctions. The square inverse-image identifications satisfy the pasting equation by
clause (1) of lem-weil-pbc-derived-inverse-image-composition; their module-linear lifts
are lem-weil-pbc-inverse-image-composition-module-linear. This uses only the two squares,
not any open-immersion hypothesis on g.
2. Let t be the inverse of b. The unit equation in lem-cbc-extension-zero-base-change
identifies the transpose of t. Substituting it in def-weil-pbc-adjunction-mate, naturality
at the counit and the triangle identity identify the mate of t with the square's
inverse-image comparison.
3. Form the composite adjunctions of def-weil-pbc-composite-adjunction. The unit equation
and uniqueness of lem-weil-pbc-conjugate-iso-unit-equation identify the composition
comparison c of lem-cbc-extension-zero-composition. Its restriction-model description
agrees with the inverse-image description by
lem-cbc-open-inverse-image-restriction-composition. Thus the conjugate of c is the
inverse inverse-image composition comparison, by def-weil-pbc-adjunction-conjugate;
the same holds for the primed pair.
4. Apply clause (2) of lem-weil-pbc-mate-pasting to t_k and t_j. The mate of their pasted
transformation is the pasted inverse-image comparison.
5. Use clauses (3a),(3b) of that lemma to conjugate the pasted transformation by c and
c'. Step 1 identifies its mate with the composite square's inverse-image comparison.
Injectivity of the mate bijection identifies it with t for the composite open immersion.
6. Invert the equation, using invertibility from lem-cbc-extension-zero-base-change and
lem-cbc-extension-zero-composition, and precompose with g inverse image of c. Functorial
inverse cancellation gives exactly the displayed equation. -/
theorem openImmersionLowerShriekBaseChange_open_pasting
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V' V U' U X' X : Scheme.{u}}
    {gV : V' ⟶ V} {gU : U' ⟶ U} {g : X' ⟶ X}
    {k' : V' ⟶ U'} {k : V ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X}
    (sqk : OpenImmersionSquare gV k' k gU) (sqj : OpenImmersionSquare gU j' j g)
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (@asIso _ _ _ _
      (@openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) _ _ _
        U' U X' X gU j' j g sqj.isOpenImmersion sqj.isOpenImmersion' sqj.toCommSq)
      (@isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) _ _ _ _
        U' U X' X gU j' j g sqj.isOpenImmersion sqj.isOpenImmersion'
        (IsPullback.of_iso_pullback sqj.toCommSq sqj.isoPullback
          sqj.hom_fst sqj.hom_snd))).inv.app
      ((@openImmersionLowerShriek (ModuleCat.{u + 1} Λ) _ _ _ V U k
        sqk.isOpenImmersion).obj F) ≫
    (@openImmersionLowerShriek (ModuleCat.{u + 1} Λ) _ _ _ U' X' j'
      sqj.isOpenImmersion').map
      ((@asIso _ _ _ _
        (@openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) _ _ _
          V' V U' U gV k' k gU sqk.isOpenImmersion sqk.isOpenImmersion' sqk.toCommSq)
        (@isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) _ _ _ _
          V' V U' U gV k' k gU sqk.isOpenImmersion sqk.isOpenImmersion'
          (IsPullback.of_iso_pullback sqk.toCommSq sqk.isoPullback
            sqk.hom_fst sqk.hom_snd))).inv.app F) ≫
    (@openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) _ _ _ V' U' X' k' j'
      sqk.isOpenImmersion' sqj.isOpenImmersion').inv.app
      ((upperStar (ModuleCat.{u + 1} Λ) gV).obj F) =
    (upperStar (ModuleCat.{u + 1} Λ) g).map
      ((@openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) _ _ _ V U X k j
        sqk.isOpenImmersion sqj.isOpenImmersion).inv.app F) ≫
    (@asIso _ _ _ _
      (@openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) _ _ _
        V' V X' X gV (k' ≫ j') (k ≫ j) g
        (@IsOpenImmersion.comp V U X k j sqk.isOpenImmersion sqj.isOpenImmersion)
        (@IsOpenImmersion.comp V' U' X' k' j' sqk.isOpenImmersion' sqj.isOpenImmersion')
        ((IsPullback.of_iso_pullback sqk.toCommSq sqk.isoPullback
          sqk.hom_fst sqk.hom_snd).paste_vert
          (IsPullback.of_iso_pullback sqj.toCommSq sqj.isoPullback
            sqj.hom_fst sqj.hom_snd)).toCommSq)
      (@isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) _ _ _ _
        V' V X' X gV (k' ≫ j') (k ≫ j) g
        (@IsOpenImmersion.comp V U X k j sqk.isOpenImmersion sqj.isOpenImmersion)
        (@IsOpenImmersion.comp V' U' X' k' j' sqk.isOpenImmersion' sqj.isOpenImmersion')
        ((IsPullback.of_iso_pullback sqk.toCommSq sqk.isoPullback
          sqk.hom_fst sqk.hom_snd).paste_vert
          (IsPullback.of_iso_pullback sqj.toCommSq sqj.isoPullback
            sqj.hom_fst sqj.hom_snd)))).inv.app F := by
  sorry

end AlgebraicGeometry.Etale
