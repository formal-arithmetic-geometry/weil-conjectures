/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Inverse image of a free etale module sheaf

Source: Stacks Project, Etale Cohomology, Lemma 03S6
(blueprint: lem-weil-pbc-inverse-image-free-etale-module).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
/-- The free module sheaf on an etale object commutes with inverse image.
Source: Stacks Project, Etale Cohomology, Lemma 03S6
(blueprint: lem-weil-pbc-inverse-image-free-etale-module).

The ring on T is written explicitly; the lambda-bound ring on Y is its constant sheaf.
gamma is the canonical
map into the direct image, obtained by sheafifying the constant sections. L and adj
are the inverse image and its adjunction of prop-weil-pbc-inverse-image-modules-exact.
The free Yoneda presheaf uses ULift only to put the indexing set in the ring universe.
The section bijection is sheafificationHomEquiv, followed by evaluation at freeMk(id).

Proof:
1. Sheafification and the free Yoneda bijection give epsilon, natural in the module
( def-weil-presheaf-modules-sheafification, lem-weil-pbc-free-yoneda-presheaf-module).
2. Direct image evaluates at the base-changed object and has the same component maps
(def-weil-pbc-direct-image, lem-weil-pbc-etale-base-change-continuous).
3. Compose epsilon on the two sites with the hom bijection of adj to obtain a natural
bijection of Hom functors (lem-weil-pbc-adjunction-of-natural-bijection).
4. Co-Yoneda yields the isomorphism theta
(lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection).
5. Naturality of the adjunction unit and epsilon gives the displayed compatibility.
6. Set H equal to the free sheaf and take its identity generating section: injectivity
of epsilon identifies the inverses of any two compatible isomorphisms. -/
theorem inverseImageFreeEtaleModule (T Y : Scheme.{u}) (h : Y ⟶ T)
    (Λ : Type (u + 1)) [CommRing Λ]
    [EssentiallySmall.{u + 1} T.Etale] [EssentiallySmall.{u + 1} Y.Etale]
    (W : T.Etale) :
    (fun (RY : Sheaf Y.smallEtaleTopology RingCat.{u + 1})
      (etaY : ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ)) ⟶ RY.obj) =>
    (fun (gamma : ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)) ⟶
          ((MorphismProperty.Over.pullback @Etale ⊤ h).sheafPushforwardContinuous
         RingCat.{u + 1} (T.smallGrothendieckTopology @Etale)
        (Y.smallGrothendieckTopology @Etale)).obj RY) =>
    ∀ (L : SheafOfModules.{u + 1} ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
          (RingCat.of Λ)) ⥤ SheafOfModules.{u + 1} RY)
      (adj : L ⊣ SheafOfModules.pushforward
        (J := T.smallGrothendieckTopology @Etale)
        (K := Y.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ h) gamma),
    ∃! θ : L.obj ((PresheafOfModules.sheafification.{u + 1} (𝟙 ((constantSheaf
          T.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)).obj)).obj
          ((PresheafOfModules.free ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
          (RingCat.of Λ)).obj).obj (uliftYoneda.{u + 1}.obj W))) ≅
          ((PresheafOfModules.sheafification.{u + 1} (𝟙 RY.obj)).obj
          ((PresheafOfModules.free RY.obj).obj
            (uliftYoneda.{u + 1}.obj
              ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W)))),
      ∀ (H : SheafOfModules.{u + 1} ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
          (RingCat.of Λ))) (s : H.val.obj (op W)) (φ : ((PresheafOfModules.sheafification.{u + 1}
          (𝟙 ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)).obj)).obj
          ((PresheafOfModules.free ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
          (RingCat.of Λ)).obj).obj (uliftYoneda.{u + 1}.obj W))) ⟶ H),
        (PresheafOfModules.sheafificationHomEquiv.{u + 1} (𝟙 ((constantSheaf T.smallEtaleTopology
          RingCat.{u + 1}).obj (RingCat.of Λ)).obj) φ).app (op W)
          (ModuleCat.freeMk (ULift.up (𝟙 W))) = s →
        (PresheafOfModules.sheafificationHomEquiv.{u + 1} (𝟙 RY.obj)
          (θ.inv ≫ L.map φ)).app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W))
          (ModuleCat.freeMk
            (ULift.up (𝟙 ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W)))) =
          (adj.unit.app H).val.app (op W) s)
      (((sheafificationAdjunction T.smallEtaleTopology RingCat.{u + 1}).homEquiv
        ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of Λ))
        (((MorphismProperty.Over.pullback @Etale ⊤ h).sheafPushforwardContinuous
          RingCat.{u + 1} (T.smallGrothendieckTopology @Etale)
          (Y.smallGrothendieckTopology @Etale)).obj RY)).symm
        (Functor.whiskerLeft (MorphismProperty.Over.pullback @Etale ⊤ h).op etaY)))
      ((constantSheaf Y.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ))
      (toSheafify Y.smallEtaleTopology
        ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ))) := by
  sorry

end AlgebraicGeometry
