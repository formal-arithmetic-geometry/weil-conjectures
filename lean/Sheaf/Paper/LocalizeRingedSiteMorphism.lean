/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.SliceSiteLocalization
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

/-!
# Localization of a morphism of ringed sites

Source: Stacks Project, sites-modules.tex, Tag 04J0, lemma-localize-morphism-ringed-sites;
sites.tex, Tag 03CF (blueprint: lem-weil-pbc-localize-ringed-site-morphism).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 800000 in
-- The signature expands the commuting squares for three kinds of sheaves.
/-- Localization commutes with ringed inverse image and module pullback and pushforward.
Source: Stacks Project, Tag 04J0, using Tag 03CF.
(blueprint: lem-weil-pbc-localize-ringed-site-morphism).

The ring morphism `aV` is the adjunct of the localized inverse-image ring morphism.
Its section equation specifies the restricted scalar action. The next equation says
that its inverse adjunct is the inverse-image comparison followed by restriction of `c`.
The last equation specifies the direct-image comparison as the identity on sections.
Mathlib's module pullback is the left adjoint of the displayed module pushforward;
lem-weil-pbc-ringed-topoi-module-adjunction identifies it with the sheafified tensor formula
of def-pur-sheaf-tensor-product, including its canonical adjunction.

Proof:
1. Apply lem-weil-pbc-slice-site-localization (03CF) to u and V. Coverings and their
   pullbacks on slices are the underlying coverings and pullbacks. This gives the
   localized continuous site morphism, finite-limit preservation and the inverse-image
   comparison. Direct image and restriction agree sectionwise, also on rings.
2. Apply that comparison to R, then restrict c. Its adjunct has at T -> V exactly
   the component of the adjunct of c at T. This constructs the localized ring map
   and makes the ringed square commute (def-pur-localized-ringed-site).
3. Localization pullback on modules is restriction: its coefficient map is the identity,
   so the tensor formula reduces by a tensor m -> a*m, with inverse m -> 1 tensor m.
   Taking right adjoints of the inverse-image square gives the commuting square of
   right adjoints. The coefficient maps agree by step 2, hence this also holds on
   modules. Apply lem-weil-pbc-ringed-topoi-module-adjunction twice to identify
   Hom((f_V)^* j_V^* M,H) with Hom(j_U^* f^* M,H), naturally in both variables.
   Yoneda gives the module pullback comparison. Finally both module direct images
   have sections G(u(T)), on which r acts through the same adjunct component a_T.
   The identity is therefore linear, natural in T and G, and invertible. -/
theorem localize_ringed_site_morphism
    {D C : Type u} [SmallCategory D] [SmallCategory C]
    (K : Precoverage D) (J : Precoverage C)
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (u : D ⥤ C)
    (hcover : ∀ (X : D) (Q : Presieve X), Q ∈ K X → Q.map u ∈ J (u.obj X))
    (hpullback : ∀ (X Y Z : D) (Q : Presieve X), Q ∈ K X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), Q f → PreservesLimit (cospan f g) u)
    [u.IsContinuous K.toGrothendieck J.toGrothendieck]
    [PreservesFiniteLimits (u.sheafPullback (Type u) K.toGrothendieck J.toGrothendieck)]
    (R : Sheaf K.toGrothendieck CommRingCat.{u})
    (S : Sheaf J.toGrothendieck CommRingCat.{u})
    (c : (u.sheafPullback CommRingCat.{u} K.toGrothendieck J.toGrothendieck).obj R ⟶ S) (V : D) :
    (∀ (X : Over V) (Q : Presieve X), Presieve.overEquiv X Q ∈ K X.left →
      Presieve.overEquiv ((Over.post (X := V) u).obj X)
        (Q.map (Over.post (X := V) u)) ∈ J (u.obj X.left)) ∧
    (∀ (X Y Z : Over V) (Q : Presieve X), Presieve.overEquiv X Q ∈ K X.left →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), Q f →
        PreservesLimit (cospan f g) (Over.post (X := V) u)) ∧
    ∃ hcont : (Over.post (X := V) u).IsContinuous
        (K.toGrothendieck.over V) (J.toGrothendieck.over (u.obj V)),
      ∃ hlim : PreservesFiniteLimits
        ((Over.post (X := V) u).sheafPullback (Type u)
          (K.toGrothendieck.over V) (J.toGrothendieck.over (u.obj V))),
        ∃ e : K.toGrothendieck.overPullback (Type u) V ⋙
            (Over.post (X := V) u).sheafPullback (Type u) (K.toGrothendieck.over V)
              (J.toGrothendieck.over (u.obj V)) ≅
            u.sheafPullback (Type u) K.toGrothendieck J.toGrothendieck ⋙
              J.toGrothendieck.overPullback (Type u) (u.obj V),
        ∃ eR : K.toGrothendieck.overPullback CommRingCat.{u} V ⋙ (Over.post (X := V)
                u).sheafPullback CommRingCat.{u} (K.toGrothendieck.over V) (J.toGrothendieck.over
                (u.obj V)) ≅
            u.sheafPullback CommRingCat.{u} K.toGrothendieck J.toGrothendieck ⋙
                J.toGrothendieck.overPullback CommRingCat.{u} (u.obj V),
          ∃ aV : R.over V ⟶ ((Over.post (X := V) u).sheafPushforwardContinuous CommRingCat.{u}
                (K.toGrothendieck.over V) (J.toGrothendieck.over (u.obj V))).obj (S.over (u.obj V)),
            (∀ (T : Over V), aV.hom.app (Opposite.op T) =
              ((u.sheafAdjunctionContinuous CommRingCat.{u} K.toGrothendieck
                J.toGrothendieck).homEquiv R S c).hom.app (Opposite.op T.left)) ∧
            ((Over.post (X := V) u).sheafAdjunctionContinuous CommRingCat.{u} (K.toGrothendieck.over
                V) (J.toGrothendieck.over (u.obj V))).homEquiv (R.over V) (S.over (u.obj V))
                (eR.hom.app R ≫ (J.toGrothendieck.overPullback CommRingCat.{u} (u.obj V)).map c) =
                aV ∧
            Nonempty (overFunctor ((sheafCompose K.toGrothendieck (forget₂ CommRingCat.{u}
                RingCat.{u})).obj R) V ⋙ pullback (F := (Over.post (X := V) u)) (J :=
                (K.toGrothendieck.over V)) (K := (J.toGrothendieck.over (u.obj V))) (S :=
                ((sheafCompose K.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over
                V) (R := ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj
                S).over (u.obj V)) ((sheafCompose (K.toGrothendieck.over V) (forget₂ CommRingCat.{u}
                RingCat.{u})).map aV) ≅
              pullback (F := u) (J := K.toGrothendieck) (K := J.toGrothendieck) (S := ((sheafCompose
                K.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (R := ((sheafCompose
                J.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ((sheafCompose
                K.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).map
                ((u.sheafAdjunctionContinuous CommRingCat.{u} K.toGrothendieck
                J.toGrothendieck).homEquiv R S c)) ⋙ overFunctor ((sheafCompose J.toGrothendieck
                (forget₂ CommRingCat.{u} RingCat.{u})).obj S) (u.obj V)) ∧
            ∃ eM : pushforward (F := u) (J := K.toGrothendieck) (K := J.toGrothendieck) (S :=
                ((sheafCompose K.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (R :=
                ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
                ((sheafCompose K.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).map
                ((u.sheafAdjunctionContinuous CommRingCat.{u} K.toGrothendieck
                J.toGrothendieck).homEquiv R S c)) ⋙ overFunctor ((sheafCompose K.toGrothendieck
                (forget₂ CommRingCat.{u} RingCat.{u})).obj R) V ≅
                overFunctor ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{u}
                RingCat.{u})).obj S) (u.obj V) ⋙ pushforward (F := (Over.post (X := V) u)) (J :=
                (K.toGrothendieck.over V)) (K := (J.toGrothendieck.over (u.obj V))) (S :=
                ((sheafCompose K.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over
                V) (R := ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj
                S).over (u.obj V)) ((sheafCompose (K.toGrothendieck.over V) (forget₂ CommRingCat.{u}
                RingCat.{u})).map aV),
              ∀ (G : SheafOfModules.{u} ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{u}
                RingCat.{u})).obj S)) (T : Over V)
                (x : G.val.obj (Opposite.op (u.obj T.left))),
                ((eM.hom.app G).val.app (Opposite.op T)) x = x := by sorry

end SheafOfModules
