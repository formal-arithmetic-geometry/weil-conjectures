/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare

/-!
# Underived vertical pasting for open base change

Source: Stacks Project, Etale Cohomology, Tag 03S6 (blueprint:
lem-cbc-derived-extension-zero-base-change-vertical-pasting).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option autoImplicit false

/-- The two successive underived extension-by-zero base-change isomorphisms paste to the
base-change isomorphism for the composite square: after the canonical composition
identifications `c_{g,h} : h^* g^* ≅ (h ≫ g)^*` and `c_{gU,hU} : hU^* gU^* ≅ (hU ≫ gU)^*`
(`upperStarComp`), `b_{h,gU^* F} ∘ h^*(b_{g,F})` equals `b_{g∘h,F}`, where `b` is the inverse of
`openImmersionLowerShriekBaseChangeMap`. Source: Stacks Project, Etale Cohomology, Tag 03S6
(lemma-shriek-base-change), composed adjunctions; categories Tags 0B65 and 0DV0
(blueprint: lem-cbc-derived-extension-zero-base-change-vertical-pasting).

Proof (the node's steps). All functors act on sheaves of `Λ`-modules. Put `G = g^*`, `H = h^*`,
`A = gU^*`, `B = hU^*`, `J = j^*`, `J' = j'^*`, `J'' = j''^*`.

1. The composite square is cartesian (`IsPullback.paste_horiz`). With `c_{u,v}` the
   module-linear composition comparison, the square comparisons are
   `s_g = c_{g,j'}⁻¹ ∘ c_{j,gU} : A J ⟶ J' G`, `s_h = c_{h,j''}⁻¹ ∘ c_{j',hU} : B J' ⟶ J'' H`
   and the identical `s_{gh}` for the composite square; these are the comparisons in the
   adjunction characterization of `b`
   ([def-cbc-open-immersion-square], [lem-weil-pbc-inverse-image-composition-module-linear],
   [lem-cbc-derived-extension-zero-base-change-underived-compatibility]; Stacks 03D8).
2. `s_h G ∘ B(s_g) = (J'' c_{g,h})⁻¹ ∘ s_{gh} ∘ (c_{gU,hU} J) : B A J ⟶ J'' H G` (*), by
   associativity of `c` (clause (1) of [lem-weil-pbc-derived-inverse-image-composition]) for
   the triples `(g, j', hU)`, `(j, gU, hU)` and `(g, h, j'')`, using `g j' = j gU` and
   `j' hU = h j''`; the module comparisons have these abelian comparisons as underlying maps
   ([lem-weil-pbc-inverse-image-composition-module-linear]) and the forgetful functor is
   faithful.
3. Put `α_{g,F} = b_{g,F}⁻¹` and `α_{h,AF} = b_{h,AF}⁻¹`. With the units `η` of the
   extension-by-zero adjunctions, `J'(α_{g,F}) ∘ η_{j',AF} = s_{g,j_!F} ∘ A(η_{j,F})` and
   `J''(α_{h,AF}) ∘ η_{j'',BAF} = s_{h,j'_!AF} ∘ B(η_{j',AF})`; likewise for `α_{gh,F}`. Each
   `α` is invertible ([lem-cbc-derived-extension-zero-base-change-underived-compatibility],
   [lem-weil-pbc-extension-by-zero-adjunction], [lem-cbc-extension-zero-base-change]).
4. For `P = H(α_{g,F}) ∘ α_{h,AF}`, the transpose `J''(P) ∘ η_{j'',BAF}` equals
   `s_{h,Gj_!F} ∘ B(s_{g,j_!F}) ∘ BA(η_{j,F})` (step 3, naturality of `s_h`, step 3); by (*)
   and naturality of `c_{gU,hU}` this is the transpose of `α_{gh,F}` transported along
   `c_{g,h}` and `c_{gU,hU}`; injectivity of the adjunction bijection identifies `P` with the
   transported `α_{gh,F}` ([lem-weil-pbc-extension-by-zero-adjunction]; Stacks 0DV0).
5. Inverting, `P⁻¹ = b_{h,AF} ∘ H(b_{g,F})` is the transported `b_{g∘h,F}`, which is the
   claimed equality. -/
theorem derivedExtensionZeroBaseChangeVerticalPasting
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ∀ {U' U X' X U'' X'' : Scheme.{u}}
      {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}
      {hU : U'' ⟶ U'} {j'' : U'' ⟶ X''} {h : X'' ⟶ X'}
      (sq₁data : OpenImmersionSquare gU j' j g)
      (sq₂data : OpenImmersionSquare hU j'' j' h),
      letI : IsOpenImmersion j := sq₁data.isOpenImmersion
      letI : IsOpenImmersion j' := sq₁data.isOpenImmersion'
      letI : IsOpenImmersion j'' := sq₂data.isOpenImmersion'
      let sq₁ : IsPullback gU j' j g :=
        IsPullback.of_iso_pullback
          sq₁data.toChosenCartesianSquare.toCommSq
          sq₁data.toChosenCartesianSquare.isoPullback
          sq₁data.toChosenCartesianSquare.hom_fst
          sq₁data.toChosenCartesianSquare.hom_snd
      let sq₂ : IsPullback hU j'' j' h :=
        IsPullback.of_iso_pullback
          sq₂data.toChosenCartesianSquare.toCommSq
          sq₂data.toChosenCartesianSquare.isoPullback
          sq₂data.toChosenCartesianSquare.hom_fst
          sq₂data.toChosenCartesianSquare.hom_snd
      ∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        ((h)^*[ModuleCat.{u + 1} Λ]).map
              ((@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
                (ModuleCat.{u + 1} Λ) sq₁)).inv.app F) ≫
            (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
              (ModuleCat.{u + 1} Λ) sq₂)).inv.app
              (((gU)^*[ModuleCat.{u + 1} Λ]).obj F) =
          (upperStarComp (ModuleCat.{u + 1} Λ) h g (h ≫ g)).inv.app
              (((j)_!open[ModuleCat.{u + 1} Λ]).obj F) ≫
            (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
              (ModuleCat.{u + 1} Λ) (sq₂.paste_horiz sq₁))).inv.app F ≫
            ((j'')_!open[ModuleCat.{u + 1} Λ]).map
              ((upperStarComp (ModuleCat.{u + 1} Λ) hU gU (hU ≫ gU)).hom.app F)
  := by
    sorry

end AlgebraicGeometry.Etale
