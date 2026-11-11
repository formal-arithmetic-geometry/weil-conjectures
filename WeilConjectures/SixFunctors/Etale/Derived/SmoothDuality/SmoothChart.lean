/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalizationUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineSpaceTwistAdjunction

/-!
# The exceptional inverse image on a chart of a smooth morphism

Let `f : X ⟶ S` admit a compactification and let `u : U ⟶ X` be a quasi-compact open immersion
with `u ≫ f = e ≫ p_d`, where `e : U ⟶ 𝔸^d_S` is separated, étale and quasi-compact and
`p_d : 𝔸^d_S ⟶ S` is the projection: a *chart* of `f` in the sense of blueprint
`proposition-exceptional-inverse-image-smooth-morphism` (every smooth morphism is covered by such
charts). For a normalized Tate twist, the exceptional inverse image is computed on the chart:

* `(Rf^! N)|_U ≅ Le^* Lp_d^* N(d)[2d]`, naturally in `N`
  (`nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_chart`,
  blueprint `proposition-exceptional-inverse-image-smooth-morphism--1`): étale localization of
  `Rf^!` along `u` and along `e` (blueprint `lem-amb-etale-adjoint-locality`), and
  `Rp_d^! ≅ Lp_d^*(d)[2d]` by uniqueness of right adjoints
  (`AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace`);
* under this identification, the counit of `R(e ≫ p_d)_! ⊣ R(e ≫ p_d)^!` is the counit of the
  extension by zero along `e` (the sum over the fibres of `e`) followed by the counit of
  `Rp_{d!} ⊣ Lp_d^*(d)[2d]`
  (`AlgebraicGeometry.Etale.existsUnique_iso_rightDerivedUpperShriek_of_chart`, blueprint
  `proposition-exceptional-inverse-image-smooth-morphism--2`);
* `ω_f|_U ≅ Λ_U(d)[2d]`
  (`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_dualizingComplex_of_chart`,
  blueprint `proposition-exceptional-inverse-image-smooth-morphism--3`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
  [HasTateTwist.IsNormalized Λ] {U X S : Scheme.{u}} [HasInvertibleExponent Λ S] (d : ℕ)

/-- Blueprint `proposition-exceptional-inverse-image-smooth-morphism--1`: *the exceptional
inverse image on a chart*. Let `f : X ⟶ S` admit a compactification, `u : U ⟶ X` a quasi-compact
open immersion and `e : U ⟶ 𝔸^d_S` a separated, quasi-compact étale morphism with
`u ≫ f = e ≫ p_d` for the projection `p_d : 𝔸^d_S ⟶ S`. Then, naturally in `N`,

`(Rf^! N)|_U ≅ Le^* Lp_d^* N(d)[2d]`. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_chart
    (u : U ⟶ X) [IsOpenImmersion u] [QuasiCompact u] (f : X ⟶ S) [HasCompactification f]
    (e : U ⟶ 𝔸(ULift.{u} (Fin d); S)) [_root_.AlgebraicGeometry.Etale e] [IsSeparated e]
    [QuasiCompact e] (h : U ⟶ S) (hu : u ≫ f = h) (he : e ≫ (𝔸(ULift.{u} (Fin d); S) ↘ S) = h)
    [HasCompactification h] :
    Nonempty (R(f)^![Λ] ⋙ L((u)^*[ModuleCat.{u + 1} Λ]) ≅
      (L(((𝔸(ULift.{u} (Fin d); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ 𝔸(ULift.{u} (Fin d); S) d) ⋙ L((e)^*[ModuleCat.{u + 1} Λ])) := by
  obtain ⟨eu⟩ := nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale Λ u f h hu
  obtain ⟨ee⟩ := nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale Λ e
    (𝔸(ULift.{u} (Fin d); S) ↘ S) h he
  obtain ⟨adj⟩ := nonempty_rightDerivedLowerShriek_adjunction_affineSpace Λ d S
  exact ⟨eu ≪≫ ee.symm ≪≫ Functor.isoWhiskerRight
    ((rightDerivedUpperShriekAdjunction Λ _).rightAdjointUniq adj) _⟩

omit [HasTateTwist.IsNormalized Λ] [HasInvertibleExponent Λ S] in
/-- Blueprint `proposition-exceptional-inverse-image-smooth-morphism--2`: *the counit on a
chart*. Let `e : U ⟶ 𝔸^d_S` be a separated étale morphism of finite type between Noetherian
schemes, so that `h = e ≫ p_d` is the restriction of `f` to the chart `U`, and let
`adj : Rp_{d!} ⊣ Lp_d^*(d)[2d]` be the adjunction of
`AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace` (computed with
the chosen compactifications). There is a unique identification
`φ : e^* Lp_d^*(-)(d)[2d] ≅ Rh^!` under which the counit of `Rh_! ⊣ Rh^!` is the inverse
composition comparison `Rh_! ≅ Rp_{d!} ∘ e_!`, followed by the counit of `e_! ⊣ e^*` (the sum over
the fibres of `e`) and by the counit of `adj`. -/
theorem existsUnique_iso_rightDerivedUpperShriek_of_chart [IsNoetherian U] [IsNoetherian S]
    [IsNoetherian 𝔸(ULift.{u} (Fin d); S)] (e : U ⟶ 𝔸(ULift.{u} (Fin d); S))
    [_root_.AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [HasCompactification (e ≫ (𝔸(ULift.{u} (Fin d); S) ↘ S))]
    (adj : R((𝔸(ULift.{u} (Fin d); S) ↘ S))_![ModuleCat.{u + 1} Λ] ⊣
      L(((𝔸(ULift.{u} (Fin d); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ 𝔸(ULift.{u} (Fin d); S) d) :
    ∃! φ : (L(((𝔸(ULift.{u} (Fin d); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
          twistShift Λ 𝔸(ULift.{u} (Fin d); S) d) ⋙
            (upperStar (ModuleCat.{u + 1} Λ) e).mapDerivedCategory ≅
        R(e ≫ (𝔸(ULift.{u} (Fin d); S) ↘ S))^![Λ],
      ∀ (N : EtaleCompactSupportNormalization Λ) (K : DerivedCategoryModule Λ S),
        (R(e ≫ (𝔸(ULift.{u} (Fin d); S) ↘ S))_![ModuleCat.{u + 1} Λ]).map (φ.hom.app K) ≫
            (rightDerivedUpperShriekAdjunction Λ
              (e ≫ (𝔸(ULift.{u} (Fin d); S) ↘ S))).counit.app K =
          (etaleAmbientLeftComparison Λ N e (𝔸(ULift.{u} (Fin d); S) ↘ S)
                (HasCompactification.compactification _)
                (HasCompactification.compactification _)).inv.app
              ((upperStar (ModuleCat.{u + 1} Λ) e).mapDerivedCategory.obj
                ((twistShift Λ 𝔸(ULift.{u} (Fin d); S) d).obj
                  ((L(((𝔸(ULift.{u} (Fin d); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj K))) ≫
            (R((𝔸(ULift.{u} (Fin d); S) ↘ S))_![ModuleCat.{u + 1} Λ]).map
              ((derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) e
                inferInstance).counit.app
                ((twistShift Λ 𝔸(ULift.{u} (Fin d); S) d).obj
                  ((L(((𝔸(ULift.{u} (Fin d); S) ↘ S))^*[ModuleCat.{u + 1} Λ])).obj K))) ≫
            adj.counit.app K :=
  existsUnique_etaleAmbientAdjointLocalityIso Λ e (𝔸(ULift.{u} (Fin d); S) ↘ S)
    (HasCompactification.compactification _) (HasCompactification.compactification _)
    (L(((𝔸(ULift.{u} (Fin d); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
      twistShift Λ 𝔸(ULift.{u} (Fin d); S) d)
    R(e ≫ (𝔸(ULift.{u} (Fin d); S) ↘ S))^![Λ] adj
    (rightDerivedUpperShriekAdjunction Λ (e ≫ (𝔸(ULift.{u} (Fin d); S) ↘ S)))

/-- Blueprint `proposition-exceptional-inverse-image-smooth-morphism--3`: *the dualizing complex
on a chart*. In the situation of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_chart`,
the dualizing complex `ω_f = Rf^! Λ_S` restricts on the chart `U` to

`ω_f|_U ≅ Λ_U(d)[2d]`. -/
theorem nonempty_iso_leftDerivedUpperStar_dualizingComplex_of_chart
    (u : U ⟶ X) [IsOpenImmersion u] [QuasiCompact u] (f : X ⟶ S) [HasCompactification f]
    (e : U ⟶ 𝔸(ULift.{u} (Fin d); S)) [_root_.AlgebraicGeometry.Etale e] [IsSeparated e]
    [QuasiCompact e] (h : U ⟶ S) (hu : u ≫ f = h) (he : e ≫ (𝔸(ULift.{u} (Fin d); S) ↘ S) = h)
    [HasCompactification h] :
    Nonempty ((L((u)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ f) ≅
      (tateObject Λ U d)⟦2 * (d : ℤ)⟧) := by
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin d); S) := .of_hom (_ ↘ S)
  have : HasInvertibleExponent Λ U := .of_hom e
  obtain ⟨φ⟩ := nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_chart Λ d u f e
    h hu he
  exact ⟨φ.app (𝟙_ _) ≪≫ leftDerivedUpperStarTwistShiftIso Λ e d _ ≪≫
    (twistShift Λ U d).mapIso ((L((e)^*[ModuleCat.{u + 1} Λ])).mapIso
      (leftDerivedUpperStarUnitIso _ _) ≪≫ leftDerivedUpperStarUnitIso _ _) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso (derivedTensorLeftUnitor _ U _)⟩

end Etale

end AlgebraicGeometry
