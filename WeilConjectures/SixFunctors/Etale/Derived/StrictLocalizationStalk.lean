/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtension
public import WeilConjectures.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.GeometricFibreStalk
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget

/-!
# Geometric stalks of higher direct images along quasi-compact quasi-separated morphisms

Let `f : X ⟶ S` be quasi-compact and quasi-separated, `s : Spec Ω ⟶ S` a geometric point with
`Ω` algebraically closed, `S_(s)` the strict localization of `S` at `s` and
`X₀ = X ×_S S_(s)`, with projection `p₀ : X₀ ⟶ X`. For an étale sheaf `G` of `Λ`-modules on `X`
the stalk at `s` of `Rᵠf_* G` is, as an abelian group, the étale cohomology group
`Hᵠ(X₀, p₀^* G)` (`AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_of_isPullback`,
blueprint `prop-weil-pbc-strict-henselization-stalk-formula`).

The proof passes to the underlying abelian sheaves, pulls back to the strict localization, where
the stalk of the derived base change map at the closed point is invertible
(`AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_closedStalk`), and computes the
stalk at the closed point of a higher direct image over a strictly henselian local ring as
cohomology of the total space
(`AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_homology_rightDerivedFunctorPlus_of_henselian`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Abelian

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The evaluation `𝒪^{sh}_{S,s} ⟶ Ω` of the strict henselization at a geometric point is a
local homomorphism. -/
instance isLocalHom_strictHenselizationEval : IsLocalHom (strictHenselizationEval s).hom :=
  ⟨fun _ ha ↦ isUnit_of_strictHenselizationEval_ne_zero ha.ne_zero⟩

/-- The geometric point `Spec Ω ⟶ S_(s)` lying over `s` factors through the closed point
`Spec κ ⟶ S_(s)` of the strict localization, `κ` its residue field. -/
lemma spec_map_lift_comp_spec_map_residue :
    Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.lift (strictHenselizationEval s).hom)) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue (strictHenselization s))) =
      Spec.map (strictHenselizationEval s) := by
  rw [← Spec.map_comp]
  congr 1

/-- **Geometric stalks of higher direct images (abelian sheaves).** For `f : X ⟶ S`
quasi-compact and quasi-separated, a geometric point `s : Spec Ω ⟶ S` (`Ω` algebraically
closed), and a cartesian square exhibiting `X₀ = X ×_S S_(s)`, the stalk at `s` of `Rᵠf_* F`
is `Hᵠ(X₀, p₀^* F)`. -/
theorem nonempty_addEquiv_sheafFiber_homology_rightDerivedFunctorPlus_of_isPullback
    {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ strictLocalization s)
    (sq : IsPullback p₀ f₀ f (strictLocalizationToBase s))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Nonempty (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          (((f)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≃+
      Sheaf.H ((p₀)^*[AddCommGrpCat.{u + 1}].obj F) q) := by
  let j := strictLocalizationToBase s
  let A := strictHenselization s
  let s' : Spec (.of Ω) ⟶ strictLocalization s := Spec.map (strictHenselizationEval s)
  have hs' : s' ≫ j = s := spec_map_strictHenselizationEval_comp_strictLocalizationToBase s
  let t₀ : Spec (.of (IsLocalRing.ResidueField A)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let a : Spec (.of Ω) ⟶ Spec (.of (IsLocalRing.ResidueField A)) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.lift (strictHenselizationEval s).hom))
  have ha : a ≫ t₀ = s' := spec_map_lift_comp_spec_map_residue s
  let eA : Spec (.of A) ≅ strictLocalization s := Iso.refl _
  have sq₀ : IsPullback p₀ f₀ f (eA.hom ≫ j) := by
    convert sq using 1
    exact Category.id_comp j
  have hBC := isIso_strictHenselization_baseChange_closedStalk f s eA p₀ f₀ sq₀ a F q
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let L := ((f)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlus.obj K
  let H := DerivedCategory.Plus.homologyFunctor (Sheaf (strictLocalization s).smallEtaleTopology
    AddCommGrpCat.{u + 1}) (q : ℤ)
  let BC := (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀.toCommSq).app K
  let Φ := (pointSmallEtale (a ≫ t₀)).sheafFiber (A := AddCommGrpCat.{u + 1})
  have hs'' : (a ≫ t₀) ≫ eA.hom ≫ j = s := by
    rw [ha]
    exact hs'
  -- the stalk at `s` is the stalk at `a ≫ t₀` of the pullback to the strict localization
  let e₁ : ((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj L) ≅
      Φ.obj (H.obj ((((eA.hom ≫ j))^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.obj L)) :=
    eqToIso (by rw [hs'']) ≪≫
      ((upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} (eA.hom ≫ j) (a ≫ t₀)).app _).symm ≪≫
      Φ.mapIso ((((eA.hom ≫ j))^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlusHomologyFunctorIso
          (q : ℤ)).app L)
  -- the base change map is invertible on the stalk at `a ≫ t₀`
  let e₂ := asIso (Φ.map (H.map BC))
  let e₃ := Φ.mapIso (H.mapIso (((f₀)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlus.mapIso
    ((((p₀)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).app F)))
  let M := H.obj (((f₀)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj ((p₀)^*[AddCommGrpCat.{u + 1}].obj F)))
  have : IsIso ((pointSmallEtalePrecomp t₀ a).sheafFiber.app M) :=
    isIso_pointSmallEtalePrecomp_sheafFiber t₀ a M
  let e₄ := asIso ((pointSmallEtalePrecomp t₀ a).sheafFiber.app M)
  obtain ⟨e₅⟩ := nonempty_addEquiv_sheafFiber_homology_rightDerivedFunctorPlus_of_henselian
    (A := A) f₀ ((p₀)^*[AddCommGrpCat.{u + 1}].obj F) q
  exact ⟨(e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄.symm).addCommGroupIsoToAddEquiv.trans e₅⟩

end Abelian

section Module

variable {Λ : Type (u + 1)} [CommRing Λ] {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [QuasiSeparated f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- **Geometric stalks of higher direct images.** For `f : X ⟶ S` quasi-compact and
quasi-separated, a geometric point `s : Spec Ω ⟶ S` (`Ω` algebraically closed), a cartesian
square exhibiting `X₀ = X ×_S S_(s)` with projection `p₀ : X₀ ⟶ X`, and an étale sheaf `G` of
`Λ`-modules on `X`, the stalk at `s` of `Rᵠf_* G` is, as an abelian group, the étale cohomology
group `Hᵠ(X₀, p₀^* G)` of the underlying abelian sheaf of `p₀^* G`. -/
theorem nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_of_isPullback
    {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ strictLocalization s)
    (sq : IsPullback p₀ f₀ f (strictLocalizationToBase s))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    Nonempty (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
        ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) ≃+
      Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((p₀)^*[ModuleCat.{u + 1} Λ].obj G)) q) := by
  obtain ⟨a⟩ := nonempty_addEquiv_sheafFiber_homology_rightDerivedFunctorPlus_of_isPullback f s
    p₀ f₀ sq ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) q
  let t := pointSmallEtale s
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  let e₁ := (t.sheafFiber (A := ModuleCat.{u + 1} Λ)).mapIso
    ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app K).symm)
  let e₂ := (t.sheafFiber (A := AddCommGrpCat.{u + 1})).mapIso
    (forget₂HomologyRightDerivedFunctorPlusIso f G q)
  exact ⟨e₁.toLinearEquiv.toAddEquiv.trans
    ((sheafFiberForget₂RestrictScalarsAddEquiv _ _).trans
      (e₂.addCommGroupIsoToAddEquiv.trans
        (a.trans (sheafHAddEquivOfIso (asIso (upperStarForget₂Comparison Λ p₀ G)) q))))⟩

end Module

end Etale

end AlgebraicGeometry
