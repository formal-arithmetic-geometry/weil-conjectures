/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.EtaleDuality
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationSheafRefinement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompIsoExchangeCompatible
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationRefinementHomotopyUnit
import all WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphTensorCore

/-!
# Section invariants along étale maps

Let `e : V' ⟶ V` be étale and `g : V ⟶ B`, `g' = e ≫ g`. Composing the adjunctions
`R(e)_! ⊣ Le^*` (`e` is étale) and `R(g)_! ⊣ Rg^!` and comparing with
`R(g')_! ≅ R(g)_! R(e)_!` identifies the exceptional inverse images,
`Rg'^! ≅ Le^* Rg^!`, hence the dualizing complexes `ω_{g'} ≅ Le^* ω_g`. For sections `s` of `g`
and `s'` of `g'` with `s' ≫ e = s` this gives an identification of section invariants

`𝒞(g', s') = Ls'^* ω_{g'} ≅ Ls'^* Le^* ω_g ≅ Ls^* ω_g = 𝒞(g, s)`.

## Main definitions

- `AlgebraicGeometry.Etale.dualizingComplexEtaleCompIso`: `ω_{g'} ≅ Le^* ω_g`.
- `AlgebraicGeometry.Etale.sectionInvariantEtaleIso`: `𝒞(g', s') ≅ 𝒞(g, s)`.

## Main statements

- `AlgebraicGeometry.Etale.sectionInvariantEtaleIso_baseChange`: these identifications commute
  with base change. Their compatibility with identities and composition is in
  `WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantEtaleComp`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Etale

variable {V' V B : Scheme.{u}} (e : V' ⟶ V) [_root_.AlgebraicGeometry.Etale e]
  [HasCompactification e] (g : V ⟶ B) (g' : V' ⟶ B) (w : e ≫ g = g') [HasCompactification g]
  [HasCompactification g'] [QuasiCompact g']

/-- The identification `Rg'^! ≅ Le^* Rg^!` for `g' = e ≫ g` with `e` étale, conjugate to the
composition isomorphism `R(g')_! ≅ R(g)_! R(e)_!` under the composite adjunction
`R(g)_! R(e)_! ⊣ Le^* Rg^!`. -/
noncomputable def rightDerivedUpperShriekEtaleCompIso :
    R(g')^![Λ] ≅ R(g)^![Λ] ⋙ L((e)^*[ModuleCat.{u + 1} Λ]) :=
  (conjugateIsoEquiv ((rightDerivedLowerShriekEtaleAdjunction Λ e).comp
      (rightDerivedUpperShriekAdjunction Λ g)) (rightDerivedUpperShriekAdjunction Λ g')
    (rightDerivedLowerShriekCompIsoOfEq Λ e g g' w)).symm

/-- The identification of dualizing complexes `ω_{g'} ≅ Le^* ω_g` for `g' = e ≫ g` with `e`
étale, obtained by composing adjunctions. -/
noncomputable def dualizingComplexEtaleCompIso :
    dualizingComplex Λ g' ≅ (L((e)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ g) :=
  (rightDerivedUpperShriekEtaleCompIso Λ e g g' w).app (𝟙_ _)

/-- The identification of section invariants `𝒞(g', s') ≅ 𝒞(g, s)` along an étale `e`, for
`g' = e ≫ g` and sections with `s' ≫ e = s`:
`Ls'^* ω_{g'} ≅ Ls'^* Le^* ω_g ≅ Ls^* ω_g`. -/
noncomputable def sectionInvariantEtaleIso (s : B ⟶ V) (s' : B ⟶ V') (hs : s' ≫ e = s) :
    sectionInvariant Λ g' s' ≅ sectionInvariant Λ g s :=
  (L((s')^*[ModuleCat.{u + 1} Λ])).mapIso (dualizingComplexEtaleCompIso Λ e g g' w) ≪≫
    ((leftDerivedUpperStarComp _ s' e s hs.symm).app _).symm

end Etale

section EtaleAdjunction

/-! ### The étale adjunction does not depend on the compactification

The comparison `De_! ⟶ Rf_!(c)` of an étale `e` with a compactification `c` is the normalized
derived comparison of the graph map, so it is compatible with refinements of compactifications
(`AlgebraicGeometry.Etale.compactificationRefinement_homotopyUnit`), hence with the comparison
isomorphisms `Rf_!(c) ≅ R(e)_!`. Consequently the mate of the inverse of `Ex_!` for a cartesian
square of étale morphisms under the adjunctions `R(e)_! ⊣ Le^*` is the canonical isomorphism
`Lv'^* Le^* ≅ Le'^* Lv^*`. -/

/-- The comparison `De_! ⟶ Rf_!(c)` is the normalized derived comparison of the graph map. -/
theorem compactificationEtaleComparison_eq_compactSupportDerivedComparison {X Y : Scheme.{u}}
    (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e] [IsSeparated e] (c : Compactification e) :
    compactificationEtaleComparison Λ e c =
      compactSupportDerivedComparison Λ e c (etaleCompactificationGraphMap Λ e c) := by
  rw [GraphExchange.graph_comparison_eq, graphComparison_eq_source]

/-- The comparison `De_! ⟶ Rf_!(c)` is compatible with the comparison along a cartesian
refinement of compactifications. -/
theorem compactificationEtaleComparison_comp_refinement {X Y : Scheme.{u}}
    {e : X ⟶ Y} [_root_.AlgebraicGeometry.Etale e] [IsSeparated e] {c d : Compactification e}
    (r : c.Refinement d) (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    compactificationEtaleComparison Λ e d ≫
        rightDerivedLowerShriekOfCompactificationComparison _ r hcart =
      compactificationEtaleComparison Λ e c := by
  have ha : etaleCompactificationGraphMap Λ e d ≫ compactificationSheafRefinement Λ r hcart =
      etaleCompactificationGraphMap Λ e c := by
    obtain ⟨h₁, h₂⟩ := compactificationSheafRefinement_properties Λ r hcart
    have : Mono (compactificationSheafToDirectImage Λ c) := NatTrans.mono_of_mono_app _
    rw [← cancel_mono (compactificationSheafToDirectImage Λ c), Category.assoc, h₁]
    refine NatTrans.ext (funext fun M ↦ ?_)
    rw [NatTrans.comp_app, NatTrans.comp_app, compactSupportGraphSheafComparison_normalization,
      compactSupportGraphSheafComparison_normalization]
  rw [compactificationEtaleComparison_eq_compactSupportDerivedComparison,
    compactificationEtaleComparison_eq_compactSupportDerivedComparison, ← ha]
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) fun K ↦ ?_
  have h := congr_app (compactificationRefinement_homotopyUnit Λ r hcart _
    (etaleCompactificationGraphMap Λ e d)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    normalizationHomotopyTransformation_app] at h
  rw [NatTrans.comp_app, compactSupportDerivedComparison_app, compactSupportDerivedComparison_app]
  exact h

/-- The comparison `De_! ⟶ Rf_!(c)` is compatible with the comparison isomorphisms
`Rf_!(c) ≅ Rf_!(d)` between compactifications. -/
theorem compactificationEtaleComparison_comp_iso {X Y : Scheme.{u}}
    {e : X ⟶ Y} [_root_.AlgebraicGeometry.Etale e] [IsSeparated e] [QuasiCompact e]
    (c d : Compactification e) :
    compactificationEtaleComparison Λ e c ≫
        (rightDerivedLowerShriekOfCompactificationIso Λ c d).hom =
      compactificationEtaleComparison Λ e d := by
  rw [rightDerivedLowerShriekOfCompactificationIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv, ← Category.assoc, compactificationEtaleComparison_comp_refinement,
    ← compactificationEtaleComparison_comp_refinement Λ (Compactification.infSnd c d)
      (Compactification.isPullback_infSnd c d), Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- The comparison `De_! ⟶ Rf_!(c)` followed by `Rf_!(c) ≅ R(e)_!` is the comparison for the
chosen compactification. -/
theorem compactificationEtaleComparison_comp_rightDerivedLowerShriekIso {X Y : Scheme.{u}}
    {e : X ⟶ Y} [_root_.AlgebraicGeometry.Etale e] [HasCompactification e] [QuasiCompact e]
    (c : Compactification e) :
    compactificationEtaleComparison Λ e c ≫ (rightDerivedLowerShriekIso Λ c).hom =
      compactificationEtaleComparison Λ e (HasCompactification.compactification e) :=
  compactificationEtaleComparison_comp_iso Λ c _

/-- The unit of `R(e)_! ⊣ Le^*` is the candidate unit of the chosen compactification. -/
theorem rightDerivedLowerShriekEtaleAdjunction_unit_app {X Y : Scheme.{u}}
    (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e] [HasCompactification e]
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekEtaleAdjunction Λ e).unit.app N =
      (compactificationEtaleUnit Λ e (HasCompactification.compactification e)).app N := by
  have := isIso_compactificationEtaleComparison Λ e (HasCompactification.compactification e)
  exact compactificationEtaleAdjunction_unit_app _ _ _ N

/-- The candidate unit of any compactification `c` of `e`, followed by `Rf_!(c) ≅ R(e)_!`, is the
unit of `R(e)_! ⊣ Le^*`. -/
theorem compactificationEtaleUnit_comp_rightDerivedLowerShriekIso {X Y : Scheme.{u}}
    (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e] [HasCompactification e] [QuasiCompact e]
    (c : Compactification e)
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactificationEtaleUnit Λ e c).app N ≫
        L((e)^*[ModuleCat.{u + 1} Λ]).map ((rightDerivedLowerShriekIso Λ c).hom.app N) =
      (rightDerivedLowerShriekEtaleAdjunction Λ e).unit.app N := by
  rw [rightDerivedLowerShriekEtaleAdjunction_unit_app,
    ← unit_map_compactificationEtaleComparison, ← unit_map_compactificationEtaleComparison,
    Category.assoc, ← Functor.map_comp, ← NatTrans.comp_app,
    compactificationEtaleComparison_comp_rightDerivedLowerShriekIso]

/-- **The étale exchange is the canonical isomorphism**: for a cartesian square
`v' ≫ e = e' ≫ v` of étale morphisms, the mate of `Ex_!⁻¹` under the adjunctions
`R(e)_! ⊣ Le^*` and `R(e')_! ⊣ Le'^*` is the canonical isomorphism `Lv'^* Le^* ≅ Le'^* Lv^*`. -/
theorem mateEquiv_rightDerivedLowerShriekEtaleAdjunction {X Y X' Y' : Scheme.{u}}
    {e : X ⟶ Y} {v : Y' ⟶ Y} {e' : X' ⟶ Y'} {v' : X' ⟶ X} [_root_.AlgebraicGeometry.Etale e]
    [_root_.AlgebraicGeometry.Etale e'] [HasCompactification e] [HasCompactification e']
    [QuasiCompact e'] (sq : IsPullback v' e' e v) :
    have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
    mateEquiv (rightDerivedLowerShriekEtaleAdjunction Λ e)
        (rightDerivedLowerShriekEtaleAdjunction Λ e')
        (inv (rightDerivedLowerShriekBaseChangeMap Λ sq)) =
      (derivedSquareUpperStarIso _ sq.toCommSq).inv := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  refine mateEquiv_eq_of_unit _ _ _ _ fun N ↦ ?_
  have h := compactificationEtaleUnit_baseChange Λ sq (HasCompactification.compactification e) N
  rw [← compactificationEtaleUnit_comp_rightDerivedLowerShriekIso Λ e'
    ((HasCompactification.compactification e).ofIsPullback sq), ← h,
    rightDerivedLowerShriekEtaleAdjunction_unit_app]
  have hE : (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
        (HasCompactification.compactification e)).app N ≫
        (rightDerivedLowerShriekIso Λ
          ((HasCompactification.compactification e).ofIsPullback sq)).hom.app
          (L((v')^*[ModuleCat.{u + 1} Λ]).obj N) =
      (rightDerivedLowerShriekBaseChangeMap Λ sq).app N :=
    rfl
  simp only [Category.assoc, ← Functor.map_comp]
  rw [reassoc_of% hE, NatIso.isIso_inv_app]
  erw [IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

end EtaleAdjunction

section BaseChange

/-- **Base change of `Rg'^! ≅ Le^* Rg^!`**: for a cartesian square `v' ≫ e = e₁ ≫ v` of étale
morphisms over the base changes `g₁` of `g` and `g₁'` of `g' = e ≫ g` along `b`, the exceptional
base change maps intertwine the identifications along `e` and `e₁`. -/
theorem rightDerivedUpperShriekEtaleCompIso_baseChange {V' V B V₁' V₁ B₁ : Scheme.{u}}
    (e : V' ⟶ V) [_root_.AlgebraicGeometry.Etale e] [HasCompactification e] (g : V ⟶ B)
    (g' : V' ⟶ B) (w : e ≫ g = g') [HasCompactification g] [HasCompactification g']
    [QuasiCompact g'] (b : B₁ ⟶ B) (e₁ : V₁' ⟶ V₁) [_root_.AlgebraicGeometry.Etale e₁]
    [HasCompactification e₁] (g₁ : V₁ ⟶ B₁) (g₁' : V₁' ⟶ B₁) (w₁ : e₁ ≫ g₁ = g₁')
    [HasCompactification g₁] [HasCompactification g₁'] [QuasiCompact g₁] [QuasiCompact g₁']
    (v : V₁ ⟶ V) (v' : V₁' ⟶ V') (sq : IsPullback v g₁ g b) (sq' : IsPullback v' g₁' g' b)
    (sqe : IsPullback v' e₁ e v)
    (K : _root_.DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedUpperShriekBaseChangeMap Λ sq').app K ≫
        (rightDerivedUpperShriekEtaleCompIso Λ e₁ g₁ g₁' w₁).hom.app
          ((L((b)^*[ModuleCat.{u + 1} Λ])).obj K) =
      (L((v')^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekEtaleCompIso Λ e g g' w).hom.app K) ≫
        (derivedSquareUpperStarIso _ sqe.toCommSq).inv.app ((R(g)^![Λ]).obj K) ≫
        (L((e₁)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekBaseChangeMap Λ sq).app K) := by
  have : QuasiCompact (e ≫ g) := w ▸ inferInstance
  have : QuasiCompact e := .of_comp e g
  have : QuasiCompact (e₁ ≫ g₁) := w₁ ▸ inferInstance
  have : QuasiCompact e₁ := .of_comp e₁ g₁
  have sqgf : IsPullback v' (e₁ ≫ g₁) (e ≫ g) b := w ▸ w₁ ▸ sq'
  have hEx := exchangeCompCompatible_of_eq (Λ := Λ) w w₁ sqe sq sq' sqgf (by
    let _ : HasCompactification (e ≫ g) := .of_eq w.symm
    let _ : HasCompactification (e₁ ≫ g₁) := .of_eq w₁.symm
    exact exchangeCompCompatible_of_paste_vert _ _ _)
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sqe
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq'
  have h := Adjunction.mateEquiv_inv_comp_conjugate (rightDerivedLowerShriekEtaleAdjunction Λ e)
    (rightDerivedUpperShriekAdjunction Λ g) (rightDerivedUpperShriekAdjunction Λ g')
    (rightDerivedLowerShriekEtaleAdjunction Λ e₁) (rightDerivedUpperShriekAdjunction Λ g₁)
    (rightDerivedUpperShriekAdjunction Λ g₁') _ _ _ _ _ hEx K
  rw [mateEquiv_rightDerivedLowerShriekEtaleAdjunction] at h
  rw [rightDerivedUpperShriekEtaleCompIso, rightDerivedUpperShriekEtaleCompIso, Iso.symm_hom,
    Iso.symm_hom]
  unfold rightDerivedUpperShriekBaseChangeMap
  convert h.symm using 2

omit [Finite Λ] in
/-- The coherence of the composition isomorphisms of derived pullbacks entering the base change
of the section invariants along an étale morphism. -/
@[reassoc]
lemma leftDerivedUpperStarComp_etaleBaseChange_coherence {B₁ B V V' V₁ V₁' : Scheme.{u}}
    (b : B₁ ⟶ B) (s : B ⟶ V) (s' : B ⟶ V') (e : V' ⟶ V) (s₁ : B₁ ⟶ V₁) (s₁' : B₁ ⟶ V₁')
    (e₁ : V₁' ⟶ V₁) (v : V₁ ⟶ V) (v' : V₁' ⟶ V') (hs : s' ≫ e = s) (hs₁ : s₁' ≫ e₁ = s₁)
    (hv₁ : s₁ ≫ v = b ≫ s) (hv₁' : s₁' ≫ v' = b ≫ s') (hv : v' ≫ e = e₁ ≫ v)
    (N : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((b)^*[ModuleCat.{u + 1} Λ])).map
        ((leftDerivedUpperStarComp _ s' e s hs.symm).inv.app N) ≫
      (leftDerivedUpperStarComp _ b s).inv.app N ≫
      (leftDerivedUpperStarComp _ s₁ v (b ≫ s) hv₁.symm).hom.app N =
    (leftDerivedUpperStarComp _ b s').inv.app ((L((e)^*[ModuleCat.{u + 1} Λ])).obj N) ≫
      (leftDerivedUpperStarComp _ s₁' v' (b ≫ s') hv₁'.symm).hom.app
        ((L((e)^*[ModuleCat.{u + 1} Λ])).obj N) ≫
      (L((s₁')^*[ModuleCat.{u + 1} Λ])).map
        ((leftDerivedUpperStarComp _ v' e).inv.app N ≫
          (leftDerivedUpperStarComp _ e₁ v (v' ≫ e) hv).hom.app N) ≫
      (leftDerivedUpperStarComp _ s₁' e₁ s₁ hs₁.symm).inv.app
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj N) := by
  have hbs : b ≫ s = (b ≫ s') ≫ e := by rw [Category.assoc, hs]
  rw [map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app_assoc _ b s' e
      (b ≫ s') s (b ≫ s) rfl hs.symm hbs,
    Functor.map_comp, Category.assoc,
    leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app_assoc
      _ s₁' v' e (b ≫ s') (v' ≫ e) (b ≫ s) hv₁'.symm rfl hbs,
    leftDerivedUpperStarComp_assoc'_app_assoc _ s₁' e₁ v s₁ (v' ≫ e) (b ≫ s) hs₁.symm hv
      hv₁.symm, Iso.hom_inv_id_app]
  erw [Category.comp_id]

/-- The unfolding of `AlgebraicGeometry.Etale.dualizingComplexEtaleCompIso`. -/
lemma dualizingComplexEtaleCompIso_hom {V' V B : Scheme.{u}} (e : V' ⟶ V)
    [_root_.AlgebraicGeometry.Etale e] [HasCompactification e] (g : V ⟶ B) (g' : V' ⟶ B)
    (w : e ≫ g = g') [HasCompactification g] [HasCompactification g'] [QuasiCompact g'] :
    (dualizingComplexEtaleCompIso Λ e g g' w).hom =
      (rightDerivedUpperShriekEtaleCompIso Λ e g g' w).hom.app (𝟙_ _) := by
  rw [dualizingComplexEtaleCompIso, Iso.app_hom]

/-- The unfolding of `AlgebraicGeometry.Etale.dualizingComplexBaseChangeMap`. -/
lemma dualizingComplexBaseChangeMap_eq_comp {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} [HasCompactification f] [HasCompactification f']
    [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    dualizingComplexBaseChangeMap Λ sq =
      (rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _) ≫
        (R(f')^![Λ]).map (leftDerivedUpperStarUnitIso _ g).hom :=
  rfl

-- `exact` compares `dualizingComplex` with `R^!` of the tensor unit inside the definitions of
-- the base change maps (deep, fast; as in `dualizingComplexBaseChangeMap_eq` of
-- `DiagonalPasteHoriz`)
set_option maxRecDepth 1000 in
/-- **Base change of `ω_{g'} ≅ Le^* ω_g`**: the identification of dualizing complexes along an
étale `e` and along its base change `e₁` are intertwined by the base change maps of the dualizing
complexes. -/
theorem dualizingComplexEtaleCompIso_baseChange {V' V B V₁' V₁ B₁ : Scheme.{u}}
    (e : V' ⟶ V) [_root_.AlgebraicGeometry.Etale e] [HasCompactification e] (g : V ⟶ B)
    (g' : V' ⟶ B) (w : e ≫ g = g') [HasCompactification g] [HasCompactification g']
    [QuasiCompact g'] (b : B₁ ⟶ B) (e₁ : V₁' ⟶ V₁) [_root_.AlgebraicGeometry.Etale e₁]
    [HasCompactification e₁] (g₁ : V₁ ⟶ B₁) (g₁' : V₁' ⟶ B₁) (w₁ : e₁ ≫ g₁ = g₁')
    [HasCompactification g₁] [HasCompactification g₁'] [QuasiCompact g₁] [QuasiCompact g₁']
    (v : V₁ ⟶ V) (v' : V₁' ⟶ V') (sq : IsPullback v g₁ g b) (sq' : IsPullback v' g₁' g' b)
    (sqe : IsPullback v' e₁ e v) :
    dualizingComplexBaseChangeMap Λ sq' ≫ (dualizingComplexEtaleCompIso Λ e₁ g₁ g₁' w₁).hom =
      (L((v')^*[ModuleCat.{u + 1} Λ])).map (dualizingComplexEtaleCompIso Λ e g g' w).hom ≫
        (derivedSquareUpperStarIso _ sqe.toCommSq).inv.app (dualizingComplex Λ g) ≫
        (L((e₁)^*[ModuleCat.{u + 1} Λ])).map (dualizingComplexBaseChangeMap Λ sq) := by
  have key (X : _root_.DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (Y : _root_.DerivedCategory (Sheaf B₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (φ : (L((b)^*[ModuleCat.{u + 1} Λ])).obj X ⟶ Y) :
      ((rightDerivedUpperShriekBaseChangeMap Λ sq').app X ≫ (R(g₁')^![Λ]).map φ) ≫
        (rightDerivedUpperShriekEtaleCompIso Λ e₁ g₁ g₁' w₁).hom.app Y =
      (L((v')^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekEtaleCompIso Λ e g g' w).hom.app X) ≫
        (derivedSquareUpperStarIso _ sqe.toCommSq).inv.app ((R(g)^![Λ]).obj X) ≫
        (L((e₁)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekBaseChangeMap Λ sq).app X ≫ (R(g₁)^![Λ]).map φ) := by
    have h := (rightDerivedUpperShriekEtaleCompIso Λ e₁ g₁ g₁' w₁).hom.naturality φ
    simp only [Functor.comp_map] at h
    rw [Category.assoc, h, reassoc_of% rightDerivedUpperShriekEtaleCompIso_baseChange Λ e g g' w b
      e₁ g₁ g₁' w₁ v v' sq sq' sqe X, Functor.map_comp]
  rw [dualizingComplexBaseChangeMap_eq_comp, dualizingComplexBaseChangeMap_eq_comp,
    dualizingComplexEtaleCompIso_hom, dualizingComplexEtaleCompIso_hom]
  exact key _ _ _

end BaseChange

section Coherence

variable {V'' V' V B : Scheme.{u}}

/-- The identifications of section invariants along étale maps commute with base change: for
`b : B₁ ⟶ B`, base changes `g₁` of `g` and `g₁'` of `g' = e ≫ g`, and the base change `e₁` of
`e`, the base change isomorphisms of section invariants carry the identification along `e` to
the identification along `e₁`. -/
theorem sectionInvariantEtaleIso_baseChange {V₁' V₁ B₁ : Scheme.{u}} (e : V' ⟶ V)
    [_root_.AlgebraicGeometry.Etale e] [HasCompactification e] (g : V ⟶ B) (g' : V' ⟶ B)
    (w : e ≫ g = g') [HasCompactification g] [HasCompactification g'] [QuasiCompact g']
    (b : B₁ ⟶ B) (e₁ : V₁' ⟶ V₁) [_root_.AlgebraicGeometry.Etale e₁] [HasCompactification e₁]
    (g₁ : V₁ ⟶ B₁) (g₁' : V₁' ⟶ B₁) (w₁ : e₁ ≫ g₁ = g₁') [HasCompactification g₁]
    [HasCompactification g₁'] [QuasiCompact g₁] [QuasiCompact g₁'] (v : V₁ ⟶ V) (v' : V₁' ⟶ V')
    (sq : IsPullback v g₁ g b) (sq' : IsPullback v' g₁' g' b) (hv : v' ≫ e = e₁ ≫ v)
    [IsIso (dualizingComplexBaseChangeMap Λ sq)] [IsIso (dualizingComplexBaseChangeMap Λ sq')]
    (s : B ⟶ V) (s' : B ⟶ V') (hs : s' ≫ e = s) (s₁ : B₁ ⟶ V₁) (s₁' : B₁ ⟶ V₁')
    (hs₁ : s₁' ≫ e₁ = s₁) (hv₁ : s₁ ≫ v = b ≫ s) (hv₁' : s₁' ≫ v' = b ≫ s') :
    (sectionInvariantBaseChangeIso Λ sq' s' s₁' hv₁').symm ≪≫
        (L((b)^*[ModuleCat.{u + 1} Λ])).mapIso (sectionInvariantEtaleIso Λ e g g' w s s' hs) ≪≫
        sectionInvariantBaseChangeIso Λ sq s s₁ hv₁ =
      sectionInvariantEtaleIso Λ e₁ g₁ g₁' w₁ s₁ s₁' hs₁ := by
  have sqe : IsPullback v' e₁ e v := IsPullback.of_bot (w ▸ w₁ ▸ sq') hv sq
  have hω := dualizingComplexEtaleCompIso_baseChange Λ e g g' w b e₁ g₁ g₁' w₁ v v' sq sq' sqe
  refine Iso.ext ?_
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.inv_comp_eq]
  dsimp only [sectionInvariantEtaleIso, sectionInvariantBaseChangeIso, Iso.trans, Iso.symm,
    Functor.mapIso, Iso.app, asIso, sectionInvariant]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (L((s₁')^*[ModuleCat.{u + 1} Λ])), hω, Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc]
  have n₁ := (leftDerivedUpperStarComp _ s₁' e₁ s₁ hs₁.symm).inv.naturality
    (dualizingComplexBaseChangeMap Λ sq)
  have n₂ := (leftDerivedUpperStarComp _ s₁' v' (b ≫ s') hv₁'.symm).hom.naturality
    (dualizingComplexEtaleCompIso Λ e g g' w).hom
  have n₃ := (leftDerivedUpperStarComp _ b s').inv.naturality
    (dualizingComplexEtaleCompIso Λ e g g' w).hom
  simp only [Functor.comp_map] at n₁ n₂ n₃
  rw [n₁, ← reassoc_of% n₂, ← reassoc_of% n₃,
    leftDerivedUpperStarComp_etaleBaseChange_coherence_assoc Λ b s s' e s₁ s₁' e₁ v v' hs hs₁
      hv₁ hv₁' hv]
  rfl

end Coherence

end Etale

end AlgebraicGeometry
