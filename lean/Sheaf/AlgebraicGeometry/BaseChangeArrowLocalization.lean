/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import Sheaf.Paper.SliceSiteLocalization
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
import Sheaf.AlgebraicGeometry.SetUnderivedExchangeSectionwise
import Sheaf.AlgebraicGeometry.UnderivedExchangeSectionwise
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Underived base change and étale localization

Source: Stacks Project, Étale Cohomology, Tag 0EZR, proof of
`lemma-base-change-local`, and Sites, Tag 03EF
(blueprint: lem-sbc-base-change-arrow-localization).

The helper constructions use a specified inverse-image adjunction only to share the
formulas between sets and abelian groups. The final statement supplies precisely the
recorded inverse images and their adjunctions, rather than arbitrary comparison maps.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.BaseChangeLocalization

variable (A : Type v) [Category.{u + 1} A]
variable (L : ∀ {X S : Scheme.{u}}, (X ⟶ S) →
  Sheaf S.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A)
variable (adj : ∀ {X S : Scheme.{u}} (f : X ⟶ S), L f ⊣ Etale.lowerStar A f)

/-- Canonical inverse-image composition, obtained by taking the adjoint of the
fibre-product direct-image comparison. Source: Sites 03CB, used in Étale Cohomology 0EZR
(blueprint: lem-sbc-base-change-arrow-localization). -/
noncomputable def pullComp {X Y S : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ S)
    (k : X ⟶ S) (hk : k = h ≫ f) : L k ≅ L f ⋙ L h :=
  ((conjugateIsoEquiv (adj k) ((adj f).comp (adj h))).symm
    (Etale.lowerStarComp A h f k hk).symm).symm

/-- The canonical square comparison in the orientation used by the transpose defining beta.
Source: Étale Cohomology 0EZR and Sites 03CB
(blueprint: lem-sbc-base-change-arrow-localization). -/
noncomputable def squareIso {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : CommSq h e f g) : L f ⋙ L h ≅ L g ⋙ L e :=
  (pullComp A L adj h f (h ≫ f) rfl).symm ≪≫
    pullComp A L adj e g (h ≫ f) sq.w

/-- Inverse image along an étale morphism is restriction, with the canonical
unit normalization supplied by uniqueness of left adjoints.
Source: Sites 03EF; Étale Cohomology 0EZR
(blueprint: lem-sbc-base-change-arrow-localization). -/
noncomputable def restrictionIso {X U : Scheme.{u}} (a : U ⟶ X) [Etale a] :
    L a ≅ Etale.localizationRestriction A a inferInstance :=
  (adj a).leftAdjointUniq
    (Etale.localizationRestrictionLowerStarAdjunction A a inferInstance)

/-- Inverse-image composition and étale restriction for a commuting square.
Source: Étale Cohomology 0EZR, first restriction identity
(blueprint: lem-sbc-base-change-arrow-localization). -/
noncomputable def inverseRestrictionSquare {X U S B : Scheme.{u}}
    {a : U ⟶ X} {b : B ⟶ S} [Etale a] [Etale b]
    {f : X ⟶ S} {fU : U ⟶ B} (sq : CommSq a fU f b) :
    L f ⋙ Etale.localizationRestriction A a inferInstance ≅
      Etale.localizationRestriction A b inferInstance ⋙ L fU :=
  Functor.isoWhiskerLeft (L f) (restrictionIso A L adj a).symm ≪≫
    squareIso A L adj sq ≪≫
    Functor.isoWhiskerRight (restrictionIso A L adj b) (L fU)

/-- Direct-image slice localization, formed from the canonical fibre-product comparison.
No base-change map is assumed invertible here: only the site-level pullback comparison
is inverted. Source: Sites 03EF; Étale Cohomology 0EZR
(blueprint: lem-sbc-base-change-arrow-localization). -/
noncomputable def directRestrictionSquare {X Y U V : Scheme.{u}}
    {h : Y ⟶ X} {a : U ⟶ X} {d : V ⟶ Y} {hU : V ⟶ U}
    [Etale a] [Etale d] (sq : IsPullback d hU h a) :
    Etale.lowerStar A h ⋙ Etale.localizationRestriction A a inferInstance ≅
      Etale.localizationRestriction A d inferInstance ⋙ Etale.lowerStar A hU := by
  letI := Scheme.isContinuous_overPullback @Etale @Etale le_rfl hU
  letI := Scheme.isContinuous_overPullback @Etale @Etale le_rfl h
  letI := Scheme.isContinuous_overMap (inferInstance : Etale d) le_rfl
  letI := Scheme.isContinuous_overMap (inferInstance : Etale a) le_rfl
  letI := Functor.isContinuous_comp
    (MorphismProperty.Over.pullback @Etale ⊤ hU)
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale d))
    (U.smallGrothendieckTopology @Etale) (V.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale)
  letI := Functor.isContinuous_comp
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale a))
    (MorphismProperty.Over.pullback @Etale ⊤ h)
    (U.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale)
  letI := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (P := @Etale) (inferInstance : Etale a) (inferInstance : Etale d) sq.flip
  exact (Functor.sheafPushforwardContinuousIso
    (asIso (MorphismProperty.Over.pullbackMapComparison
      (P := @Etale) (inferInstance : Etale a) (inferInstance : Etale d)
      sq.flip.toCommSq)) A (U.smallGrothendieckTopology @Etale)
      (Y.smallGrothendieckTopology @Etale)).symm

variable {X Y S T U B : Scheme.{u}}
variable {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
variable (sq : ChosenCartesianSquare h e f g)
variable (a : U ⟶ X) (b : B ⟶ S) [Etale a] [Etale b]
variable (fU : U ⟶ B) (fac : a ≫ f = fU ≫ b)

/-- The canonical arrow from `U ×_X Y` to `B ×_S T`, defined by the two projections.
Source: Étale Cohomology 0EZR (blueprint: lem-sbc-base-change-arrow-localization). -/
noncomputable def localArrow : pullback a h ⟶ pullback b g :=
  pullback.lift (pullback.fst a h ≫ fU) (pullback.snd a h ≫ e) (by
    simp only [Category.assoc]
    rw [← fac, ← Category.assoc, pullback.condition, Category.assoc, sq.w])

/-- The canonical Cartesian identification of the localized square, obtained by
pasting and cancelling pullback squares. Source: Étale Cohomology 0EZR
(blueprint: lem-sbc-base-change-arrow-localization). -/
noncomputable def localSquare :
    ChosenCartesianSquare (pullback.fst a h) (localArrow sq a b fU fac)
      fU (pullback.fst b g) := by
  let globalPB := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback
    sq.hom_fst sq.hom_snd
  let total := ((IsPullback.of_hasPullback a h).flip.paste_horiz globalPB.flip).flip
  have total' : IsPullback (pullback.fst a h)
      (localArrow sq a b fU fac ≫ pullback.snd b g) (fU ≫ b) g := by
    simpa only [localArrow, pullback.lift_snd, ← fac] using total
  let localPB := total'.of_bot (pullback.lift_fst _ _ _).symm
    (IsPullback.of_hasPullback b g)
  exact
    { toCommSq := localPB.toCommSq
      isoPullback := localPB.isoPullback
      hom_fst := localPB.isoPullback_hom_fst
      hom_snd := localPB.isoPullback_hom_snd }

/-- The source comparison C_L, using inverse-image composition followed by
slice localization for `g`. Source: Étale Cohomology 0EZR, first restriction identity
(blueprint: lem-sbc-base-change-arrow-localization). -/
noncomputable def leftComparison :
    (Etale.lowerStar A g ⋙ L f) ⋙ Etale.localizationRestriction A a inferInstance ≅
      Etale.localizationRestriction A (pullback.snd b g) inferInstance ⋙
        (Etale.lowerStar A (pullback.fst b g) ⋙ L fU) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Etale.lowerStar A g)
      (inverseRestrictionSquare A L adj (CommSq.mk fac)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (directRestrictionSquare A (IsPullback.of_hasPullback b g).flip) (L fU) ≪≫
    Functor.associator _ _ _

/-- The target comparison C_R, using slice localization for `h` followed by
inverse-image composition for `ed = ce_U`.
Source: Étale Cohomology 0EZR, second restriction identity
(blueprint: lem-sbc-base-change-arrow-localization). -/
noncomputable def rightComparison :
    (L e ⋙ Etale.lowerStar A h) ⋙ Etale.localizationRestriction A a inferInstance ≅
      Etale.localizationRestriction A (pullback.snd b g) inferInstance ⋙
        (L (localArrow sq a b fU fac) ⋙ Etale.lowerStar A (pullback.fst a h)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (L e)
      (directRestrictionSquare A (IsPullback.of_hasPullback a h).flip) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (inverseRestrictionSquare A L adj
        (CommSq.mk (pullback.lift_snd _ _ _).symm))
      (Etale.lowerStar A (pullback.fst a h)) ≪≫
    Functor.associator _ _ _

/-- Equality of the two canonical natural transformations, hence compatibility
for every sheaf and naturally in that sheaf. The two coefficient instances used below
are the recorded inverse-image adjunctions, not additional hypotheses.
Source: Étale Cohomology 0EZR (blueprint: lem-sbc-base-change-arrow-localization). -/
def Compatible
    (β : ∀ {X₀ Y₀ S₀ T₀ : Scheme.{u}}
      {h₀ : Y₀ ⟶ X₀} {e₀ : Y₀ ⟶ T₀} {f₀ : X₀ ⟶ S₀} {g₀ : T₀ ⟶ S₀},
      ChosenCartesianSquare h₀ e₀ f₀ g₀ →
        ∀ F : Sheaf T₀.smallEtaleTopology A,
          (L f₀).obj ((Etale.lowerStar A g₀).obj F) ⟶
            (Etale.lowerStar A h₀).obj ((L e₀).obj F)) : Prop :=
  (∀ F : Sheaf T.smallEtaleTopology A,
    (Etale.localizationRestriction A a inferInstance).map (β sq F) ≫
        (rightComparison A L adj sq a b fU fac).hom.app F =
      (leftComparison A L adj a b fU fac).hom.app F ≫
        β (localSquare sq a b fU fac)
          ((Etale.localizationRestriction A (pullback.snd b g) inferInstance).obj F)) ∧
  (∀ (F G : Sheaf T.smallEtaleTopology A) (φ : F ⟶ G),
    ((Etale.lowerStar A g ⋙ L f) ⋙
        Etale.localizationRestriction A a inferInstance).map φ ≫
      (Etale.localizationRestriction A a inferInstance).map (β sq G) ≫
        (rightComparison A L adj sq a b fU fac).hom.app G =
      ((Etale.localizationRestriction A a inferInstance).map (β sq F) ≫
        (rightComparison A L adj sq a b fU fac).hom.app F) ≫
      (Etale.localizationRestriction A (pullback.snd b g) inferInstance ⋙
        (L (localArrow sq a b fU fac) ⋙
          Etale.lowerStar A (pullback.fst a h))).map φ)

/-- The canonical underived base-change arrow commutes with étale localization,
for sets and abelian groups. Equality of natural transformations includes naturality in F.
Source: Stacks Project, Étale Cohomology, Tag 0EZR, proof of lemma-base-change-local
(blueprint: lem-sbc-base-change-arrow-localization).

Proof:
1. The fibre-product universal property gives the localized Cartesian square and
   `c e_U = e d`. For representatives define kappa from the local representative target
   to the global target by d, c and the identity on W. Its composite with ell_loc is
   ell_glob by equality of projections; kappa need not be an isomorphism.
2. Apply lem-weil-pbc-slice-site-localization and
   lem-weil-pbc-etale-site-localization-open. Together with
   lem-weil-pbc-sets-etale-inverse-image-restriction,
   lem-weil-pbc-etale-inverse-image-restriction and
   lem-weil-pbc-site-morphism-composition these give the displayed C_L and C_R.
3. A local representative (W over B, alpha, s_B) comes from its global representative
   (W over S, alpha', s), with s_B the restriction of s along
   T_B ×_B W ≅ T ×_S W. The unit formulas of
   lem-weil-pbc-sets-etale-inverse-image-composition-units and
   lem-weil-pbc-inverse-image-composition show that C_L takes the global class to
   the local class, using both factorizations fa = bf_U and the restriction formulas.
4. By lem-sbc-sets-underived-exchange-sectionwise and
   lem-weil-pbc-underived-exchange-sectionwise, the two beta maps send these classes
   to ell_glob^*(e^*s) and ell_loc^*(e_U^*s_B). C_R takes kappa^*(e^*s) to e_U^*s_B
   by the same unit and restriction formulas for ed = ce_U. Its naturality along
   ell_loc and kappa ell_loc = ell_glob give equality on every representative.
5. The universal property of sheafification (def-weil-pbc-sheafification) makes the
   two sheaf morphisms equal. All constituent arrows are natural in F, so the
   equality is an equality of natural transformations. The calculation applies
   separately to sets and abelian groups. -/
theorem baseChangeArrow_localization :
    Compatible (Type (u + 1))
      (fun {_ _} k => Scheme.etaleSetPullback k) (fun {_ _} k => Etale.setUpperLowerAdjunction k)
      sq a b fU fac (fun {_ _ _ _} {_ _ _ _} q F => Etale.setBaseChangeArrow q F) ∧
    Compatible AddCommGrpCat.{u + 1}
      (fun {_ _} k => Etale.upperStar AddCommGrpCat.{u + 1} k)
      (fun {_ _} k => Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} k)
      sq a b fU fac
      (fun {_ _ _ _} {_ _ _ _} q F =>
        (Etale.baseChangeMap AddCommGrpCat.{u + 1} q.toCommSq.flip).app F) := by
  sorry

end AlgebraicGeometry.Etale.BaseChangeLocalization
