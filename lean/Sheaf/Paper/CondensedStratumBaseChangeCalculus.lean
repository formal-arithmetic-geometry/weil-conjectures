/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

import Sheaf.Paper.ProfinitePointPullback
import Sheaf.Paper.CondensedOpenClosedRecollement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek

/-! # Exact unbounded stratum base change

Source: Stacks Project, Tags 09AA, 09BM, 09BN and 09AH, and the Local models
paragraph of the blueprint `det-lem-int-tensor-pullback.proof.md`.
(blueprint: lem-sfb-condensed-stratum-base-change-calculus)

This module contains the existing termwise functors and actual adjunction mates,
and proves their support and unbounded base-change calculus. The constructions
are retained verbatim from IntegralBoundedStratumBaseChange.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralBoundedStratumBaseChange

section Maps

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {S' S T' T : Scheme.{u}} {hS : S' ⟶ S} {a' : S' ⟶ T'}
  {a : S ⟶ T} {h : T' ⟶ T}

/-- The exact module pullback applied termwise, with its structural arguments shared.
Source: Stacks 09AA/09BN, bounded module pullback
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.upperStar Λ f).mapDerivedCategory

/-- Open extension by zero applied termwise.
Source: Stacks 09BN/09AH
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def openExtension {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :=
  (CondensedRing.openImmersionLowerShriek Λ f).mapDerivedCategory

/-- The actual localized open adjunction, with the preceding named functors.
Source: Stacks 09BN, adjunction j_! to j^*
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def openAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    openExtension Λ f ⊣ pullback Λ f :=
  CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ f

/-- Closed direct image applied termwise using its exactness witness.
Source: Stacks 09BM
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def closedDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [PreservesFiniteColimits (CondensedRing.lowerStar Λ f)] :=
  (CondensedRing.lowerStar Λ f).mapDerivedCategory

/-- The actual localized closed adjunction.
Source: Stacks 09AA/09BM
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def closedAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [PreservesFiniteColimits (CondensedRing.lowerStar Λ f)] :
    pullback Λ f ⊣ closedDirectImage Λ f :=
  (CondensedRing.upperStarLowerStarAdjunction Λ f).mapDerivedCategoryAdjunction

/-- Pullback composition around the given commutative square, localized termwise.
Source: Stacks 09AA/09BN, pullback composition in the base-change construction
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def pullbackSquare (sq : CommSq hS a' a h) :
    (pullback Λ a) ⋙
        (pullback Λ hS) ≅
      (pullback Λ h) ⋙
        (pullback Λ a') :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((CondensedRing.upperStarComp Λ hS a).symm ≪≫
        eqToIso (congrArg (CondensedRing.upperStar Λ) sq.w) ≪≫
          CondensedRing.upperStarComp Λ a' h) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The open exchange map beta, the mate of the actual pullback-composition comparison.
Source: Stacks 09BN/09AH and the node proof, Step 4
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def openMate [IsOpenImmersion a] [IsOpenImmersion a'] (sq : CommSq hS a' a h) :
    (pullback Λ hS) ⋙
        (openExtension Λ a') ⟶
      (openExtension Λ a) ⋙
        (pullback Λ h) :=
  Adjunction.exchangeLeft
    (openAdjunction Λ a)
    (openAdjunction Λ a')
    (pullbackSquare Λ sq)

/-- The closed exchange map gamma, unit insertion followed by square transport and counit.
The exactness witnesses merely allow the specified termwise derived functors to be named.
Source: Stacks 09AA/09BM/09AH and the node proof, Step 4
(blueprint: lem-sfb-integral-bounded-stratum-base-change). -/
def closedMate [PreservesFiniteColimits (CondensedRing.lowerStar Λ a)]
    [PreservesFiniteColimits (CondensedRing.lowerStar Λ a')] (sq : CommSq hS a' a h) :
    (closedDirectImage Λ a) ⋙
        (pullback Λ h) ⟶
      (pullback Λ hS) ⋙
        (closedDirectImage Λ a') :=
  Adjunction.exchangeRight
    (closedAdjunction Λ a)
    (closedAdjunction Λ a')
    (pullbackSquare Λ sq).symm

private instance pullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback Λ f).Additive :=
  inferInstanceAs (CondensedRing.upperStar Λ f).mapDerivedCategory.Additive

end Maps

/-- The actual termwise open adjunction unit is invertible, by full faithfulness
and exact-derived localization.
Source: Stacks 09AA, 09BM, 09BN and 09AH; blueprint Local models.
(blueprint: lem-sfb-condensed-stratum-base-change-calculus). -/
theorem open_unit_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (openAdjunction Λ j).unit := by
  have : IsIso (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  exact Adjunction.isIso_mapDerivedCategoryAdjunction_unit _

private theorem cartesian_module_counit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X Up Xp : Scheme.{u}}
    {j : U ⟶ X} {g : Xp ⟶ X} {jp : Up ⟶ Xp} {gp : Up ⟶ U}
    [IsOpenImmersion j] [IsOpenImmersion jp] (sq : IsPullback gp jp j g)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    IsIso ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ jp).counit.app
      ((CondensedRing.upperStar Λ g).obj
        ((CondensedRing.openImmersionLowerShriek Λ j).obj M))) := by
  let e := (profinitePointModuleForgetPullbackIso Λ g).app
      ((CondensedRing.openImmersionLowerShriek Λ j).obj M) ≪≫
    ((ProEtale.openImmersionLowerShriekBaseChangeIso Ab.{u + 1} sq).app M.X).symm
  apply (Adjunction.isIso_counit_app_iff_mem_essImage _).2
  apply CondensedRing.mem_essImage_openImmersionLowerShriek_of_mem_essImage Λ jp
  exact ⟨_, ⟨e.symm⟩⟩

private theorem cartesian_derived_counit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X Up Xp : Scheme.{u}}
    {j : U ⟶ X} {g : Xp ⟶ X} {jp : Up ⟶ Xp} {gp : Up ⟶ U}
    [IsOpenImmersion j] [IsOpenImmersion jp] (sq : IsPullback gp jp j g)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))) :
    IsIso ((openAdjunction Λ jp).counit.app
      ((pullback Λ g).obj ((openExtension Λ j).obj K))) := by
  let F := CondensedRing.openImmersionLowerShriek Λ j ⋙ CondensedRing.upperStar Λ g
  let L := CondensedRing.openImmersionLowerShriek Λ jp
  let R := CondensedRing.upperStar Λ jp
  let adj := CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ jp
  have : IsIso adj.unit := Adjunction.unit_isIso_of_L_fully_faithful _
  have ff := adj.mapDerivedCategoryAdjunction.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  let α : F ⋙ (R ⋙ L) ⟶ F :=
    Functor.whiskerLeft F adj.counit ≫ (Functor.rightUnitor F).hom
  have hαapp (M) : IsIso (α.app M) := by
    have : IsIso (adj.counit.app (F.obj M)) := cartesian_module_counit Λ sq M
    dsimp only [α, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let e : F.mapDerivedCategory ⋙ (R.mapDerivedCategory ⋙ L.mapDerivedCategory) ≅
      F.mapDerivedCategory :=
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso R L).symm ≪≫
      (Functor.mapDerivedCategoryCompIso F (R ⋙ L)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso α)
  have hc := adj.mapDerivedCategoryAdjunction.isIso_counit_app_of_iso (e.app K).symm
  exact (NatTrans.isIso_app_iff_of_iso adj.mapDerivedCategoryAdjunction.counit
    ((Functor.mapDerivedCategoryCompIso _ _).symm.app K)).2 hc

/-- The canonical open mate for a cartesian square is invertible on every
unbounded input. The pulled-back open extension lies in the primed essential
image, so the counit factor is invertible; the unit and square factors are also
invertible.
Source: Stacks 09AA, 09BM, 09BN and 09AH; blueprint Local models.
(blueprint: lem-sfb-condensed-stratum-base-change-calculus). -/
theorem open_mate_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X Up Xp : Scheme.{u}}
    {j : U ⟶ X} {g : Xp ⟶ X} {jp : Up ⟶ Xp} {gp : Up ⟶ U}
    [IsOpenImmersion j] [IsOpenImmersion jp] (sq : IsPullback gp jp j g) :
    IsIso (openMate Λ sq.toCommSq) := by
  have := open_unit_iso Λ j
  have h (K) : IsIso ((openMate Λ sq.toCommSq).app K) := by
    have := cartesian_derived_counit Λ sq K
    simp only [openMate, Adjunction.exchangeLeft_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- A quasi-compact open complement supplies exact closed direct image and an
invertible actual underived closed counit, by condensed recollement and full
faithfulness.
Source: Stacks 09AA, 09BM, 09BN and 09AH; blueprint Local models.
(blueprint: lem-sfb-condensed-stratum-base-change-calculus). -/
theorem closed_data
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ) :
    PreservesFiniteColimits (CondensedRing.lowerStar Λ i) ∧
      IsIso (CondensedRing.upperStarLowerStarAdjunction Λ i).counit := by
  obtain ⟨hc, hs⟩ := CondensedRing.condensed_open_closed_recollement Λ i j hij
  have := hs.2.2.2.2.2.2.2.2.2.1
  have := hs.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨hc, Adjunction.counit_isIso_of_R_fully_faithful _⟩

/-- The exact termwise restriction of an open extension to a disjoint morphism
vanishes. Apply the underived support theorem to each homology object and use
the exact extension homology comparison.
Source: Stacks 09AA, 09BM, 09BN and 09AH; blueprint Local models.
(blueprint: lem-sfb-condensed-stratum-base-change-calculus). -/
theorem mixed_open_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j]
    (hij : Disjoint (Set.range j) (Set.range i))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))) :
    IsZero ((pullback Λ i).obj ((openExtension Λ j).obj K)) := by
  apply (CondensedRing.upperStar Λ i).isZero_mapDerivedCategory_obj
  intro n
  exact (CondensedRing.isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint
    Λ j i hij _).of_iso ((CondensedRing.upperStar Λ i).mapIso
      (((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategoryHomologyFunctorIso
        n).symm.app K))

/-- The mixed open restriction of an exact closed direct image vanishes. Two
adjunction Hom equivalences reduce its identity to a morphism from an open
extension restricted to a disjoint closed support; then descend through
homology.
Source: Stacks 09AA, 09BM, 09BN and 09AH; blueprint Local models.
(blueprint: lem-sfb-condensed-stratum-base-change-calculus). -/
theorem mixed_closed_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    [PreservesFiniteColimits (CondensedRing.lowerStar Λ i)]
    (hij : Disjoint (Set.range j) (Set.range i))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    IsZero ((pullback Λ j).obj ((closedDirectImage Λ i).obj K)) := by
  apply (CondensedRing.upperStar Λ j).isZero_mapDerivedCategory_obj
  intro n
  let M := (DerivedCategory.homologyFunctor _ n).obj K
  have hz (N) : IsZero ((CondensedRing.upperStar Λ j).obj
      ((CondensedRing.lowerStar Λ i).obj N)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv
      _ _).symm.injective
    apply ((CondensedRing.upperStarLowerStarAdjunction Λ i).homEquiv _ _).symm.injective
    exact (CondensedRing.isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint
      Λ j i hij _).eq_of_src _ _
  exact (hz M).of_iso ((CondensedRing.upperStar Λ j).mapIso
    (((CondensedRing.lowerStar Λ i).mapDerivedCategoryHomologyFunctorIso n).symm.app K))

/-- The open mate satisfies the actual unit-transpose identity. This is the
apply-symm-apply identity of the primed adjunction Hom equivalence.
Source: Stacks 09AA, 09BM, 09BN and 09AH; blueprint Local models.
(blueprint: lem-sfb-condensed-stratum-base-change-calculus). -/
theorem open_mate_unit
    {A B Ap Bp : Type*} [Category A] [Category B] [Category Ap] [Category Bp]
    {J : A ⥤ B} {P : B ⥤ A} {Jp : Ap ⥤ Bp} {Pp : Bp ⥤ Ap}
    {H : A ⥤ Ap} {G : B ⥤ Bp} (a : J ⊣ P) (ap : Jp ⊣ Pp)
    (θ : P ⋙ H ≅ G ⋙ Pp) (K : A) :
    ap.unit.app (H.obj K) ≫ Pp.map ((Adjunction.exchangeLeft a ap θ).app K) =
      H.map (a.unit.app K) ≫ θ.hom.app (J.obj K) := by
  simpa only [Adjunction.exchangeLeft_app, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, Functor.id_obj] using
    (ap.homEquiv _ _).apply_symm_apply
      (H.map (a.unit.app K) ≫ θ.hom.app (J.obj K))

/-- The closed mate satisfies the actual counit-transpose identity. This is the
symm-apply-apply identity of the primed adjunction Hom equivalence.
Source: Stacks 09AA, 09BM, 09BN and 09AH; blueprint Local models.
(blueprint: lem-sfb-condensed-stratum-base-change-calculus). -/
theorem closed_mate_counit
    {A B Ap Bp : Type*} [Category A] [Category B] [Category Ap] [Category Bp]
    {Q : B ⥤ A} {I : A ⥤ B} {Qp : Bp ⥤ Ap} {Ip : Ap ⥤ Bp}
    {H : A ⥤ Ap} {G : B ⥤ Bp} (a : Q ⊣ I) (ap : Qp ⊣ Ip)
    (θ : G ⋙ Qp ≅ Q ⋙ H) (K : A) :
    Qp.map ((Adjunction.exchangeRight a ap θ).app K) ≫ ap.counit.app (H.obj K) =
      θ.hom.app (I.obj K) ≫ H.map (a.counit.app K) := by
  simpa only [Adjunction.exchangeRight_app, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, Functor.id_obj] using
    (ap.homEquiv _ _).symm_apply_apply
      (θ.hom.app (I.obj K) ≫ H.map (a.counit.app K))

/-- Complementary open and closed restrictions detect invertibility of the
closed mate. Its open restriction has zero endpoints; its closed restriction
is invertible by the counit-transpose identity and both invertible counits.
Source: Stacks 09AA, 09BM, 09BN and 09AH; blueprint Local models.
(blueprint: lem-sfb-condensed-stratum-base-change-calculus). -/
theorem closed_mate_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Z X Up Zp Xp : Scheme.{u}}
    {j : U ⟶ X} {i : Z ⟶ X} {jp : Up ⟶ Xp} {ip : Zp ⟶ Xp}
    {g : Xp ⟶ X} {gp : Up ⟶ U} {gz : Zp ⟶ Z}
    [IsOpenImmersion j] [IsClosedImmersion i] [QuasiCompact j]
    [IsOpenImmersion jp] [IsClosedImmersion ip] [QuasiCompact jp]
    [PreservesFiniteColimits (CondensedRing.lowerStar Λ i)]
    [PreservesFiniteColimits (CondensedRing.lowerStar Λ ip)]
    (hij : Set.range j = (Set.range i)ᶜ)
    (hijp : Set.range jp = (Set.range ip)ᶜ)
    (squ : CommSq gp jp j g) (sqz : CommSq gz ip i g)
    (hc : IsIso (closedAdjunction Λ i).counit)
    (hcp : IsIso (closedAdjunction Λ ip).counit) :
    IsIso (closedMate Λ sqz) := by
  have hd := Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory
    (CondensedRing.upperStar Λ jp) (CondensedRing.upperStar Λ ip)
    (CondensedRing.jointlyReflectIsomorphisms_upperStar_of_isCompl Λ ip jp
      (by rw [hijp]; exact (isCompl_compl (x := Set.range ip))))
  have h (K) : IsIso ((closedMate Λ sqz).app K) := by
    have hz₁ : IsZero ((pullback Λ jp).obj
        (((closedDirectImage Λ i) ⋙ (pullback Λ g)).obj K)) :=
      ((pullback Λ gp).map_isZero
        (mixed_closed_zero Λ i j (by rw [hij]; exact disjoint_compl_left) K)).of_iso
          ((pullbackSquare Λ squ).symm.app ((closedDirectImage Λ i).obj K))
    have hz₂ := mixed_closed_zero Λ ip jp
      (by rw [hijp]; exact disjoint_compl_left) ((pullback Λ gz).obj K)
    apply hd.isIso_of_pairFunctor _
    · exact isIso_of_source_target_iso_zero _ hz₁.isoZero hz₂.isoZero
    · have he := closed_mate_counit (closedAdjunction Λ i)
        (closedAdjunction Λ ip) (pullbackSquare Λ sqz).symm K
      have hcomp : IsIso ((pullback Λ ip).map ((closedMate Λ sqz).app K) ≫
          (closedAdjunction Λ ip).counit.app ((pullback Λ gz).obj K)) := by
        change IsIso ((pullback Λ ip).map
          ((Adjunction.exchangeRight _ _ _).app K) ≫ _)
        rw [he]
        infer_instance
      have : IsIso ((closedAdjunction Λ ip).counit.app ((pullback Λ gz).obj K)) :=
        inferInstance
      change IsIso ((pullback Λ ip).map ((closedMate Λ sqz).app K))
      let := hcomp
      exact IsIso.of_isIso_comp_right
        ((pullback Λ ip).map ((closedMate Λ sqz).app K))
        ((closedAdjunction Λ ip).counit.app ((pullback Λ gz).obj K))
  exact NatIso.isIso_of_isIso_app _

/-- Complementary ranges remain complementary after cartesian base change.
Apply the pullback image identity to the whole open and closed source, then
use preservation of complements by inverse image.
Source: Stacks 09AA, 09BM, 09BN and 09AH; blueprint Local models.
(blueprint: lem-sfb-condensed-stratum-base-change-calculus). -/
theorem complementary_base_change
    {U Z X Up Zp Xp : Scheme.{u}}
    {j : U ⟶ X} {i : Z ⟶ X} {jp : Up ⟶ Xp} {ip : Zp ⟶ Xp}
    {g : Xp ⟶ X} {gp : Up ⟶ U} {gz : Zp ⟶ Z}
    (hij : Set.range j = (Set.range i)ᶜ)
    (squ : IsPullback gp jp j g) (sqz : IsPullback gz ip i g) :
    Set.range jp = (Set.range ip)ᶜ := by
  have hu := Scheme.image_preimage_eq_of_isPullback squ Set.univ
  have hz := Scheme.image_preimage_eq_of_isPullback sqz Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at hu hz
  rw [hu, hz, hij, Set.preimage_compl]

/-- The actual closed mate is invertible on all unbounded inputs for a closed
cartesian square with locally Noetherian ambient schemes. Form the open
complement of the closed image; local Noetherianity makes it quasi-compact.
Pull it back, use complementary ranges to obtain exact closed direct images
and invertible counits from recollement, and apply closed-mate detection.
Source: Stacks 09AA, 09BM, 09BN and 09AH; blueprint Local models.
(blueprint: lem-sfb-condensed-stratum-base-change-calculus). -/
theorem closed_square_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z X Zp Xp : Scheme.{u}}
    {i : Z ⟶ X} {ip : Zp ⟶ Xp} {g : Xp ⟶ X} {gz : Zp ⟶ Z}
    [IsClosedImmersion i] [IsClosedImmersion ip]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Xp]
    (sq : IsPullback gz ip i g) :
    Exists fun [_hi : PreservesFiniteColimits (CondensedRing.lowerStar Λ i)] ↦
    Exists fun [_hip : PreservesFiniteColimits (CondensedRing.lowerStar Λ ip)] ↦
      IsIso (closedMate Λ sq.toCommSq) := by
  let U : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let j := U.ι
  let jp := CategoryTheory.Limits.pullback.snd j g
  let gp := CategoryTheory.Limits.pullback.fst j g
  have hu : Set.range j = (Set.range i)ᶜ := U.range_ι
  have squ : IsPullback gp jp j g := IsPullback.of_hasPullback j g
  have hup := complementary_base_change hu squ sq
  obtain ⟨hi, hc⟩ := closed_data Λ i j hu
  obtain ⟨hip, hcp⟩ := closed_data Λ ip jp hup
  have hdc : IsIso (closedAdjunction Λ i).counit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_counit _
  have hdcp : IsIso (closedAdjunction Λ ip).counit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_counit _
  exact ⟨hi, hip, closed_mate_iso Λ hu hup squ.toCommSq sq.toCommSq hdc hdcp⟩


end AlgebraicGeometry.ProEtale.IntegralBoundedStratumBaseChange
