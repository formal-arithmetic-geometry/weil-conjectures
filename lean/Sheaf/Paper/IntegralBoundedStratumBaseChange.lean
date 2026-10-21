/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.IntegralDerivedCoefficientData
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.Paper.ProfinitePointPullback
import Sheaf.Paper.CondensedOpenClosedRecollement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Bounded integral base change for a stratum extension

Source: Stacks Project, Tags 09AA, 09BM, 09BN and 09AH; blueprint main-20261015,
`det-lem-int-tensor-pullback.proof.md`, Local models.
(blueprint: lem-sfb-integral-bounded-stratum-base-change)

All derived functors here apply the exact module functors termwise. Exactness of a closed
pushforward is returned as a witness, rather than assumed. The bounded inclusions retain
all bounded inputs, without a constructibility or completeness condition.
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

private theorem open_unit_iso
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

private theorem open_mate_iso
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

private theorem closed_data
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

private theorem mixed_closed_zero
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

private theorem open_mate_unit
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

private theorem closed_mate_counit
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

private theorem closed_mate_iso
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

private theorem complementary_base_change
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

private theorem closed_square_iso
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

open CondensedRing (integralCoefficientRing)

set_option maxHeartbeats 1600000 in
-- The large conjunction elaborates several exactness witnesses and derived functor instances.
/-- The canonical open and closed mates are natural isomorphisms on all bounded inputs,
with identity restrictions on their own stratum and zero restrictions on its complement.
The existential exactness witnesses supply the termwise closed derived functors.
Source: Stacks 09AA, 09BM, 09BN and 09AH; node proof, Steps 1--6
(blueprint: lem-sfb-integral-bounded-stratum-base-change).

Proof:
1. Finite type over the field gives Noetherian underlying spaces by the finite affine
cover argument of `lem-sfb-finite-type-noetherian-spectrum`; all the opens are retrocompact.
Open and closed immersions survive base change, and their ranges stay complementary
by the base-change image lemma.
2. Cartesian coefficients make pullback exact. Transport the actual module operations
and adjunctions to section-ring modules using the internal-module-operations transport
lemma. Tags 09AA/09BM/09BN/09AH give exact extension and closed direct image, mixed zero
restrictions and the localization short exact sequence. Apply the restrictions to this
sequence and use triangle identities to see that the actual open units and closed
counits are invertible; transfer back through the coefficient transport equivalences.
3. Apply exact-open-closed-unbounded calculus. The localized adjunctions have the actual
units and counits, the mixed restrictions vanish, and complementary restrictions jointly
reflect isomorphisms. Exact-functor cohomology identifies H^q(FK) with F(H^q K), so every
functor here preserves both cohomological bounds.
4. Descend pullback composition via exact-derived composition and natural-isomorphism
localization. The definitions `openMate` and `closedMate` are precisely the open transpose
and the closed unit--square--counit mate, and are natural before imposing bounds.
5. The open transpose identity gives the displayed open restriction equation. Both
units and the square comparison are invertible, so this is the identity after canonical
identification. Its closed restriction has zero source and target by mixed vanishing
and the square comparison. Joint reflection makes beta invertible.
6. The closed triangle identity gives the displayed closed restriction equation.
The counits identify this with the identity. Its open restriction is between zero
objects by mixed vanishing and square transport. Joint reflection makes gamma invertible.
Restriction along the full bounded inclusions gives the two asserted natural isomorphisms.
-/
theorem integral_bounded_open_closed_base_change
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {U : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    {T : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    {Up : Over (Spec (.of k))}
    [LocallyOfFiniteType Up.hom] [QuasiCompact Up.hom] [IsSeparated Up.hom]
    {Zp : Over (Spec (.of k))}
    [LocallyOfFiniteType Zp.hom] [QuasiCompact Zp.hom] [IsSeparated Zp.hom]
    {Tp : Over (Spec (.of k))}
    [LocallyOfFiniteType Tp.hom] [QuasiCompact Tp.hom] [IsSeparated Tp.hom]
    (h : Tp ⟶ T) (j : U ⟶ T) (i : Z ⟶ T)
    (hU : Up ⟶ U) (jp : Up ⟶ Tp) (hZ : Zp ⟶ Z) (ip : Zp ⟶ Tp)
    [IsOpenImmersion j.left] [IsClosedImmersion i.left]
    [IsOpenImmersion jp.left] [IsClosedImmersion ip.left]
    (hcomp : Set.range j.left = (Set.range i.left)ᶜ)
    (sqU : IsPullback hU.left jp.left j.left h.left)
    (sqZ : IsPullback hZ.left ip.left i.left h.left) :
    Exists fun [_hi : PreservesFiniteColimits (CondensedRing.lowerStar (integralCoefficientRing l
            E) i.left)] ↦
    Exists fun [_hip : PreservesFiniteColimits (CondensedRing.lowerStar (integralCoefficientRing l
            E)
            ip.left)] ↦
      (∃ beta : DerivedCategory.Bounded.ι ⋙ ((pullback (integralCoefficientRing l E) hU.left) ⋙
            (openExtension (integralCoefficientRing l E) jp.left)) ≅
          DerivedCategory.Bounded.ι ⋙ ((openExtension (integralCoefficientRing l E) j.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)),
        beta.hom = Functor.whiskerLeft DerivedCategory.Bounded.ι (openMate
            (integralCoefficientRing l E)
            sqU.toCommSq)) ∧
      (∃ gamma : DerivedCategory.Bounded.ι ⋙ ((closedDirectImage (integralCoefficientRing l E)
            i.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)) ≅
          DerivedCategory.Bounded.ι ⋙ ((pullback (integralCoefficientRing l E) hZ.left) ⋙
            (closedDirectImage (integralCoefficientRing l E) ip.left)),
        gamma.hom = Functor.whiskerLeft DerivedCategory.Bounded.ι (closedMate
            (integralCoefficientRing l E)
            sqZ.toCommSq)) ∧
      (∀ N : DerivedCategory.Bounded
          (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
            (condensedRingObj (integralCoefficientRing l E) U.left)),
        DerivedCategory.TStructure.t.bounded
            (((pullback (integralCoefficientRing l E) hU.left) ⋙
            (openExtension (integralCoefficientRing l E) jp.left)).obj N.obj) ∧
        DerivedCategory.TStructure.t.bounded
            (((openExtension (integralCoefficientRing l E) j.left)
            ⋙ (pullback (integralCoefficientRing l E) h.left)).obj N.obj) ∧
        IsIso ((openAdjunction (integralCoefficientRing l E) jp.left).unit.app ((pullback
            (integralCoefficientRing l E) hU.left).obj
            N.obj)) ∧
        IsIso ((openAdjunction (integralCoefficientRing l E) j.left).unit.app N.obj) ∧
        (openAdjunction (integralCoefficientRing l E) jp.left).unit.app
            ((pullback (integralCoefficientRing l E) hU.left).obj N.obj) ≫
            (pullback (integralCoefficientRing l E) jp.left).map
            ((openMate
            (integralCoefficientRing l
            E) sqU.toCommSq).app N.obj) =
          (pullback (integralCoefficientRing l E) hU.left).map
            ((openAdjunction (integralCoefficientRing l E) j.left).unit.app N.obj) ≫
            (pullbackSquare (integralCoefficientRing l E) sqU.toCommSq).hom.app
            ((openExtension (integralCoefficientRing l E) j.left).obj N.obj) ∧
        IsZero ((pullback (integralCoefficientRing l E) ip.left).obj
          (((pullback (integralCoefficientRing l E) hU.left) ⋙
            (openExtension (integralCoefficientRing l E) jp.left)).obj N.obj)) ∧
        IsZero ((pullback (integralCoefficientRing l E) ip.left).obj
          (((openExtension (integralCoefficientRing l E) j.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)).obj N.obj)) ∧
        (pullback (integralCoefficientRing l E) ip.left).map
            ((openMate
            (integralCoefficientRing l E)
            sqU.toCommSq).app N.obj) = 0) ∧
      (∀ N : DerivedCategory.Bounded
          (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
            (condensedRingObj (integralCoefficientRing l E) Z.left)),
        DerivedCategory.TStructure.t.bounded
            (((closedDirectImage (integralCoefficientRing l E) i.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)).obj N.obj) ∧
        DerivedCategory.TStructure.t.bounded
            (((pullback (integralCoefficientRing l E) hZ.left) ⋙
            (closedDirectImage (integralCoefficientRing l E) ip.left)).obj N.obj) ∧
        IsIso ((closedAdjunction (integralCoefficientRing l E) i.left).counit.app N.obj) ∧
        IsIso ((closedAdjunction (integralCoefficientRing l E) ip.left).counit.app ((pullback
            (integralCoefficientRing l E) hZ.left).obj N.obj)) ∧
        (pullback (integralCoefficientRing l E) ip.left).map
            ((closedMate
            (integralCoefficientRing l
            E) sqZ.toCommSq).app N.obj) ≫
            (closedAdjunction (integralCoefficientRing l E) ip.left).counit.app ((pullback
            (integralCoefficientRing l E) hZ.left).obj N.obj) =
          (pullbackSquare (integralCoefficientRing l E) sqZ.toCommSq).inv.app
            ((closedDirectImage (integralCoefficientRing l E) i.left).obj N.obj) ≫
            (pullback (integralCoefficientRing l E) hZ.left).map
            ((closedAdjunction (integralCoefficientRing l E) i.left).counit.app N.obj) ∧
        IsZero ((pullback (integralCoefficientRing l E) jp.left).obj
          (((closedDirectImage (integralCoefficientRing l E) i.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)).obj N.obj)) ∧
        IsZero ((pullback (integralCoefficientRing l E) jp.left).obj
          (((pullback (integralCoefficientRing l E) hZ.left) ⋙
            (closedDirectImage (integralCoefficientRing l E) ip.left)).obj N.obj)) ∧
        (pullback (integralCoefficientRing l E) jp.left).map
            ((closedMate
            (integralCoefficientRing l
            E) sqZ.toCommSq).app N.obj) = 0) := by
  let Λ := integralCoefficientRing l E
  have : QuasiCompact j.left := by
    have : QuasiCompact (j.left ≫ T.hom) := by rw [Over.w j]; infer_instance
    exact QuasiCompact.of_comp j.left T.hom
  have : QuasiCompact jp.left := by
    have : QuasiCompact (jp.left ≫ Tp.hom) := by rw [Over.w jp]; infer_instance
    exact QuasiCompact.of_comp jp.left Tp.hom
  have hcomp' := complementary_base_change hcomp sqU sqZ
  obtain ⟨hi, hci⟩ := closed_data Λ i.left j.left hcomp
  obtain ⟨hip, hcip⟩ := closed_data Λ ip.left jp.left hcomp'
  have hdi : IsIso (closedAdjunction Λ i.left).counit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_counit _
  have hdip : IsIso (closedAdjunction Λ ip.left).counit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_counit _
  have hβ := open_mate_iso Λ sqU
  have hγ := closed_mate_iso Λ hcomp hcomp' sqU.toCommSq sqZ.toCommSq hdi hdip
  refine ⟨hi, hip, ⟨Functor.isoWhiskerLeft _ (asIso (openMate Λ sqU.toCommSq)), rfl⟩,
    ⟨Functor.isoWhiskerLeft _ (asIso (closedMate Λ sqZ.toCommSq)), rfl⟩, ?_, ?_⟩
  · intro N
    have hu := open_unit_iso Λ j.left
    have hup := open_unit_iso Λ jp.left
    have hz₁ := (CondensedRing.isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint
      Λ jp.left ip.left (by rw [hcomp']; exact disjoint_compl_left)
      ((pullback Λ hU.left).obj N.obj)).of_iso
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ ip.left).app _).symm
    have hz₂ := ((pullback Λ hZ.left).map_isZero
      ((CondensedRing.isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint
        Λ j.left i.left (by rw [hcomp]; exact disjoint_compl_left) N.obj).of_iso
          ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ i.left).app _).symm)).of_iso
            ((pullbackSquare Λ sqZ.toCommSq).symm.app
              ((openExtension Λ j.left).obj N.obj))
    refine ⟨(CondensedRing.openImmersionLowerShriek Λ jp.left).bounded_mapDerivedCategory_obj
        ((CondensedRing.upperStar Λ hU.left).bounded_mapDerivedCategory_obj N.property),
      (CondensedRing.upperStar Λ h.left).bounded_mapDerivedCategory_obj
        ((CondensedRing.openImmersionLowerShriek Λ j.left).bounded_mapDerivedCategory_obj
          N.property), inferInstance, inferInstance, ?_, hz₁, hz₂, hz₁.eq_of_src _ _⟩
    exact open_mate_unit _ _ _ _
  · intro N
    have hz₁ := ((pullback Λ hU.left).map_isZero
      (mixed_closed_zero Λ i.left j.left
        (by rw [hcomp]; exact disjoint_compl_left) N.obj)).of_iso
          ((pullbackSquare Λ sqU.toCommSq).symm.app
            ((closedDirectImage Λ i.left).obj N.obj))
    have hz₂ := mixed_closed_zero Λ ip.left jp.left
      (by rw [hcomp']; exact disjoint_compl_left) ((pullback Λ hZ.left).obj N.obj)
    refine ⟨(CondensedRing.upperStar Λ h.left).bounded_mapDerivedCategory_obj
        ((CondensedRing.lowerStar Λ i.left).bounded_mapDerivedCategory_obj N.property),
      (CondensedRing.lowerStar Λ ip.left).bounded_mapDerivedCategory_obj
        ((CondensedRing.upperStar Λ hZ.left).bounded_mapDerivedCategory_obj N.property),
      inferInstance, inferInstance, ?_, hz₁, hz₂, hz₁.eq_of_src _ _⟩
    exact closed_mate_counit _ _ _ _


/-- Locally closed base change is the composite of the open beta and the inverse closed
gamma, with a fixed open--closed factorization. The displayed equation specifies that
composite without choosing any unrelated isomorphism.
Source: blueprint `det-lem-int-tensor-pullback.proof.md`, Local models; node proof, Step 7
(blueprint: lem-sfb-integral-bounded-stratum-base-change).

Proof: Apply the preceding open result to u inside the closure and the closed result
to i, using the bounded input u_!M. Its boundedness follows from exact-functor cohomology.
First apply i'_* to beta_u,M, then compose with the inverse of gamma_i,u_!M. These maps
are natural in M; every factor is invertible, and exactness keeps both ends bounded.
The composite satisfies the displayed cancellation equation by the inverse identity.
No independence of factorization, constructibility, or derived completeness is used.
-/
theorem integral_bounded_locally_closed_base_change
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {S : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    {C : Over (Spec (.of k))}
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    {T : Over (Spec (.of k))}
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    {Sp : Over (Spec (.of k))}
    [LocallyOfFiniteType Sp.hom] [QuasiCompact Sp.hom] [IsSeparated Sp.hom]
    {Cp : Over (Spec (.of k))}
    [LocallyOfFiniteType Cp.hom] [QuasiCompact Cp.hom] [IsSeparated Cp.hom]
    {Tp : Over (Spec (.of k))}
    [LocallyOfFiniteType Tp.hom] [QuasiCompact Tp.hom] [IsSeparated Tp.hom]
    (h : Tp ⟶ T) (u₀ : S ⟶ C) (i : C ⟶ T)
    (hS : Sp ⟶ S) (up : Sp ⟶ Cp) (hC : Cp ⟶ C) (ip : Cp ⟶ Tp)
    [IsOpenImmersion u₀.left] [IsClosedImmersion i.left]
    [IsOpenImmersion up.left] [IsClosedImmersion ip.left]
    (sqU : IsPullback hS.left up.left u₀.left hC.left)
    (sqI : IsPullback hC.left ip.left i.left h.left) :
    Exists fun [_hi : PreservesFiniteColimits (CondensedRing.lowerStar (integralCoefficientRing l
            E) i.left)] ↦
    Exists fun [_hip : PreservesFiniteColimits (CondensedRing.lowerStar (integralCoefficientRing l
            E)
            ip.left)] ↦
      ∃ e : DerivedCategory.Bounded.ι ⋙
          ((pullback (integralCoefficientRing l E) hS.left) ⋙
            (openExtension (integralCoefficientRing l E) up.left) ⋙ (closedDirectImage
            (integralCoefficientRing l E) ip.left)) ≅
        DerivedCategory.Bounded.ι ⋙
          ((openExtension (integralCoefficientRing l E) u₀.left) ⋙
            (closedDirectImage (integralCoefficientRing l E) i.left) ⋙ (pullback
            (integralCoefficientRing l E) h.left)),
        ∀ M : DerivedCategory.Bounded
            (Mod (Sheaf (Scheme.ProEt.topology S.left) Ab.{u + 1})
              (condensedRingObj (integralCoefficientRing l E) S.left)),
          DerivedCategory.TStructure.t.bounded
              (((pullback (integralCoefficientRing l E) hS.left) ⋙
            (openExtension (integralCoefficientRing l E) up.left)
            ⋙ (closedDirectImage (integralCoefficientRing l E) ip.left)).obj M.obj) ∧
          DerivedCategory.TStructure.t.bounded
              (((openExtension (integralCoefficientRing l E) u₀.left) ⋙
            (closedDirectImage (integralCoefficientRing l E) i.left) ⋙
            (pullback (integralCoefficientRing l E) h.left)).obj M.obj) ∧
          e.hom.app M ≫
              (closedMate (integralCoefficientRing l E) sqI.toCommSq).app
            ((openExtension (integralCoefficientRing l E) u₀.left).obj M.obj) =
            (closedDirectImage (integralCoefficientRing l E) ip.left).map
            ((openMate
            (integralCoefficientRing l
            E) sqU.toCommSq).app M.obj) := by
  let Λ := integralCoefficientRing l E
  have : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  have : IsLocallyNoetherian Tp.left := LocallyOfFiniteType.isLocallyNoetherian Tp.hom
  obtain ⟨hi, hip, hγ⟩ := closed_square_iso Λ sqI
  have hβ := open_mate_iso Λ sqU
  let β := asIso (openMate Λ sqU.toCommSq)
  let γ := asIso (closedMate Λ sqI.toCommSq)
  let e₀ :
      (pullback Λ hS.left) ⋙ (openExtension Λ up.left) ⋙ (closedDirectImage Λ ip.left) ≅
        (openExtension Λ u₀.left) ⋙ (closedDirectImage Λ i.left) ⋙ (pullback Λ h.left) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight β _ ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ γ.symm
  refine ⟨hi, hip, Functor.isoWhiskerLeft DerivedCategory.Bounded.ι e₀, ?_⟩
  intro M
  refine ⟨(CondensedRing.lowerStar Λ ip.left).bounded_mapDerivedCategory_obj
      ((CondensedRing.openImmersionLowerShriek Λ up.left).bounded_mapDerivedCategory_obj
        ((CondensedRing.upperStar Λ hS.left).bounded_mapDerivedCategory_obj M.property)),
    (CondensedRing.upperStar Λ h.left).bounded_mapDerivedCategory_obj
      ((CondensedRing.lowerStar Λ i.left).bounded_mapDerivedCategory_obj
        ((CondensedRing.openImmersionLowerShriek Λ u₀.left).bounded_mapDerivedCategory_obj
          M.property)), ?_⟩
  dsimp [e₀, β, γ, Λ]
  simp only [Category.id_comp]
  simp only [NatIso.isIso_inv_app, Category.assoc, IsIso.inv_hom_id, Category.comp_id]


end AlgebraicGeometry.ProEtale.IntegralBoundedStratumBaseChange
