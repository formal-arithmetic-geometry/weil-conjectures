/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.ConstructibleExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.SixFunctors.CartesianOpenAdjunctionRestriction
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Mathlib.CategoryTheory.Adjunction.Mates
import all Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
import all Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport
import all Sheaf.AlgebraicGeometry.FixSiteOpenExchangeSheaf
import all Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison

/-! # Finite isomorphism exchange and the specified mates

Source: current Weil blueprint, prop-pur-weil-equivariance-compatibilities.proof.md,
constituent-compatibility assembly; Stacks Tags 09A5, 07A7, 0D6D and 03DI
(blueprint: lem-pur-isomorphism-finite-mate-normalization).

The proper reindexing map is the published sectionwise fibre-product comparison
`sfProperOpenDerivedRestriction`. The open reindexing map is constructed from the
same section comparison by uniqueness of left adjoints, then descended termwise.
The statement identifies these concrete maps with the specified proper/open mates.
-/

@[expose] public noncomputable section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] sfIntrinsicModuleEquivalence sfIntrinsicDirectImageComparison

/-- Forget only the chosen Cartesian identification, retaining its projection equations.
Source: Stacks Tag 09A5, Cartesian reindexing
(blueprint: lem-pur-isomorphism-finite-mate-normalization). -/
abbrev finiteMateCartesian {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) : IsPullback g' f' f g :=
  IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd

/-- The ordinary open reindexing isomorphism. Its right-adjoint comparison is the
canonical identification of sections on the two fibre products, not a chosen map.
When the horizontal maps are isomorphisms this is reindexing the zero-extension
presheaf: it keeps a section over the open and the zero section off the open.
Source: Stacks Tags 09A5 and 03DI, constituent-compatibility assembly
(blueprint: lem-pur-isomorphism-finite-mate-normalization). -/
def finiteMateOpenReindexing (A : Type u) [CommRing A] [Finite A]
    {U' U V' V : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ V')
    (j : U ⟶ V) (b : V' ⟶ V) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j b) :
    sfIntrinsicExtensionByZero j A ⋙ sfIntrinsicPullback A b ≅
      sfIntrinsicPullback A h ⋙ sfIntrinsicExtensionByZero j' A :=
  (((sfIntrinsicOpenAdjunction A j).comp (sfIntrinsicConstantModuleAdjunction b A)).ofNatIsoRight
    (sfProperOpenPullbackRestriction A h j' j b sq)).leftAdjointUniq
      ((sfIntrinsicConstantModuleAdjunction h A).comp (sfIntrinsicOpenAdjunction A j'))

/-- Apply the section-normalized open reindexing isomorphism termwise to unbounded
complexes and localize. All functors here are the published exact functors.
Source: Stacks Tags 03DJ and 05RU, constituent-compatibility assembly
(blueprint: lem-pur-isomorphism-finite-mate-normalization). -/
def finiteMateDerivedOpenReindexing (A : Type u) [CommRing A] [Finite A]
    {U' U V' V : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ V')
    (j : U ⟶ V) (b : V' ⟶ V) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j b) :
    sfIntrinsicDerivedOpen A j ⋙ sfIntrinsicDerivedPullback A b ≅
      sfIntrinsicDerivedPullback A h ⋙ sfIntrinsicDerivedOpen A j' :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (finiteMateOpenReindexing A h j' j b sq) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

attribute [local irreducible] finiteMateOpenReindexing finiteMateDerivedOpenReindexing

private theorem mate_change_right
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R S : D ⥤ C} {L' : E ⥤ F} {R' S' : F ⥤ E}
    (a : L ⊣ R) (a' : L' ⊣ R') (e : R ≅ S) (e' : R' ≅ S')
    {G : C ⥤ E} {H : D ⥤ F} (t : G ⋙ L' ⟶ L ⋙ H) :
    (mateEquiv (a.ofNatIsoRight e) (a'.ofNatIsoRight e')
      (TwoSquare.mk _ _ _ _ t)).natTrans =
      whiskerRight e.inv G ≫ (mateEquiv a a' (TwoSquare.mk _ _ _ _ t)).natTrans ≫
        whiskerLeft H e'.hom := by
  ext X
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoRight_counit,
    Functor.map_comp, Category.assoc]
  dsimp only [TwoSquare.natTrans, TwoSquare.mk, Functor.comp_obj, Functor.comp_map]
  simp only [Category.id_comp]
  rw [← e'.hom.naturality_assoc]
  rw [← e'.hom.naturality_assoc]
  rw [← e'.hom.naturality_assoc]
  rw [← R'.map_comp_assoc]
  erw [← t.naturality]
  rw [R'.map_comp_assoc]
  erw [← a'.unit.naturality_assoc]
  simp only [Functor.id_map, Functor.id_obj, Category.comp_id, Category.id_comp]

private theorem proper_underived (A : Type u) [CommRing A] [Finite A]
    {U V W T : Scheme.{u}} (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    (mateEquiv (sfIntrinsicConstantModuleAdjunction p A)
      (sfIntrinsicConstantModuleAdjunction r A)
      (TwoSquare.mk _ _ _ _ (sfIntrinsicSquarePullback A r k i p sq.w).hom)).natTrans =
      (sfProperOpenPullbackRestriction A r k i p sq).hom := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let ap := ProEtale.upperStarLowerStarAdjunction B p
  let ar := ProEtale.upperStarLowerStarAdjunction B r
  have ht := trMate (sfIntrinsicModuleEquivalence T A) (sfIntrinsicModuleEquivalence V A)
    (sfIntrinsicModuleEquivalence W A) (sfIntrinsicModuleEquivalence U A)
    ap ar (ProEtale.upperStar B i) (ProEtale.upperStar B k)
    (ProEtale.baseChangeMap B sq.toCommSq)
  have hraw : ((mateEquiv ap ar).symm
      (TwoSquare.mk _ _ _ _ (ProEtale.baseChangeMap B sq.toCommSq))).natTrans =
      (ProEtale.upperStarCompIso B sq.w).hom := by
    rw [ProEtale.pro_baseChange_eq_mate]
    exact congrArg TwoSquare.natTrans ((mateEquiv ap ar).symm_apply_apply _)
  rw [hraw] at ht
  have hm : (mateEquiv
      (trAdj (sfIntrinsicModuleEquivalence T A) (sfIntrinsicModuleEquivalence V A) ap)
      (trAdj (sfIntrinsicModuleEquivalence W A) (sfIntrinsicModuleEquivalence U A) ar)
      (TwoSquare.mk _ _ _ _ (sfIntrinsicSquarePullback A r k i p sq.w).hom)).natTrans =
      (sfIntrinsicTransportComp A (ProEtale.lowerStar B p) (ProEtale.upperStar B i)).inv ≫
        trNat (sfIntrinsicModuleEquivalence V A) (sfIntrinsicModuleEquivalence W A)
          (ProEtale.baseChangeMap B sq.toCommSq) ≫
        (sfIntrinsicTransportComp A (ProEtale.upperStar B k) (ProEtale.lowerStar B r)).hom := by
    apply congrArg TwoSquare.natTrans
    apply (Equiv.eq_symm_apply _).mp
    apply congrArg (TwoSquare.mk _ _ _ _)
    simpa only [sfSquare_transport, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      trComp, trNat, trFunctor, sfIntrinsicPullback, sfIntrinsicTransport,
      sfIntrinsicTransportComp, sfIntrinsicTransportIso, B, TwoSquare.mk, TwoSquare.natTrans,
      isoWhiskerLeft_hom, isoWhiskerRight_hom] using
      ht.symm
  rw [sfIntrinsicConstantModuleAdjunction, sfIntrinsicConstantModuleAdjunction,
    mate_change_right]
  change whiskerRight (sfProperOpenDirectImageCoordinates A p).hom _ ≫
    (mateEquiv _ _ _).natTrans ≫
      whiskerLeft _ (sfProperOpenDirectImageCoordinates A r).inv = _
  dsimp only [trAdj, ap, ar] at hm
  erw [hm]
  rw [← fixed_restriction_eq_baseChange A r k i p sq]
  simp only [sfProperOpenPullbackRestriction, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, Category.assoc,
    sfIntrinsicTransportIso, trNat, fixed_restriction]
  rfl

private theorem leftUniq_inv
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R') (e : R ≅ R') :
    ((a.ofNatIsoRight e).leftAdjointUniq a').inv = (conjugateEquiv a a').symm e.hom := by
  ext X
  rw [Adjunction.leftAdjointUniq_inv_app]
  apply (a'.homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
  change a.unit.app X ≫ e.hom.app (L.obj X) = _
  exact unit_conjugateEquiv_symm a a' e.hom X

private theorem open_underived (A : Type u) [CommRing A] [Finite A]
    {U' U V' V : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ V')
    (j : U ⟶ V) (b : V' ⟶ V) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j b) :
    (finiteMateOpenReindexing A h j' j b sq).inv =
      sfIntrinsicOpenMate A h j' j b sq.w := by
  rw [finiteMateOpenReindexing, leftUniq_inv]
  apply (conjugateEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  have hi := iterated_mateEquiv_conjugateEquiv
    (sfIntrinsicOpenAdjunction A j) (sfIntrinsicOpenAdjunction A j')
    (sfIntrinsicConstantModuleAdjunction h A) (sfIntrinsicConstantModuleAdjunction b A)
    (TwoSquare.mk _ _ _ _ (sfIntrinsicOpenMate A h j' j b sq.w))
  rw [sfOpenMate_mate] at hi
  rw [proper_underived A h j' j b sq] at hi
  exact hi

private theorem proper_derived (A : Type u) [CommRing A] [Finite A]
    {U V W T : Scheme.{u}} (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    (mateEquiv (sfCartesianOpenPullPushAdjunction A p)
      (sfCartesianOpenPullPushAdjunction A r)
      (TwoSquare.mk _ _ _ _ (sfIntrinsicDerivedSquarePullback A r k i p sq.w).hom)
      ).natTrans = (sfProperOpenDerivedRestriction A r k i p sq).hom := by
  rw [intrinsic_restriction_eq_square]
  change (mateEquiv
    (sfIntrinsicConstantModuleAdjunction p A).mapDerivedCategoryRightDerivedAdjunction
    (sfIntrinsicConstantModuleAdjunction r A).mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (sfIntrinsicDerivedSquarePullback A r k i p sq.w).hom)
    ).natTrans = _
  have hd := Etale.derived_mate_exact_eq_square
    (sfIntrinsicConstantModuleAdjunction p A) (sfIntrinsicConstantModuleAdjunction r A)
    (sfIntrinsicSquarePullback A r k i p sq.w)
  change _ = _ at hd
  exact hd.trans (congrArg Etale.derivedSquare (proper_underived A r k i p sq))

private theorem open_derived (A : Type u) [CommRing A] [Finite A]
    {U' U V' V : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ V')
    (j : U ⟶ V) (b : V' ⟶ V) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j b) :
    (finiteMateDerivedOpenReindexing A h j' j b sq).inv =
      sfIntrinsicDerivedOpenMate A h j' j b sq.w := by
  unfold finiteMateDerivedOpenReindexing sfIntrinsicDerivedOpenMate
  simp only [Iso.trans_inv, Iso.symm_inv]
  have hd : (Functor.mapDerivedCategoryNatIso (finiteMateOpenReindexing A h j' j b sq)).inv =
      sfIntrinsicDeriveMap A (finiteMateOpenReindexing A h j' j b sq).inv := by
    rw [← mapDerivedCategoryNatIso_symm]
    exact (dMap_iso (finiteMateOpenReindexing A h j' j b sq).symm).symm
  rw [hd, open_underived, Category.assoc]

private theorem unit_of_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (a' : L' ⊣ R') {G : C ⥤ E} {H : D ⥤ F}
    (α : G ⋙ L' ⟶ L ⋙ H) (τ : R ⋙ G ⟶ H ⋙ R')
    (ht : (mateEquiv a a' (TwoSquare.mk _ _ _ _ α)).natTrans = τ) (X : C) :
    a'.unit.app (G.obj X) ≫ R'.map (α.app X) =
      G.map (a.unit.app X) ≫ τ.app (L.obj X) := by
  have hu := unit_mateEquiv a a' (TwoSquare.mk _ _ _ _ α) X
  change mateEquiv a a' (TwoSquare.mk _ _ _ _ α) = TwoSquare.mk _ _ _ _ τ at ht
  rw [ht] at hu
  simpa only [TwoSquare.mk, TwoSquare.natTrans, Functor.comp_obj, Functor.id_obj] using hu.symm

private theorem localized_adjunct
    {C₁ D₁ C₂ D₂ : Type*}
    [Category C₁] [Category D₁] [Category C₂] [Category D₂]
    [Abelian C₁] [Abelian D₁] [Abelian C₂] [Abelian D₂]
    [HasDerivedCategory C₁] [HasDerivedCategory D₁]
    [HasDerivedCategory C₂] [HasDerivedCategory D₂]
    {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (ad₁ : L₁.mapDerivedCategory ⊣ R₁.mapDerivedCategory)
    (ad₂ : L₂.mapDerivedCategory ⊣ R₂.mapDerivedCategory)
    (he₁ : ad₁ = exactAdj a₁) (he₂ : ad₂ = exactAdj a₂)
    (u : C₁ ⥤ C₂) (v : D₁ ⥤ D₂)
    [u.Additive] [v.Additive]
    [PreservesFiniteLimits u] [PreservesFiniteColimits u]
    [PreservesFiniteLimits v] [PreservesFiniteColimits v]
    (τ : R₁ ⋙ u ≅ v ⋙ R₂) (β : u ⋙ L₂ ≅ L₁ ⋙ v)
    (hβ : ∀ M, a₂.unit.app (u.obj M) ≫ R₂.map (β.hom.app M) =
      u.map (a₁.unit.app M) ≫ τ.hom.app (L₁.obj M))
    (K : DerivedCategory C₁) :
    (mapDerivedCategorySquareIso β).hom.app K =
      (ad₂.homEquiv _ _).symm
        (u.mapDerivedCategory.map (ad₁.unit.app K) ≫
          (mapDerivedCategorySquareIso τ).hom.app (L₁.mapDerivedCategory.obj K)) := by
  subst ad₁ ad₂
  apply ((exactAdj a₂).homEquiv _ _).injective
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact exact_unit_square a₁ a₂ (exactAdj a₁) (exactAdj a₂)
    (exactAdj_unit_Qh a₁) (exactAdj_unit_Qh a₂) u v τ β hβ K

private theorem openAdj_eq_exact (A : Type u) [CommRing A] [Finite A]
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    exceptionalOpenAdjunction j A = exactAdj (sfIntrinsicOpenAdjunction A j) := rfl

attribute [local irreducible] sfIntrinsicOpenAdjunction sfIntrinsicExtensionByZero
  sfIntrinsicPullback sfIntrinsicSquarePullback sfIntrinsicOpenMate exceptionalOpenAdjunction

private theorem open_adjunct (A : Type u) [CommRing A] [Finite A]
    {U' U V' V : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ V')
    (j : U ⟶ V) (b : V' ⟶ V) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j b) (K : proEtaleDerivedCategory U A) :
    (finiteMateDerivedOpenReindexing A h j' j b sq).inv.app K =
      ((exceptionalOpenAdjunction j' A).homEquiv _ _).symm
        ((sfIntrinsicDerivedPullback A h).map
          ((exceptionalOpenAdjunction j A).unit.app K) ≫
        (sfIntrinsicDerivedSquarePullback A h j' j b sq.w).hom.app
          ((sfIntrinsicDerivedOpen A j).obj K)) := by
  have hb : ∀ M, (sfIntrinsicOpenAdjunction A j').unit.app
      ((sfIntrinsicPullback A h).obj M) ≫
        (sfIntrinsicPullback A j').map
          ((finiteMateOpenReindexing A h j' j b sq).inv.app M) =
      (sfIntrinsicPullback A h).map ((sfIntrinsicOpenAdjunction A j).unit.app M) ≫
        (sfIntrinsicSquarePullback A h j' j b sq.w).hom.app
          ((sfIntrinsicExtensionByZero j A).obj M) := by
    intro M
    rw [open_underived]
    exact unit_of_mate (sfIntrinsicOpenAdjunction A j) (sfIntrinsicOpenAdjunction A j')
      (sfIntrinsicOpenMate A h j' j b sq.w) (sfIntrinsicSquarePullback A h j' j b sq.w).hom
      (sfOpenMate_mate A h j' j b sq.w) M
  have hu := localized_adjunct (sfIntrinsicOpenAdjunction A j)
    (sfIntrinsicOpenAdjunction A j')
    (exceptionalOpenAdjunction j A) (exceptionalOpenAdjunction j' A)
    (openAdj_eq_exact A j) (openAdj_eq_exact A j')
    (sfIntrinsicPullback A h) (sfIntrinsicPullback A b)
    (sfIntrinsicSquarePullback A h j' j b sq.w)
    (finiteMateOpenReindexing A h j' j b sq).symm hb K
  simpa only [finiteMateDerivedOpenReindexing, mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    mapDerivedCategoryNatIso_symm, Category.assoc, sfIntrinsicDerivedSquarePullback,
    sfIntrinsicDerivedPullback, sfIntrinsicDerivedOpen] using hu

/-- Finite reindexing identifies the actual proper mate, its counit transpose, the
actual open comparison with its open-unit inverse transpose, and the ordered
compactification exchange. The two chosen Cartesian squares express that `c'` is
the base change of `c`; no linearity of the horizontal isomorphisms is required.
The proper comparison is defined by `sfProperOpenPullbackRestriction` on ordinary
sheaves and by its K-injective derivation `sfProperOpenDerivedRestriction`.
In fixed-scalar coordinates its section map is exactly
`sfProperOpenFixedRestrictionIso`: evaluation on the canonical fibre-product map.
For isomorphisms, `openImmersionRestriction` is the site postcomposition functor
`isoSectionwiseInverseImage`, so these are the reindexing comparisons of the node.
Source: current blueprint prop-pur-weil-equivariance-compatibilities.proof.md,
constituent-compatibility assembly; Stacks Tags 09A5, 07A7, 0D6D, 03DI and 03DJ
(blueprint: lem-pur-isomorphism-finite-mate-normalization).

Proof. Transport the fixed-scalar base-change mate through the canonical module
equivalences, accounting for the specified direct-image coordinates. The fixed
section restriction is that base-change map. Compatibility of exact localization
with right-derived adjunction mates identifies its derived restriction, and the
mate counit identity gives the second clause. Iterating mates identifies the
ordinary inverse open reindexing with the open mate, by uniqueness of left
adjoints. Exact localization preserves this identity and its unit equation,
giving the third and fourth clauses. Substitute the proper identity into the
ordered compactification exchange; its associators are identities. The final
section formula is the definition of the fixed restriction. -/
theorem isomorphismFiniteMateNormalization (P : PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (f' : X' ⟶ Y') (g : Y' ≅ Y) (g' : X' ≅ X)
    (c : Compactification f) (c' : Compactification f') (b : c'.Z ≅ c.Z)
    (sqP : ChosenCartesianSquare b.hom c'.g c.g g.hom)
    (sqJ : ChosenCartesianSquare g'.hom c'.i c.i b.hom) :
    (mateEquiv (sfCartesianOpenPullPushAdjunction P.Ring c.g)
      (sfCartesianOpenPullPushAdjunction P.Ring c'.g)
      (TwoSquare.mk _ _ _ _
        (sfIntrinsicDerivedSquarePullback P.Ring c'.g b.hom g.hom c.g sqP.w.symm).hom)
        ).natTrans =
      (sfProperOpenDerivedRestriction P.Ring c'.g b.hom g.hom c.g
        (finiteMateCartesian sqP).flip).hom ∧
    (∀ M : proEtaleDerivedCategory c.Z P.Ring,
      (sfIntrinsicDerivedPullback P.Ring c'.g).map
          ((sfProperOpenDerivedRestriction P.Ring c'.g b.hom g.hom c.g
            (finiteMateCartesian sqP).flip).hom.app M) ≫
        (sfCartesianOpenPullPushAdjunction P.Ring c'.g).counit.app
          ((sfIntrinsicDerivedPullback P.Ring b.hom).obj M) =
      (sfIntrinsicDerivedSquarePullback P.Ring c'.g b.hom g.hom c.g sqP.w.symm).hom.app
          ((proEtaleConstantDerivedDirectImage c.g P.Ring).obj M) ≫
        (sfIntrinsicDerivedPullback P.Ring b.hom).map
          ((sfCartesianOpenPullPushAdjunction P.Ring c.g).counit.app M)) ∧
    (finiteMateDerivedOpenReindexing P.Ring g'.hom c'.i c.i b.hom
        (finiteMateCartesian sqJ)).inv =
      sfIntrinsicDerivedOpenMate P.Ring g'.hom c'.i c.i b.hom sqJ.w ∧
    (∀ K : proEtaleDerivedCategory X P.Ring,
      (finiteMateDerivedOpenReindexing P.Ring g'.hom c'.i c.i b.hom
        (finiteMateCartesian sqJ)).inv.app K =
      ((exceptionalOpenAdjunction c'.i P.Ring).homEquiv _ _).symm
        ((sfIntrinsicDerivedPullback P.Ring g'.hom).map
            ((exceptionalOpenAdjunction c.i P.Ring).unit.app K) ≫
          (sfIntrinsicDerivedSquarePullback P.Ring g'.hom c'.i c.i b.hom sqJ.w).hom.app
            ((sfIntrinsicDerivedOpen P.Ring c.i).obj K))) ∧
    (∀ K : proEtaleDerivedCategory X P.Ring,
      (CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
        (sfIntrinsicDerivedOpen P.Ring c.i) (sfIntrinsicDerivedOpen P.Ring c'.i)
        (sfIntrinsicDerivedPullback P.Ring c.g)
        (proEtaleConstantDerivedDirectImage c.g P.Ring)
        (sfCartesianOpenPullPushAdjunction P.Ring c.g)
        (sfIntrinsicDerivedPullback P.Ring c'.g)
        (proEtaleConstantDerivedDirectImage c'.g P.Ring)
        (sfCartesianOpenPullPushAdjunction P.Ring c'.g)
        (sfIntrinsicDerivedPullback P.Ring g.hom)
        (sfIntrinsicDerivedPullback P.Ring g'.hom)
        (sfIntrinsicDerivedPullback P.Ring b.hom)
        (sfIntrinsicDerivedSquarePullback P.Ring c'.g b.hom g.hom c.g sqP.w.symm)
        (finiteMateDerivedOpenReindexing P.Ring g'.hom c'.i c.i b.hom
          (finiteMateCartesian sqJ))).app K =
      (sfProperOpenDerivedRestriction P.Ring c'.g b.hom g.hom c.g
          (finiteMateCartesian sqP).flip).hom.app ((sfIntrinsicDerivedOpen P.Ring c.i).obj K) ≫
        (proEtaleConstantDerivedDirectImage c'.g P.Ring).map
          ((finiteMateDerivedOpenReindexing P.Ring g'.hom c'.i c.i b.hom
            (finiteMateCartesian sqJ)).hom.app K)) ∧
    (∀ (F : Sheaf (Scheme.ProEt.topology c.Z)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} P.Ring))) (V : Y'.ProEt),
      ((sfProperOpenFixedRestrictionIso P.Ring c'.g b.hom g.hom c.g
          (finiteMateCartesian sqP).flip).hom.app F).hom.app (Opposite.op V) =
        F.obj.map ((MorphismProperty.Over.pullbackMapComparison
          (inferInstance : WeaklyEtale g.hom) (inferInstance : WeaklyEtale b.hom)
          (finiteMateCartesian sqP).flip.toCommSq).app V).op) := by
  have hproper : (mateEquiv (sfCartesianOpenPullPushAdjunction P.Ring c.g)
      (sfCartesianOpenPullPushAdjunction P.Ring c'.g)
      (TwoSquare.mk _ _ _ _
        (sfIntrinsicDerivedSquarePullback P.Ring c'.g b.hom g.hom c.g sqP.w.symm).hom)
        ).natTrans =
      (sfProperOpenDerivedRestriction P.Ring c'.g b.hom g.hom c.g
        (finiteMateCartesian sqP).flip).hom := by
    exact proper_derived P.Ring c'.g b.hom g.hom c.g (finiteMateCartesian sqP).flip
  have hopen : (finiteMateDerivedOpenReindexing P.Ring g'.hom c'.i c.i b.hom
      (finiteMateCartesian sqJ)).inv =
      sfIntrinsicDerivedOpenMate P.Ring g'.hom c'.i c.i b.hom sqJ.w := by
    exact open_derived P.Ring g'.hom c'.i c.i b.hom (finiteMateCartesian sqJ)
  refine ⟨hproper, ?_, hopen, ?_, ?_, ?_⟩
  · intro M
    rw [← hproper]
    exact mateEquiv_counit _ _ _ M
  · intro K
    exact open_adjunct P.Ring g'.hom c'.i c.i b.hom (finiteMateCartesian sqJ) K
  · intro K
    simp only [SuppliedExchangeProjection.compactificationExchangeFromData,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
      Category.comp_id, hproper]
  · intro F V
    rfl

end WeilConjectures.PurityFiniteSetting
