/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Sheaf.Paper.KFlatScalarComparisonNormalization
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Sheaf.Paper.ProjectionMateExact
import all Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Sheaf.Paper.KFlatRingedToposPullback
import all Sheaf.CategoryTheory.DerivedCategory.CokernelAdjointExchange
import Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import all Sheaf.CategoryTheory.DerivedExactSquareComposition
import Sheaf.CategoryTheory.PastedMatesCounitNormalization

/-! # Transitivity of normalized scalar mates on sheaf topoi

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E, 0D6D and 07A6;
the normalized scalar-tower calculation in the DAG proof
(blueprint: lem-sfb-topos-scalar-mate-transitivity).

The geometric adjunction is derived from the ordinary module adjunction.
Coefficient adjunctions retain their scalar-insertion and K-flat normalization.
The two tower comparisons are characterized by ordinary pure tensors and the
actual universal cochain counits. No direct-image comparison is inverted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits
universe u w
open CategoryTheory CategoryTheory.Limits
open SheafOfModules.ScalarPullback

namespace SheafOfModules.ToposScalarMate

attribute [local irreducible] SheafOfModules.ScalarPullback.pure
  SheafOfModules.monoidalCategory CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors DerivedCategory.Q DerivedCategory.Qh

-- Cache these proof-valued instances used by all ring/module aliases in this file.
private theorem compose_ring {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
private theorem compose_ring_sets {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u}) :=
  inferInstance
private theorem compose_group_sets {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u} ⋙ uliftFunctor.{u, u}) :=
  inferInstance
attribute [local instance] compose_ring compose_ring_sets compose_group_sets

section Coefficients
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A B : Sheaf J CommRingCat.{u}} {a : A ⟶ B}
  [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
  [PreservesFiniteLimits (restriction a)] [PreservesFiniteColimits (restriction a)]

/-- The coefficient adjunctions with precisely the existing normalization predicate.
Source: Stacks 07A6 and 06YY
(blueprint: lem-sfb-topos-scalar-mate-transitivity). -/
structure CoefficientAdjunction (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a) where
  ordinary : m.E ⊣ restriction a
  derived : m.T ⊣ (restriction a).mapDerivedCategory
  normalized : AdjunctionNormalized m ordinary derived
end Coefficients

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isIso_mate_change
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {r : B ⥤ A} {F' : C ⥤ D} {r' : D ⥤ C}
    (d n : F ⊣ r) (d' n' : F' ⊣ r') {I : A ⥤ C} {J : B ⥤ D}
    (a : r ⋙ I ⟶ J ⋙ r') [IsIso (mate d d' a)] : IsIso (mate n n' a) := by
  let α := ((conjugateIsoEquiv n d).symm (Iso.refl r)).hom
  let β := ((conjugateIsoEquiv d' n').symm (Iso.refl r')).hom
  have he : mate n n' a = ((TwoSquare.mk _ _ _ _ (mate d d' a)).whiskerLeft α).whiskerRight β := by
    apply (mateEquiv n n').injective
    rw [mateEquiv_conjugateEquiv_vcomp n d' n']
    rw [conjugateEquiv_mateEquiv_vcomp n d d']
    simp only [α, β, conjugateIsoEquiv_symm_apply_hom, Iso.refl_hom,
      Equiv.apply_symm_apply, mate]
    ext X
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.id_app]
    erw [I.map_id, Category.id_comp, Category.comp_id]
  rw [he]
  change IsIso (Functor.whiskerLeft _ β ≫ (mate d d' a ≫ Functor.whiskerRight α _))
  infer_instance



private theorem leftAdjointUniq_comp
    {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} {R : B ⥤ A} (a : F ⊣ R) (b : G ⊣ R)
    {X : A} {Y : B} (f : G.obj X ⟶ Y) (g : F.obj X ⟶ Y)
    (h : b.homEquiv X Y f = a.homEquiv X Y g) :
    (a.leftAdjointUniq b).hom.app X ≫ f = g := by
  apply (a.homEquiv X Y).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simpa only [Adjunction.homEquiv_unit] using h

private theorem composite_homEquiv
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C} {R : B ⥤ A} {S : C ⥤ B} {T : C ⥤ A}
    (a : F ⊣ R) (b : G ⊣ S) (c : S ⋙ R ≅ T)
    {X : A} {Y : C} (f : G.obj (F.obj X) ⟶ Y) :
    ((a.comp b).ofNatIsoRight c).homEquiv X Y f =
      a.homEquiv X _ (b.homEquiv _ _ f) ≫ c.hom.app Y := by
  simp only [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  rfl

private theorem leftAdjointUniq_compIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    {R : B ⥤ A} {S : C ⥤ B} {T : C ⥤ A}
    (a : F ⊣ R) (b : G ⊣ S) (d : H ⊣ T) (c : S ⋙ R ≅ T) :
    ((a.comp b).ofNatIsoRight c).leftAdjointUniq d =
      Adjunction.leftAdjointCompIso a b d c := by
  apply Iso.ext
  ext X
  apply ((((a.comp b).ofNatIsoRight c)).homEquiv X _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit]
  rw [Adjunction.leftAdjointCompIso_hom]
  change _ = (((a.comp b).unit.app X ≫ (S ⋙ R).map
    (((conjugateEquiv d (a.comp b)).symm c.inv).app X)) ≫ _)
  rw [← unit_conjugateEquiv_symm]
  simp

private theorem comparison_comp
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    {R : B ⥤ A} {S : C ⥤ B} {T : C ⥤ A}
    {F' : A' ⥤ B'} {G' : B' ⥤ C'} {H' : A' ⥤ C'}
    {R' : B' ⥤ A'} {S' : C' ⥤ B'} {T' : C' ⥤ A'}
    (a : F ⊣ R) (b : G ⊣ S) (d : H ⊣ T)
    (a' : F' ⊣ R') (b' : G' ⊣ S') (d' : H' ⊣ T')
    (QA : A ⥤ A') (QB : B ⥤ B') (QC : C ⥤ C')
    (c : S ⋙ R ≅ T) (c' : S' ⋙ R' ≅ T') (β : F ⋙ G ≅ H)
    (kR : R ⋙ QA ≅ QB ⋙ R') (kS : S ⋙ QB ≅ QC ⋙ S')
    (kT : T ⋙ QA ≅ QC ⋙ T')
    (εF : QA ⋙ F' ⟶ F ⋙ QB) (εG : QB ⋙ G' ⟶ G ⋙ QC)
    (εH : QA ⋙ H' ⟶ H ⋙ QC)
    (hF : ∀ P Q (f : F.obj P ⟶ Q),
      a'.homEquiv _ _ (εF.app P ≫ QB.map f) =
        QA.map (a.homEquiv _ _ f) ≫ kR.hom.app Q)
    (hG : ∀ P Q (f : G.obj P ⟶ Q),
      b'.homEquiv _ _ (εG.app P ≫ QC.map f) =
        QB.map (b.homEquiv _ _ f) ≫ kS.hom.app Q)
    (hH : ∀ P Q (f : H.obj P ⟶ Q),
      d'.homEquiv _ _ (εH.app P ≫ QC.map f) =
        QA.map (d.homEquiv _ _ f) ≫ kT.hom.app Q)
    (hc : ∀ Q, kR.hom.app (S.obj Q) ≫ R'.map (kS.hom.app Q) ≫
      c'.hom.app (QC.obj Q) = QA.map (c.hom.app Q) ≫ kT.hom.app Q)
    (hβ : ∀ P, a.homEquiv _ _ (b.homEquiv _ _ (β.hom.app P)) ≫
      c.hom.app (H.obj P) = d.unit.app P) (P : A) :
    (((a'.comp b').ofNatIsoRight c').leftAdjointUniq d').hom.app (QA.obj P) ≫
        εH.app P =
      G'.map (εF.app P) ≫ εG.app (F.obj P) ≫ QC.map (β.hom.app P) := by
  apply leftAdjointUniq_comp
  have hh := hH P (H.obj P) (𝟙 _)
  rw [QC.map_id] at hh
  erw [Category.comp_id, Adjunction.homEquiv_id] at hh
  refine hh.trans ?_
  have ht := composite_homEquiv a' b' c'
    (G'.map (εF.app P) ≫ εG.app (F.obj P) ≫ QC.map (β.hom.app P))
  refine Eq.trans ?_ ht.symm
  rw [Adjunction.homEquiv_naturality_left]
  dsimp only [Functor.comp_obj]
  rw [hG]
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right, hF]
  simp only [Category.assoc]
  rw [hc, ← QA.map_comp_assoc, hβ]

private theorem transpose_from_unit
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {E : A ⥤ B} {R : B ⥤ A} {T : A' ⥤ B'} {R' : B' ⥤ A'}
    (a : E ⊣ R) (d : T ⊣ R') (QA : A ⥤ A') (QB : B ⥤ B')
    (ε : QA ⋙ T ⟶ E ⋙ QB) (k : R ⋙ QA ≅ QB ⋙ R')
    (hu : ∀ P, d.unit.app (QA.obj P) ≫ R'.map (ε.app P) ≫
      k.inv.app (E.obj P) = QA.map (a.unit.app P))
    (P : A) (Q : B) (f : E.obj P ⟶ Q) :
    d.homEquiv _ _ (ε.app P ≫ QB.map f) =
      QA.map (a.homEquiv _ _ f) ≫ k.hom.app Q := by
  rw [Adjunction.homEquiv_unit, R'.map_comp]
  apply (cancel_mono (k.inv.app Q)).1
  simp only [Category.assoc, Iso.hom_inv_id_app]
  have hn := k.inv.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [hn, reassoc_of% hu, ← QA.map_comp, Adjunction.homEquiv_unit]
  exact (Category.comp_id _).symm

private theorem cancel_balancing_square
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {A B : C} {X Y Z : D} (p : A ≅ B) (q : G.obj B ≅ X) (r : Y ≅ Z)
    (f : X ⟶ Z) (g : G.obj A ⟶ Y)
    (h : g ≫ r.hom = G.map p.hom ≫ q.hom ≫ f) :
    f ≫ r.inv = q.inv ≫ G.map p.inv ≫ g := by
  apply (cancel_epi (G.map p.hom ≫ q.hom)).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← G.map_comp_assoc, Iso.hom_inv_id, G.map_id, Category.id_comp]
  have he := congrArg (fun t ↦ t ≫ r.inv) h.symm
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he

section Geometry
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
  {V : Sheaf K (Type u) ⥤ Sheaf J (Type u)} (h : L ⊣ V)
  {AY : Sheaf J CommRingCat.{u}} {AX : Sheaf K CommRingCat.{u}}

/-- The induced module adjunction, fixed by its transpose on underlying sheaves.
Thus its right adjoint and its adjunction are geometric, rather than arbitrary lifts.
Source: Stacks 03D7 and 07A6
(blueprint: lem-sfb-topos-scalar-mate-transitivity). -/
structure GeometricAdjunction (I : InverseImage L AY AX) where
  push : Modules AX ⥤ Modules AY
  [additive : push.Additive]
  ordinary : inverseModules I ⊣ push
  underlying : push ⋙ ScalarPullback.underlying AY ≅ ScalarPullback.underlying AX ⋙ V
  normalized : ∀ (M : Modules AY) (N : Modules AX) (f : (inverseModules I).obj M ⟶ N),
    (ScalarPullback.underlying AY).map (ordinary.homEquiv M N f) ≫ underlying.hom.app N =
      h.homEquiv _ _ ((inverseUnderlying I).inv.app M ≫
        (ScalarPullback.underlying AX).map f)

attribute [instance] GeometricAdjunction.additive

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{w} (Modules AY)] [HasDerivedCategory.{w} (Modules AX)]
  {I : InverseImage L AY AX} [(inverseModules I).Additive]
  [PreservesFiniteLimits (inverseModules I)] [PreservesFiniteColimits (inverseModules I)]
  [Abelian.HasKInjectiveResolutions (Modules AX)]

/-- The canonical unbounded geometric adjunction, with its actual derived counit.
Source: Stacks 07A6 (blueprint: lem-sfb-topos-scalar-mate-transitivity). -/
def GeometricAdjunction.derived (g : GeometricAdjunction h I) :
    (inverseModules I).mapDerivedCategory ⊣ g.push.rightDerivedFunctor :=
  g.ordinary.mapDerivedCategoryRightDerivedAdjunction
end Geometry

attribute [local irreducible] GeometricAdjunction.derived

section Tower
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R S T : Sheaf J CommRingCat.{u}} {a : R ⟶ S} {b : S ⟶ T}
  [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (Modules S)]
  [HasDerivedCategory.{w} (Modules T)]

private noncomputable def resComp {R S T : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ T) : restriction b ⋙ restriction a ≅ restriction (a ≫ b) :=
  NatIso.ofComponents (fun M ↦ {
    hom := { val := {
      app := fun U ↦ ModuleCat.ofHom
        (X := ((restriction a).obj ((restriction b).obj M)).val.obj U)
        (Y := ((restriction (a ≫ b)).obj M).val.obj U) {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      naturality := by intros; ext; rfl } }
    inv := { val := {
      app := fun U ↦ ModuleCat.ofHom
        (X := ((restriction (a ≫ b)).obj M).val.obj U)
        (Y := ((restriction a).obj ((restriction b).obj M)).val.obj U) {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      naturality := by intros; ext; rfl } }
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl
  }) (by intros; ext; rfl)


omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (Modules S)]
  [HasDerivedCategory.{w} (Modules T)] in
private theorem restriction_composition_underlying {R S T : Sheaf J CommRingCat.{u}}
    (a : R ⟶ S) (b : S ⟶ T) (M : Modules T) :
    (ScalarPullback.underlying R).map ((resComp a b).hom.app M) = 𝟙 _ := by
  rfl

@[irreducible]
private def resD (a : R ⟶ S) (b : S ⟶ T)
    [PreservesFiniteLimits (restriction a)] [PreservesFiniteColimits (restriction a)]
    [PreservesFiniteLimits (restriction b)] [PreservesFiniteColimits (restriction b)]
    [PreservesFiniteLimits (restriction (a ≫ b))]
    [PreservesFiniteColimits (restriction (a ≫ b))] :
    (restriction b).mapDerivedCategory ⋙ (restriction a).mapDerivedCategory ≅
      (restriction (a ≫ b)).mapDerivedCategory :=
  compositionDerived _ _ _ (resComp a b)

private theorem normalized_unit_all
    (ma : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    [PreservesFiniteLimits (restriction a)] [PreservesFiniteColimits (restriction a)]
    (na : CoefficientAdjunction ma) (P : CochainComplex (Modules R) ℤ) :
    na.derived.unit.app (DerivedCategory.Q.obj P) ≫
      (restriction a).mapDerivedCategory.map (ma.ε.app P) ≫
      (restriction a).mapDerivedCategoryFactors.hom.app
        ((ma.E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((na.ordinary.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  apply unit_all ma.E (restriction a) na.ordinary ma.T na.derived ma.ε
    (fun P ↦ P.IsKFlatIndependentCoefficients ∧
      ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
  · intro K
    obtain ⟨P, p, hp, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) K
    refine ⟨P, p, ⟨hp, ?_⟩, hq⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X n)).symm (hf n)
  · intro P hp
    exact na.normalized.2 P hp.1 hp.2

@[irreducible]
private def towerOrdinary
    (ma : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    (mb : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} b)
    (mc : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} (a ≫ b))
    [PreservesFiniteLimits (restriction a)] [PreservesFiniteColimits (restriction a)]
    [PreservesFiniteLimits (restriction b)] [PreservesFiniteColimits (restriction b)]
    [PreservesFiniteLimits (restriction (a ≫ b))]
    [PreservesFiniteColimits (restriction (a ≫ b))]
    (na : CoefficientAdjunction ma) (nb : CoefficientAdjunction mb)
    (nc : CoefficientAdjunction mc) : ma.E ⋙ mb.E ≅ mc.E :=
  (((na.ordinary.comp nb.ordinary).ofNatIsoRight (resComp a b))).leftAdjointUniq nc.ordinary

@[irreducible]
private def towerDerived
    (ma : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    (mb : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} b)
    (mc : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} (a ≫ b))
    [PreservesFiniteLimits (restriction a)] [PreservesFiniteColimits (restriction a)]
    [PreservesFiniteLimits (restriction b)] [PreservesFiniteColimits (restriction b)]
    [PreservesFiniteLimits (restriction (a ≫ b))]
    [PreservesFiniteColimits (restriction (a ≫ b))]
    (na : CoefficientAdjunction ma) (nb : CoefficientAdjunction mb)
    (nc : CoefficientAdjunction mc) : ma.T ⋙ mb.T ≅ mc.T :=
  (((na.derived.comp nb.derived).ofNatIsoRight (resD a b))).leftAdjointUniq nc.derived

/-- Characterization of one tower comparison, using the existing scalar-extension models.
The forward and inverse formulas include the scalar-unit normalization. The last
square is the representative characterization of the derived comparison.
Source: Stacks 0G7E, 0D6D and 06YY
(blueprint: lem-sfb-topos-scalar-mate-transitivity). -/
def TowerNormalized
    (ma : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    (mb : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} b)
    (mc : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} (a ≫ b))
    (β₀ : ma.E ⋙ mb.E ≅ mc.E) (β : ma.T ⋙ mb.T ≅ mc.T) : Prop :=
  (∀ (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) (t : T.obj.obj U),
    ((β₀.hom.app M).val.app U) (pure mb (ma.E.obj M) U t (pure ma M U s x)) =
      pure mc M U (t * (b.hom.app U).hom s) x) ∧
  (∀ (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (t : T.obj.obj U),
    ((β₀.inv.app M).val.app U) (pure mc M U t x) =
      pure mb (ma.E.obj M) U t (pure ma M U 1 x)) ∧
  (∀ (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U),
    ((β₀.hom.app M).val.app U) (pure mb (ma.E.obj M) U 1 (pure ma M U 1 x)) =
      pure mc M U 1 x) ∧
  ∀ P : CochainComplex (Modules R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    (∀ n : ℤ, IsFlatOnSite.{u, u, u, u} (J := J) (R := R) (P.X n)) →
    IsIso (mb.ε.app ((ma.E.mapHomologicalComplex (.up ℤ)).obj P)) ∧
    β.hom.app (DerivedCategory.Q.obj P) ≫ mc.ε.app P =
      mb.T.map (ma.ε.app P) ≫ mb.ε.app ((ma.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso β₀ (.up ℤ)).hom.app P)

section TowerProof
variable
    (ma : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    (mb : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} b)
    (mc : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} (a ≫ b))
    [PreservesFiniteLimits (restriction a)] [PreservesFiniteColimits (restriction a)]
    [PreservesFiniteLimits (restriction b)] [PreservesFiniteColimits (restriction b)]
    [PreservesFiniteLimits (restriction (a ≫ b))]
    [PreservesFiniteColimits (restriction (a ≫ b))]
    (na : CoefficientAdjunction ma) (nb : CoefficientAdjunction mb)
    (nc : CoefficientAdjunction mc)

private theorem towerOrdinary_unit (M : Modules R) :
    na.ordinary.unit.app M ≫ (restriction a).map (nb.ordinary.unit.app (ma.E.obj M)) ≫
      (resComp a b).hom.app (mb.E.obj (ma.E.obj M)) ≫
      (restriction (a ≫ b)).map ((towerOrdinary ma mb mc na nb nc).hom.app M) =
      nc.ordinary.unit.app M := by
  simpa only [towerOrdinary, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Functor.comp_obj, Category.assoc] using
    Adjunction.unit_leftAdjointUniq_hom_app
      (((na.ordinary.comp nb.ordinary).ofNatIsoRight (resComp a b))) nc.ordinary M

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem towerOrdinary_hom
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) (t : T.obj.obj U) :
    ((towerOrdinary ma mb mc na nb nc).hom.app M).val.app U
      (pure mb (ma.E.obj M) U t (pure ma M U s x)) =
      pure mc M U (t * (b.hom.app U).hom s) x := by
  have hu := congrArg (fun f ↦ f.val.app U x) (towerOrdinary_unit ma mb mc na nb nc M)
  change ((towerOrdinary ma mb mc na nb nc).hom.app M).val.app U
    ((nb.ordinary.unit.app (ma.E.obj M)).val.app U
      ((na.ordinary.unit.app M).val.app U x)) = _ at hu
  simp only [na.normalized.1, nb.normalized.1] at hu
  have hs : pure mb (ma.E.obj M) U 1 (s • pure ma M U 1 x) =
      (b.hom.app U).hom s • pure mb (ma.E.obj M) U 1 (pure ma M U 1 x) := by
    have hm := ((nb.ordinary.unit.app (ma.E.obj M)).val.app U).hom.map_smul s
      (pure ma M U 1 x)
    change (nb.ordinary.unit.app (ma.E.obj M)).val.app U (s • pure ma M U 1 x) =
      (b.hom.app U).hom s •
        (show (mb.E.obj (ma.E.obj M)).val.obj U from
          (nb.ordinary.unit.app (ma.E.obj M)).val.app U (pure ma M U 1 x)) at hm
    simpa only [nb.normalized.1] using hm
  rw [ScalarPullback.pure_smul_one ma, ScalarPullback.pure_smul_one mb, hs]
  rw [((towerOrdinary ma mb mc na nb nc).hom.app M).val.app U |>.hom.map_smul,
    ((towerOrdinary ma mb mc na nb nc).hom.app M).val.app U |>.hom.map_smul, hu]
  rw [ScalarPullback.pure_smul_one, smul_smul]
  exact congrArg (fun y : (mc.E.obj M).val.obj U ↦
    (t * (b.hom.app U).hom s) • y) (nc.normalized.1 M U x)

private theorem towerOrdinary_inv
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (t : T.obj.obj U) :
    ((towerOrdinary ma mb mc na nb nc).inv.app M).val.app U (pure mc M U t x) =
      pure mb (ma.E.obj M) U t (pure ma M U 1 x) := by
  have h := congrArg (fun y ↦
    ((towerOrdinary ma mb mc na nb nc).inv.app M).val.app U y)
    (towerOrdinary_hom ma mb mc na nb nc M U x 1 t)
  simp only [map_one, mul_one] at h
  have hc := congrArg (fun f ↦ f.val.app U
    (pure mb (ma.E.obj M) U t (pure ma M U 1 x)))
    ((towerOrdinary ma mb mc na nb nc).hom_inv_id_app M)
  exact h.symm.trans hc

private theorem transpose_cochain
    (P : CochainComplex (Modules R) ℤ) (Q : CochainComplex (Modules S) ℤ)
    (f : (ma.E.mapHomologicalComplex (.up ℤ)).obj P ⟶ Q) :
    na.derived.homEquiv _ _ (ma.ε.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((na.ordinary.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        (restriction a).mapDerivedCategoryFactors.inv.app Q := by
  exact transpose_from_unit (na.ordinary.mapHomologicalComplex (.up ℤ)) na.derived
    DerivedCategory.Q DerivedCategory.Q ma.ε (restriction a).mapDerivedCategoryFactors.symm
    (normalized_unit_all ma na) P Q f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem resD_inverse_normalization (P : CochainComplex (Modules T) ℤ) :
    (restriction a).mapDerivedCategoryFactors.inv.app
        (((restriction b).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (restriction a).mapDerivedCategory.map
        ((restriction b).mapDerivedCategoryFactors.inv.app P) ≫
      (resD a b).hom.app (DerivedCategory.Q.obj P) =
    DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (resComp a b) (.up ℤ)).hom.app P) ≫
      (restriction (a ≫ b)).mapDerivedCategoryFactors.inv.app P := by
  have h := Functor.exactDerivedRestrictionComposition_inv_factors
    (restriction b) (restriction a) (restriction (a ≫ b)) (resComp a b) P
  have hc : (NatIso.mapHomologicalComplex (resComp a b) (.up ℤ)).hom.app P =
      (Functor.mapHomologicalComplexCompIso (resComp a b) (.up ℤ)).hom.app P := by
    apply HomologicalComplex.Hom.ext
    funext i
    rfl
  simpa only [resD, compositionDerived, Functor.exactDerivedRestrictionComposition, hc]
    using h

attribute [local irreducible] Adjunction.leftAdjointUniq Adjunction.ofNatIsoRight
  Adjunction.comp

private theorem towerDerived_representative (P : CochainComplex (Modules R) ℤ) :
    (towerDerived ma mb mc na nb nc).hom.app (DerivedCategory.Q.obj P) ≫ mc.ε.app P =
      mb.T.map (ma.ε.app P) ≫ mb.ε.app ((ma.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (towerOrdinary ma mb mc na nb nc) (.up ℤ)).hom.app P) := by
  rw [towerDerived]
  exact comparison_comp
    (na.ordinary.mapHomologicalComplex (.up ℤ))
    (nb.ordinary.mapHomologicalComplex (.up ℤ))
    (nc.ordinary.mapHomologicalComplex (.up ℤ))
    na.derived nb.derived nc.derived DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (Functor.mapHomologicalComplexCompIso (resComp a b) (.up ℤ)) (resD a b)
    (Functor.mapHomologicalComplexCompIso (towerOrdinary ma mb mc na nb nc) (.up ℤ))
    (restriction a).mapDerivedCategoryFactors.symm
    (restriction b).mapDerivedCategoryFactors.symm
    (restriction (a ≫ b)).mapDerivedCategoryFactors.symm
    ma.ε mb.ε mc.ε (transpose_cochain ma na) (transpose_cochain mb nb)
    (transpose_cochain mc nc)
    (fun Q ↦ resD_inverse_normalization (a := a) (b := b) Q)
    (fun P ↦ by
      apply HomologicalComplex.Hom.ext
      funext i
      change (na.ordinary.homEquiv _ _
        (nb.ordinary.homEquiv _ _ ((towerOrdinary ma mb mc na nb nc).hom.app (P.X i)))) ≫
          (resComp a b).hom.app (mc.E.obj (P.X i)) = nc.ordinary.unit.app (P.X i)
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, (restriction a).map_comp]
      simp only [Category.assoc]
      erw [(resComp a b).hom.naturality ((towerOrdinary ma mb mc na nb nc).hom.app (P.X i))]
      exact towerOrdinary_unit ma mb mc na nb nc (P.X i)) P

private theorem towerDerived_eq :
    towerDerived ma mb mc na nb nc =
      Adjunction.leftAdjointCompIso na.derived nb.derived nc.derived (resD a b) := by
  simpa only [towerDerived] using
    leftAdjointUniq_compIso na.derived nb.derived nc.derived (resD a b)

private noncomputable def identityInverse (R : Sheaf J CommRingCat.{u}) :
    AlgebraicInverseImage (𝟭 (Sheaf J (Type u))) R R where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h ↦ h
  ringMul := fun _ _ _ _ h ↦ h
  ringZero := fun _ _ h ↦ h
  ringOne := fun _ _ h ↦ h
  modules := 𝟭 (Modules R)
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h ↦ h
  moduleZero := fun _ _ _ h ↦ h
  moduleSMul := fun _ _ _ _ _ h ↦ h

private theorem tower_normalized :
    TowerNormalized ma mb mc (towerOrdinary ma mb mc na nb nc)
      (towerDerived ma mb mc na nb nc) := by
  refine ⟨towerOrdinary_hom ma mb mc na nb nc, towerOrdinary_inv ma mb mc na nb nc,
    ?_, ?_⟩
  · intro M U x
    simpa only [map_one, mul_one] using
      towerOrdinary_hom ma mb mc na nb nc M U x 1 1
  · intro P hp hf
    have h := isKFlat_ringedToposPullback (𝟭 _) (𝟭 _) Adjunction.id
      (identityInverse R) a ma.E ma.obj_eq ma.map_eq P hp hf
    exact ⟨mb.computes _ h.1, towerDerived_representative ma mb mc na nb nc P⟩

end TowerProof
end Tower

private theorem switch_iso_square
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y : A} {X' Y' : B} (c : X ≅ Y) (d : X' ≅ Y')
    (f : F.obj X ⟶ X') (g : F.obj Y ⟶ Y')
    (h : F.map c.hom ≫ g = f ≫ d.hom) :
    F.map c.inv ≫ f = g ≫ d.inv := by
  have hh := congrArg (fun k ↦ F.map c.inv ≫ k ≫ d.inv) h
  simpa only [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id,
    Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mates_of_balancing_square
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    {L₀ : A₀ ⥤ B₀} {R₀ : B₀ ⥤ A₀} (d₀ : L₀ ⊣ R₀)
    {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁} (d₁ : L₁ ⊣ R₁)
    {L₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂} (d₂ : L₂ ⊣ R₂)
    {F₀ : A₀ ⥤ A₁} {F₁ : A₁ ⥤ A₂} {F₂ : A₀ ⥤ A₂}
    {G₀ : B₀ ⥤ B₁} {G₁ : B₁ ⥤ B₂} {G₂ : B₀ ⥤ B₂}
    (βA : F₀ ⋙ F₁ ≅ F₂) (βB : G₀ ⋙ G₁ ≅ G₂)
    (c₀ : F₀ ⋙ L₁ ⟶ L₀ ⋙ G₀) (c₁ : F₁ ⋙ L₂ ⟶ L₁ ⋙ G₁)
    (c₂ : F₂ ⋙ L₂ ⟶ L₀ ⋙ G₂)
    (hc : ∀ M, L₂.map (βA.hom.app M) ≫ c₂.app M =
      c₁.app (F₀.obj M) ≫ G₁.map (c₀.app M) ≫ βB.hom.app (L₀.obj M))
    (Z : B₀) :
    βA.hom.app (R₀.obj Z) ≫ (mateEquiv d₀ d₂ c₂).app Z =
      F₁.map ((mateEquiv d₀ d₁ c₀).app Z) ≫
        (mateEquiv d₁ d₂ c₁).app (G₀.obj Z) ≫ R₂.map (βB.hom.app Z) := by
  apply (d₂.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  have hp := pasted_mates_counit_normalization d₀ d₁ d₂ c₀ c₁ Z _ _
    (𝟙 _) (βB.hom.app Z)
  simp only [Category.id_comp] at hp
  rw [hp]
  simp only [L₂.map_comp, Category.assoc]
  rw [mateEquiv_counit, ← Category.assoc, hc]
  simp only [Category.assoc, L₂.map_id, Category.id_comp]
  have hn := βB.hom.naturality (d₀.counit.app Z)
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map] at hn
  exact congrArg (fun f ↦ c₁.app (F₀.obj (R₀.obj Z)) ≫
    G₁.map (c₀.app (R₀.obj Z)) ≫ f) hn.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mate_tower_square
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    {r : B ⥤ A} {s : C ⥤ B} {t : C ⥤ A}
    {F' : A' ⥤ B'} {G' : B' ⥤ C'} {H' : A' ⥤ C'}
    {r' : B' ⥤ A'} {s' : C' ⥤ B'} {t' : C' ⥤ A'}
    (dF : F ⊣ r) (dG : G ⊣ s) (dH : H ⊣ t)
    (dF' : F' ⊣ r') (dG' : G' ⊣ s') (dH' : H' ⊣ t')
    {I : A ⥤ A'} {J : B ⥤ B'} {K : C ⥤ C'}
    (c : s ⋙ r ≅ t) (c' : s' ⋙ r' ≅ t')
    (a : r ⋙ I ⟶ J ⋙ r') (b : s ⋙ J ⟶ K ⋙ s') (e : t ⋙ I ⟶ K ⋙ t')
    (he : ∀ M, I.map (c.hom.app M) ≫ e.app M =
      a.app (s.obj M) ≫ r'.map (b.app M) ≫ c'.hom.app (K.obj M)) (M : A) :
    (Adjunction.leftAdjointCompIso dF' dG' dH' c').hom.app (I.obj M) ≫
        (mate dH dH' e).app M =
      G'.map ((mate dF dF' a).app M) ≫ (mate dG dG' b).app (F.obj M) ≫
        K.map ((Adjunction.leftAdjointCompIso dF dG dH c).hom.app M) := by
  let x : TwoSquare I (F ⋙ G) (F' ⋙ G') K :=
    TwoSquare.vComp (mate dF dF' a) (mate dG dG' b)
  let y : TwoSquare I (F ⋙ G) (F' ⋙ G') K :=
    ((TwoSquare.mk _ _ _ _ (mate dH dH' e)).whiskerLeft
      (Adjunction.leftAdjointCompIso dF dG dH c).inv).whiskerRight
        (Adjunction.leftAdjointCompIso dF' dG' dH' c').hom
  have h : x = y := by
    apply (mateEquiv (dF.comp dG) (dF'.comp dG')).injective
    dsimp only [x, y]
    rw [mateEquiv_hcomp]
    rw [mateEquiv_conjugateEquiv_vcomp (dF.comp dG) dH' (dF'.comp dG')]
    rw [conjugateEquiv_mateEquiv_vcomp (dF.comp dG) dH dH']
    simp only [mate, Equiv.apply_symm_apply,
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
      Adjunction.leftAdjointCompIso_hom, Adjunction.leftAdjointCompNatTrans,
      Equiv.apply_symm_apply, TwoSquare.mk, TwoSquare.natTrans]
    ext N
    simp only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id]
    apply (cancel_mono (c'.hom.app (K.obj N))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact (he N).symm
  have hh := congrArg (fun z ↦ z.app M) h
  dsimp only [x, y, TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app] at hh
  simp only [Category.id_comp, Category.comp_id] at hh
  apply (cancel_mono (K.map ((Adjunction.leftAdjointCompIso dF dG dH c).inv.app M))).1
  simp only [Category.assoc, ← K.map_comp, Iso.hom_inv_id_app]
  erw [K.map_id, Category.comp_id]
  exact hh.symm

section Transitivity
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {RY SY TY : Sheaf J CommRingCat.{u}} {RX SX TX : Sheaf K CommRingCat.{u}}
  (aY : RY ⟶ SY) (bY : SY ⟶ TY) (aX : RX ⟶ SX) (bX : SX ⟶ TX)
  (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (h : L ⊣ V)
  [PreservesFiniteLimits L]
  (IR : InverseImage L RY RX) (IS : InverseImage L SY SX) (IT : InverseImage L TY TX)
  [HasDerivedCategory.{w} (Modules RY)]
  [HasDerivedCategory.{w} (Modules SY)]
  [HasDerivedCategory.{w} (Modules TY)]
  [HasDerivedCategory.{w} (Modules RX)]
  [HasDerivedCategory.{w} (Modules SX)]
  [HasDerivedCategory.{w} (Modules TX)]
  [(inverseModules IR).Additive]
  [PreservesFiniteLimits (inverseModules IR)] [PreservesFiniteColimits (inverseModules IR)]
  [(inverseModules IS).Additive]
  [PreservesFiniteLimits (inverseModules IS)] [PreservesFiniteColimits (inverseModules IS)]
  [(inverseModules IT).Additive]
  [PreservesFiniteLimits (inverseModules IT)] [PreservesFiniteColimits (inverseModules IT)]
  [PreservesFiniteLimits (restriction aY)]
  [PreservesFiniteColimits (restriction aY)]
  [PreservesFiniteLimits (restriction bY)]
  [PreservesFiniteColimits (restriction bY)]
  [PreservesFiniteLimits (restriction (aY ≫ bY))]
  [PreservesFiniteColimits (restriction (aY ≫ bY))]
  [PreservesFiniteLimits (restriction aX)]
  [PreservesFiniteColimits (restriction aX)]
  [PreservesFiniteLimits (restriction bX)]
  [PreservesFiniteColimits (restriction bX)]
  [PreservesFiniteLimits (restriction (aX ≫ bX))]
  [PreservesFiniteColimits (restriction (aX ≫ bX))]
  [Abelian.HasKInjectiveResolutions (Modules RX)]
  [Abelian.HasKInjectiveResolutions (Modules SX)]
  [Abelian.HasKInjectiveResolutions (Modules TX)]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{w} (Modules RY)]
  [HasDerivedCategory.{w} (Modules SY)]
  [HasDerivedCategory.{w} (Modules TY)]
  [HasDerivedCategory.{w} (Modules RX)]
  [HasDerivedCategory.{w} (Modules SX)]
  [HasDerivedCategory.{w} (Modules TX)]
  [(inverseModules IR).Additive]
  [PreservesFiniteLimits (inverseModules IR)]
  [PreservesFiniteColimits (inverseModules IR)]
  [(inverseModules IS).Additive]
  [PreservesFiniteLimits (inverseModules IS)]
  [PreservesFiniteColimits (inverseModules IS)]
  [(inverseModules IT).Additive]
  [PreservesFiniteLimits (inverseModules IT)]
  [PreservesFiniteColimits (inverseModules IT)]
  [PreservesFiniteLimits (restriction aY)]
  [PreservesFiniteColimits (restriction aY)]
  [PreservesFiniteLimits (restriction bY)]
  [PreservesFiniteColimits (restriction bY)]
  [PreservesFiniteLimits (restriction (aY ≫ bY))]
  [PreservesFiniteColimits (restriction (aY ≫ bY))]
  [PreservesFiniteLimits (restriction aX)]
  [PreservesFiniteColimits (restriction aX)]
  [PreservesFiniteLimits (restriction bX)]
  [PreservesFiniteColimits (restriction bX)]
  [PreservesFiniteLimits (restriction (aX ≫ bX))]
  [PreservesFiniteColimits (restriction (aX ≫ bX))]
  [Abelian.HasKInjectiveResolutions (Modules RX)]
  [Abelian.HasKInjectiveResolutions (Modules SX)]
  [Abelian.HasKInjectiveResolutions (Modules TX)] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem action_tower_square
    (ha : L.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map aY) ≫
        (inverseRing IS).hom = (inverseRing IR).hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map aX)
    (hb : L.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map bY) ≫
        (inverseRing IT).hom = (inverseRing IS).hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map bX)
    (hc : L.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map (aY ≫ bY)) ≫
        (inverseRing IT).hom = (inverseRing IR).hom ≫
        (sheafCompose K
          (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map (aX ≫ bX))
    (M : Modules TY) :
    (inverseModules IR).map ((resComp aY bY).hom.app M) ≫
        (a_h IR IT hc inferInstance).hom.app M =
      (a_h IR IS ha inferInstance).hom.app ((restriction bY).obj M) ≫
        (restriction aX).map ((a_h IS IT hb inferInstance).hom.app M) ≫
        (resComp aX bX).hom.app ((inverseModules IT).obj M) := by
  apply (ScalarPullback.underlying RX).map_injective
  have hs {AY BY : Sheaf J CommRingCat.{u}} {AX BX : Sheaf K CommRingCat.{u}}
      {fY : AY ⟶ BY} {fX : AX ⟶ BX}
      (IA : InverseImage L AY AX) (IB : InverseImage L BY BX)
      (hh : L.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map fY) ≫
          (inverseRing IB).hom = (inverseRing IA).hom ≫
          (sheafCompose K
            (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map fX)
      (N : Modules BY) :
      (ScalarPullback.underlying AX).map ((a_h IA IB hh inferInstance).hom.app N) =
        (inverseUnderlying IA).hom.app ((restriction fY).obj N) ≫
          (inverseUnderlying IB).inv.app N := by
    ext U x
    exact congrArg ULift.up (a_h_spec IA IB hh inferInstance N U x.down)
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, hs, hs]
  change _ = _ ≫ (ScalarPullback.underlying SX).map ((a_h IS IT hb inferInstance).hom.app M) ≫ 𝟙 _
  rw [hs, Category.comp_id]
  have hn := (inverseUnderlying IR).hom.naturality ((resComp aY bY).hom.app M)
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc, hn]
  change (inverseUnderlying IR).hom.app
      ((restriction aY).obj ((restriction bY).obj M)) ≫ L.map (𝟙 _) ≫
      (inverseUnderlying IT).inv.app M = _
  rw [L.map_id]
  erw [Category.id_comp]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]


attribute [local irreducible] SheafOfModules.restrictScalars
  resComp

omit [Abelian.HasKInjectiveResolutions (Modules RX)]
  [Abelian.HasKInjectiveResolutions (Modules SX)]
  [Abelian.HasKInjectiveResolutions (Modules TX)] in
private theorem action_derived_tower_square
    (ha : L.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map aY) ≫
        (inverseRing IS).hom = (inverseRing IR).hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map aX)
    (hb : L.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map bY) ≫
        (inverseRing IT).hom = (inverseRing IS).hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map bX)
    (hc : L.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map (aY ≫ bY)) ≫
        (inverseRing IT).hom = (inverseRing IR).hom ≫
        (sheafCompose K
          (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map (aX ≫ bX))
    (M : DerivedCategory (Modules TY)) :
    (inverseModules IR).mapDerivedCategory.map ((resD aY bY).hom.app M) ≫
        (aD_h IR IT hc inferInstance).hom.app M =
      (aD_h IR IS ha inferInstance).hom.app ((restriction bY).mapDerivedCategory.obj M) ≫
        (restriction aX).mapDerivedCategory.map
          ((aD_h IS IT hb inferInstance).hom.app M) ≫
        (resD aX bX).hom.app ((inverseModules IT).mapDerivedCategory.obj M) := by
  have hi (N : Modules TY) :
      (inverseModules IR).map ((resComp aY bY).inv.app N) ≫
          (a_h IR IS ha inferInstance).hom.app ((restriction bY).obj N) ≫
          (restriction aX).map ((a_h IS IT hb inferInstance).hom.app N) =
        (a_h IR IT hc inferInstance).hom.app N ≫
          (resComp aX bX).inv.app ((inverseModules IT).obj N) := by
    simpa only [Category.assoc, Iso.app_hom, Iso.app_inv] using
      switch_iso_square (inverseModules IR)
      ((resComp aY bY).app N) ((resComp aX bX).app ((inverseModules IT).obj N))
      ((a_h IR IS ha inferInstance).hom.app ((restriction bY).obj N) ≫
        (restriction aX).map ((a_h IS IT hb inferInstance).hom.app N))
      ((a_h IR IT hc inferInstance).hom.app N)
      (by simpa only [Category.assoc, Iso.app_hom, Iso.app_inv] using
        action_tower_square aY bY aX bX L IR IS IT ha hb hc N)
  have hd := Functor.exactSquare_comp_forward
    (restriction bY) (restriction aY) (restriction (aY ≫ bY))
    (restriction bX) (restriction aX) (restriction (aX ≫ bX))
    (inverseModules IT) (inverseModules IS) (inverseModules IR)
    (a_h IS IT hb inferInstance) (a_h IR IS ha inferInstance)
    (a_h IR IT hc inferInstance) (resComp aY bY).symm (resComp aX bX).symm hi M
  have heY :
      (Functor.mapDerivedCategoryNatIso (resComp aY bY).symm ≪≫
        Functor.mapDerivedCategoryCompIso (restriction bY) (restriction aY)).hom =
      (resD aY bY).inv := by
    simp only [resD, compositionDerived, Iso.trans_inv, Iso.symm_inv,
      Iso.trans_hom, Functor.mapDerivedCategoryNatIso_symm]
  have heX :
      (Functor.mapDerivedCategoryNatIso (resComp aX bX).symm ≪≫
        Functor.mapDerivedCategoryCompIso (restriction bX) (restriction aX)).hom =
      (resD aX bX).inv := by
    simp only [resD, compositionDerived, Iso.trans_inv, Iso.symm_inv,
      Iso.trans_hom, Functor.mapDerivedCategoryNatIso_symm]
  rw [heY, heX] at hd
  have hh := switch_iso_square (inverseModules IR).mapDerivedCategory
    ((resD aY bY).app M).symm
    ((resD aX bX).app ((inverseModules IT).mapDerivedCategory.obj M)).symm
    ((Functor.mapDerivedCategorySquareIso (a_h IR IT hc inferInstance)).hom.app M)
    ((Functor.mapDerivedCategorySquareIso (a_h IR IS ha inferInstance)).hom.app
        ((restriction bY).mapDerivedCategory.obj M) ≫
      (restriction aX).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso (a_h IS IT hb inferInstance)).hom.app M))
    hd
  simpa only [aD_h, Functor.mapDerivedCategorySquareIso, Category.assoc,
    Iso.symm_inv, Iso.app_hom] using hh

include h in
omit [Abelian.HasKInjectiveResolutions (Modules RX)]
  [Abelian.HasKInjectiveResolutions (Modules SX)] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_mate_isIso
    (ha : L.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map aY) ≫
        (inverseRing IS).hom = (inverseRing IR).hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map aX)
    (mY : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} aY)
    (mX : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} aX)
    (nY : CoefficientAdjunction mY) (nX : CoefficientAdjunction mX) :
    IsIso (θ_h IR IS ha inferInstance nY.derived nX.derived) := by
  have hn := kflat_scalar_comparison_normalization aY aX L V h IR IS ha mY mX
  rcases hn with ⟨addR, addS, limR, colR, limS, colS, limY, colY, limX, colX, hn⟩
  rcases hn with ⟨ay, ax, dy, dx, χ, hy, hx, _, _, _, _, _, hi⟩
  rw [θ_h]
  change IsIso (mate nY.derived nX.derived (aD_h IR IS ha inferInstance).hom)
  have : IsIso (mate dy dx (aD_h IR IS ha inferInstance).hom) := by
    simpa only [θ_h] using hi
  exact isIso_mate_change dy nY.derived dx nX.derived _

/-- The canonical scalar-tower isomorphisms intertwine balancing and the specified
geometric right mates, with their scalar-unit and K-flat normalizations.

Source: Stacks 0G7E, 0D6D, 07A6 and the scalar-tower expansion of
`det-sf-comp-coherence-cocycle`, Refinement isomorphisms
(blueprint: lem-sfb-topos-scalar-mate-transitivity).

Proof:
1. Apply `lem-sfb-successive-derived-quotient-normalization` on X and Y. Commute
   the degree-zero scalar factors to the left: multiplication is t b(s), and the
   inverse inserts 1. No Koszul sign occurs. Scalar insertion is preserved.
2. On ordinary module sheaves compare the two pullback/scalar paths on generalized
   tensor generators. Both send the inverse image of t tensor s tensor x to
   t-bar b_X(s-bar) tensor x-bar. This uses the two given ring-map compatibilities
   and the balanced coequalizer comparison of
   `lem-sfb-kflat-scalar-comparison-normalization`; putting s=t=1 gives the unit clause.
3. Apply `lem-trf-ringed-kflat-word-comparison-descent` to the six ringed corners.
   A common flat-term K-flat resolution computes all words and intermediate scalar
   extensions, without flatness of a or b. Its uniqueness and pasting clauses
   descend the ordinary equality. The representative formula identifies its scalar
   associator and balancing maps with the specified ones. This gives the first square.
4. Apply `lem-sfb-pasted-mates-counit-normalization` with the three actual geometric
   adjunctions, the two balancing maps, input identity, and output beta_X. It computes
   the counit transpose of the successive right mates as the pasted balancing maps
   followed by scalar extension of the R-counit and beta_X.
5. Transpose the direct mate followed by beta_Y. Use the square of step 3 and
   naturality of beta_X at that same R-counit. Its transpose is exactly step 4.
   Injectivity of the adjunction Hom equivalence proves the second equality.
   All adjunctions are canonically derived from the normalized ordinary module
   adjunctions. No right mate, coefficient map or resolution map is inverted. -/
theorem topos_scalar_mate_transitivity
    (ha : L.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map aY) ≫
        (inverseRing IS).hom = (inverseRing IR).hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map aX)
    (hb : L.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map bY) ≫
        (inverseRing IT).hom = (inverseRing IS).hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map bX)
    (hc : L.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map (aY ≫ bY)) ≫
        (inverseRing IT).hom = (inverseRing IR).hom ≫
        (sheafCompose K
          (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map (aX ≫ bX))
    (mYa : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} aY)
    (mYb : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} bY)
    (mYc : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} (aY ≫ bY))
    (mXa : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} aX)
    (mXb : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} bX)
    (mXc : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} (aX ≫ bX))
    (nYa : CoefficientAdjunction mYa)
    (nYb : CoefficientAdjunction mYb)
    (nYc : CoefficientAdjunction mYc)
    (nXa : CoefficientAdjunction mXa)
    (nXb : CoefficientAdjunction mXb)
    (nXc : CoefficientAdjunction mXc)
    (gR : GeometricAdjunction h IR) (gS : GeometricAdjunction h IS)
    (gT : GeometricAdjunction h IT) :
    ∃ (βY₀ : mYa.E ⋙ mYb.E ≅ mYc.E) (βX₀ : mXa.E ⋙ mXb.E ≅ mXc.E)
      (βY : mYa.T ⋙ mYb.T ≅ mYc.T) (βX : mXa.T ⋙ mXb.T ≅ mXc.T)
      (balA : mYa.T ⋙ (inverseModules IS).mapDerivedCategory ≅
        (inverseModules IR).mapDerivedCategory ⋙ mXa.T)
      (balB : mYb.T ⋙ (inverseModules IT).mapDerivedCategory ≅
        (inverseModules IS).mapDerivedCategory ⋙ mXb.T)
      (balC : mYc.T ⋙ (inverseModules IT).mapDerivedCategory ≅
        (inverseModules IR).mapDerivedCategory ⋙ mXc.T),
      TowerNormalized mYa mYb mYc βY₀ βY ∧ TowerNormalized mXa mXb mXc βX₀ βX ∧
      balA.inv = θ_h IR IS ha inferInstance nYa.derived nXa.derived ∧
      balB.inv = θ_h IS IT hb inferInstance nYb.derived nXb.derived ∧
      balC.inv = θ_h IR IT hc inferInstance nYc.derived nXc.derived ∧
      (∀ M : DerivedCategory (Modules RY),
        (inverseModules IT).mapDerivedCategory.map (βY.hom.app M) ≫ balC.hom.app M =
          balB.hom.app (mYa.T.obj M) ≫
            mXb.T.map (balA.hom.app M) ≫
            βX.hom.app ((inverseModules IR).mapDerivedCategory.obj M)) ∧
      ∀ Z : DerivedCategory (Modules RX),
        βY.hom.app (gR.push.rightDerivedFunctor.obj Z) ≫
            (mateEquiv (gR.derived h) (gT.derived h) balC.hom).app Z =
          mYb.T.map ((mateEquiv (gR.derived h) (gS.derived h) balA.hom).app Z) ≫
            (mateEquiv (gS.derived h) (gT.derived h) balB.hom).app (mXa.T.obj Z) ≫
            gT.push.rightDerivedFunctor.map (βX.hom.app Z) := by
  classical
  have hA := coefficient_mate_isIso aY aX L V h IR IS ha mYa mXa nYa nXa
  have hB := coefficient_mate_isIso bY bX L V h IS IT hb mYb mXb nYb nXb
  have hC := coefficient_mate_isIso (aY ≫ bY) (aX ≫ bX) L V h IR IT hc
    mYc mXc nYc nXc
  let balA := (asIso (θ_h IR IS ha inferInstance nYa.derived nXa.derived)).symm
  let balB := (asIso (θ_h IS IT hb inferInstance nYb.derived nXb.derived)).symm
  let balC := (asIso (θ_h IR IT hc inferInstance nYc.derived nXc.derived)).symm
  let βY := towerDerived mYa mYb mYc nYa nYb nYc
  let βX := towerDerived mXa mXb mXc nXa nXb nXc
  have hs (M : DerivedCategory (Modules RY)) :
      (inverseModules IT).mapDerivedCategory.map (βY.hom.app M) ≫ balC.hom.app M =
        balB.hom.app (mYa.T.obj M) ≫ mXb.T.map (balA.hom.app M) ≫
          βX.hom.app ((inverseModules IR).mapDerivedCategory.obj M) := by
    have hh := mate_tower_square nYa.derived nYb.derived nYc.derived
      nXa.derived nXb.derived nXc.derived (resD aY bY) (resD aX bX)
      (aD_h IR IS ha inferInstance).hom (aD_h IS IT hb inferInstance).hom
      (aD_h IR IT hc inferInstance).hom
      (action_derived_tower_square aY bY aX bX L IR IS IT ha hb hc) M
    rw [← towerDerived_eq mYa mYb mYc nYa nYb nYc,
      ← towerDerived_eq mXa mXb mXc nXa nXb nXc] at hh
    have hh : βX.hom.app ((inverseModules IR).mapDerivedCategory.obj M) ≫
        balC.inv.app M =
      mXb.T.map (balA.inv.app M) ≫ balB.inv.app (mYa.T.obj M) ≫
        (inverseModules IT).mapDerivedCategory.map (βY.hom.app M) := by
      simpa only [βX, βY, balA, balB, balC, Iso.symm_inv, asIso_hom, θ_h] using hh
    exact cancel_balancing_square mXb.T (balA.app M).symm
      (balB.app (mYa.T.obj M)).symm (balC.app M).symm
      ((inverseModules IT).mapDerivedCategory.map (βY.hom.app M))
      (βX.hom.app ((inverseModules IR).mapDerivedCategory.obj M)) hh
  refine ⟨towerOrdinary mYa mYb mYc nYa nYb nYc,
    towerOrdinary mXa mXb mXc nXa nXb nXc, βY, βX, balA, balB, balC,
    tower_normalized mYa mYb mYc nYa nYb nYc,
    tower_normalized mXa mXb mXc nXa nXb nXc, rfl, rfl, rfl, hs, ?_⟩
  exact mates_of_balancing_square (gR.derived h) (gS.derived h) (gT.derived h)
    βY βX balA.hom balB.hom balC.hom hs

end Transitivity
end SheafOfModules.ToposScalarMate
