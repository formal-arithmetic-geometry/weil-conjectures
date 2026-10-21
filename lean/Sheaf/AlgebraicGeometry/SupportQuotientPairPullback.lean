/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.AlgebraicGeometry.SupportQuotientFlat
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf

import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison

/-!
# Functorial pullback of constant support quotients

Source: Stacks Project, Tag 03Q1, especially (1) and (3), and the ordinary comparison
in the final paragraph of blueprint `lem-pur-kunneth-supported.proof.md`
(blueprint: lem-pur-support-quotient-pair-pullback).

The quotients and quotient maps are exactly those of `SupportQuotientFlat`. The
fixed-scalar presentation is the same presentation used by that dependency: its canonical
realization identifies it with ordinary modules over the constant ring sheaf. The helper
structures only bundle the schemes, closed immersions and factorization hypotheses.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The input closed pair, including precisely the quasi-compact-complement hypothesis.
Source: support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
structure SupportQuotientPair where
  T : Scheme.{u}
  C : Scheme.{u}
  a : C ⟶ T
  closed : IsClosedImmersion a
  qc : QuasiCompact a.openComplement.ι

attribute [instance] SupportQuotientPair.closed SupportQuotientPair.qc

/-- A scheme morphism carrying the source closed subscheme into the target, with its
scheme-theoretic factorization, rather than merely an inclusion of underlying sets.
Source: support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
structure SupportQuotientPairMap (P Q : SupportQuotientPair.{u}) where
  f : P.T ⟶ Q.T
  s : P.C ⟶ Q.C
  w : s ≫ Q.a = P.a ≫ f

/-- Identity input pair map.
Source: the identity clause of the support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
def SupportQuotientPairMap.id (P : SupportQuotientPair.{u}) : SupportQuotientPairMap P P :=
  ⟨𝟙 P.T, 𝟙 P.C, (Category.id_comp P.a).trans (Category.comp_id P.a).symm⟩

/-- Composite input pair map, using the composite of the supplied factorizations.
Source: the composition clause of the support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
def SupportQuotientPairMap.comp {P Q R : SupportQuotientPair.{u}}
    (g : SupportQuotientPairMap P Q) (f : SupportQuotientPairMap Q R) :
    SupportQuotientPairMap P R :=
  ⟨g.f ≫ f.f, g.s ≫ f.s,
    (Category.assoc g.s f.s R.a).trans
      ((congrArg (fun k ↦ g.s ≫ k) f.w).trans
        ((Category.assoc g.s Q.a f.f).symm.trans
          ((congrArg (fun k ↦ k ≫ f.f) g.w).trans (Category.assoc P.a g.f f.f))))⟩

/-- The ordinary etale pair-map family type; all objects and arrows are the recorded ones.
Source: support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
abbrev EtaleSupportQuotientPairMaps (A : Type u) [CommRing A] [Finite A] :=
  ∀ {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q),
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).obj
      (etaleSupportQuotient A Q.a) ⟶ etaleSupportQuotient A P.a

/-- The ordinary pro-etale pair-map family type, in the same coefficient realization.
Source: support-quotient refinement of Tag 03Q1
(blueprint: lem-pur-support-quotient-pair-pullback). -/
abbrev ProEtaleSupportQuotientPairMaps (A : Type u) [CommRing A] [Finite A] :=
  ∀ {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q),
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).obj
      (proEtaleSupportQuotient A Q.a) ⟶ proEtaleSupportQuotient A P.a

/-- The constant etale germ, obtained from constant sections on the final object.
Source: Tag 03Q1 and the normalized stalk clause of `lem-pur-support-quotient-flat`
(blueprint: lem-pur-support-quotient-pair-pullback). -/
def supportQuotientEtaleConstantGerm (A : Type u) [CommRing A] (T : Scheme.{u})
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :=
  (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
    (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))).app
      (op (Etale.mk (𝟙 T))) ≫
    (pointSmallEtale t).toPresheafFiber (Etale.mk (𝟙 T))
      (Over.homMk t (Category.comp_id t))
      ((constantSheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
          (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))).obj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section ConstantSections

universe v₁ v₂ v₃ u₁ u₂ u₃ w

variable {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
  {D : Type w} [Category D]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  (J₃ : GrothendieckTopology C₃)
  [HasWeakSheafify J₁ D] [HasWeakSheafify J₂ D] [HasWeakSheafify J₃ D]

private def constantDirect (F : C₁ ⥤ C₂) [F.IsContinuous J₁ J₂] (N : D) :
    (constantSheaf J₁ D).obj N ⟶
      (F.sheafPushforwardContinuous D J₁ J₂).obj ((constantSheaf J₂ D).obj N) :=
  ((sheafificationAdjunction J₁ D).homEquiv _ _).symm
    (Functor.whiskerLeft F.op (toSheafify J₂ ((Functor.const C₂ᵒᵖ).obj N)))

private theorem constantDirect_unit (F : C₁ ⥤ C₂) [F.IsContinuous J₁ J₂]
    (N : D) (W : C₁ᵒᵖ) :
    (toSheafify J₁ ((Functor.const C₁ᵒᵖ).obj N)).app W ≫
      (constantDirect J₁ J₂ F N).hom.app W =
        (toSheafify J₂ ((Functor.const C₂ᵒᵖ).obj N)).app (F.op.obj W) := by
  have h := ((sheafificationAdjunction J₁ D).homEquiv
    ((Functor.const C₁ᵒᵖ).obj N)
    ((F.sheafPushforwardContinuous D J₁ J₂).obj ((constantSheaf J₂ D).obj N))).apply_symm_apply
    (Functor.whiskerLeft F.op (toSheafify J₂ ((Functor.const C₂ᵒᵖ).obj N)))
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k ↦ k.app W) h

private def constantInverse (F : C₁ ⥤ C₂) [F.IsContinuous J₁ J₂]
    {L : Sheaf J₁ D ⥤ Sheaf J₂ D}
    (a : L ⊣ F.sheafPushforwardContinuous D J₁ J₂) (N : D) :
    L.obj ((constantSheaf J₁ D).obj N) ⟶ (constantSheaf J₂ D).obj N :=
  (a.homEquiv _ _).symm (constantDirect J₁ J₂ F N)

private theorem constantDirect_comp
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃)
    [F.IsContinuous J₁ J₂] [G.IsContinuous J₂ J₃] [H.IsContinuous J₁ J₃]
    (e : F ⋙ G ≅ H) (N : D) :
    constantDirect J₁ J₂ F N ≫
      (F.sheafPushforwardContinuous D J₁ J₂).map (constantDirect J₂ J₃ G N) ≫
        (Functor.sheafPushforwardContinuousComp' e D J₁ J₂ J₃).hom.app
          ((constantSheaf J₃ D).obj N) = constantDirect J₁ J₃ H N := by
  apply ((sheafificationAdjunction J₁ D).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext W
  change (toSheafify J₁ ((Functor.const C₁ᵒᵖ).obj N)).app W ≫
      (constantDirect J₁ J₂ F N).hom.app W ≫
      (constantDirect J₂ J₃ G N).hom.app (F.op.obj W) ≫
      (((Functor.sheafPushforwardContinuousComp' e D J₁ J₂ J₃).hom.app
        ((constantSheaf J₃ D).obj N)).hom.app W) =
    (toSheafify J₁ ((Functor.const C₁ᵒᵖ).obj N)).app W ≫
      (constantDirect J₁ J₃ H N).hom.app W
  rw [Functor.sheafPushforwardContinuousComp'_hom_app_hom_app]
  rw [← Category.assoc, ← Category.assoc, constantDirect_unit]
  change ((toSheafify J₂ ((Functor.const C₂ᵒᵖ).obj N)).app (F.op.obj W) ≫
      (constantDirect J₂ J₃ G N).hom.app (F.op.obj W)) ≫
      ((constantSheaf J₃ D).obj N).obj.map (e.inv.app W.unop).op = _
  rw [constantDirect_unit, constantDirect_unit]
  have hn := (toSheafify J₃ ((Functor.const C₃ᵒᵖ).obj N)).naturality
    (e.inv.app W.unop).op
  change (𝟙 N) ≫
      (toSheafify J₃ ((Functor.const C₃ᵒᵖ).obj N)).app (H.op.obj W) =
    (toSheafify J₃ ((Functor.const C₃ᵒᵖ).obj N)).app (G.op.obj (F.op.obj W)) ≫
      (sheafify J₃ ((Functor.const C₃ᵒᵖ).obj N)).map (e.inv.app W.unop).op at hn
  exact hn.symm.trans (Category.id_comp _)

private theorem homEquiv_mate
    {E E' : Type*} [Category E] [Category E']
    {L L' : E ⥤ E'} {R R' : E' ⥤ E} (a : L ⊣ R) (b : L' ⊣ R')
    (d : R' ≅ R) {X : E} {Y : E'} (t : L'.obj X ⟶ Y) :
    a.homEquiv X Y
        (((conjugateIsoEquiv a b).symm d.symm).inv.app X ≫ t) =
      b.homEquiv X Y t ≫ d.hom.app Y := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc]
  change (a.unit.app X ≫
      R.map (((conjugateEquiv b a).symm d.hom).app X)) ≫ R.map t = _
  rw [← unit_conjugateEquiv_symm b a d.hom X, Category.assoc, ← d.hom.naturality]
  simp only [Category.assoc]

private theorem constantInverse_composite_adjunct
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.IsContinuous J₁ J₂] [G.IsContinuous J₂ J₃]
    {L₁ : Sheaf J₁ D ⥤ Sheaf J₂ D} {L₂ : Sheaf J₂ D ⥤ Sheaf J₃ D}
    (a₁ : L₁ ⊣ F.sheafPushforwardContinuous D J₁ J₂)
    (a₂ : L₂ ⊣ G.sheafPushforwardContinuous D J₂ J₃) (N : D) :
    (a₁.comp a₂).homEquiv _ _
        (L₂.map (constantInverse J₁ J₂ F a₁ N) ≫ constantInverse J₂ J₃ G a₂ N) =
      constantDirect J₁ J₂ F N ≫
        (F.sheafPushforwardContinuous D J₁ J₂).map (constantDirect J₂ J₃ G N) := by
  rw [Adjunction.comp_homEquiv]
  change a₁.homEquiv _ _ (a₂.homEquiv _ _ _) = _
  rw [Adjunction.homEquiv_naturality_left]
  unfold constantInverse
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply]

private theorem constantInverse_comp
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃)
    [F.IsContinuous J₁ J₂] [G.IsContinuous J₂ J₃] [H.IsContinuous J₁ J₃]
    {L₁ : Sheaf J₁ D ⥤ Sheaf J₂ D} {L₂ : Sheaf J₂ D ⥤ Sheaf J₃ D}
    {L₃ : Sheaf J₁ D ⥤ Sheaf J₃ D}
    (a₁ : L₁ ⊣ F.sheafPushforwardContinuous D J₁ J₂)
    (a₂ : L₂ ⊣ G.sheafPushforwardContinuous D J₂ J₃)
    (a₃ : L₃ ⊣ H.sheafPushforwardContinuous D J₁ J₃)
    (e : F ⋙ G ≅ H) (N : D) :
    constantInverse J₁ J₃ H a₃ N =
      ((conjugateIsoEquiv a₃ (a₁.comp a₂)).symm
        (Functor.sheafPushforwardContinuousComp' e D J₁ J₂ J₃).symm).inv.app
          ((constantSheaf J₁ D).obj N) ≫
        L₂.map (constantInverse J₁ J₂ F a₁ N) ≫ constantInverse J₂ J₃ G a₂ N := by
  apply (a₃.homEquiv _ _).injective
  unfold constantInverse
  rw [Equiv.apply_symm_apply, homEquiv_mate, Adjunction.comp_homEquiv]
  change _ = a₁.homEquiv _ _ (a₂.homEquiv _ _ _) ≫ _
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  simpa only [Category.assoc] using (constantDirect_comp J₁ J₂ J₃ F G H e N).symm

private theorem constantDirect_id
    (F : C₁ ⥤ C₁) [F.IsContinuous J₁ J₁] (e : F ≅ 𝟭 C₁) (N : D) :
    constantDirect J₁ J₁ F N =
      (Functor.sheafPushforwardContinuousId' e D J₁).inv.app
        ((constantSheaf J₁ D).obj N) := by
  apply ((sheafificationAdjunction J₁ D).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext W
  change (toSheafify J₁ ((Functor.const C₁ᵒᵖ).obj N)).app W ≫
      (constantDirect J₁ J₁ F N).hom.app W = _
  rw [constantDirect_unit]
  change (toSheafify J₁ ((Functor.const C₁ᵒᵖ).obj N)).app (F.op.obj W) =
    (toSheafify J₁ ((Functor.const C₁ᵒᵖ).obj N)).app W ≫
      (((Functor.sheafPushforwardContinuousId' e D J₁).inv.app
        ((constantSheaf J₁ D).obj N)).hom.app W)
  rw [Functor.sheafPushforwardContinuousId'_inv_app_hom_app]
  exact (Category.id_comp _).symm.trans
    ((toSheafify J₁ ((Functor.const C₁ᵒᵖ).obj N)).naturality (e.hom.app W.unop).op)

private theorem constantInverse_id
    (F : C₁ ⥤ C₁) [F.IsContinuous J₁ J₁]
    {L : Sheaf J₁ D ⥤ Sheaf J₁ D}
    (a : L ⊣ F.sheafPushforwardContinuous D J₁ J₁)
    (e : F ≅ 𝟭 C₁) (N : D) :
    constantInverse J₁ J₁ F a N =
      ((conjugateIsoEquiv Adjunction.id a).symm
        (Functor.sheafPushforwardContinuousId' e D J₁).symm).hom.app
          ((constantSheaf J₁ D).obj N) := by
  apply (a.homEquiv _ _).injective
  unfold constantInverse
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  change _ = a.unit.app _ ≫
    (F.sheafPushforwardContinuous D J₁ J₁).map
      (((conjugateEquiv Adjunction.id a).symm
        (Functor.sheafPushforwardContinuousId' e D J₁).inv).app _)
  rw [← unit_conjugateEquiv_symm Adjunction.id a]
  change constantDirect J₁ J₁ F N =
    𝟙 _ ≫ (Functor.sheafPushforwardContinuousId' e D J₁).inv.app
      ((constantSheaf J₁ D).obj N)
  rw [Category.id_comp]
  exact constantDirect_id J₁ F e N

end ConstantSections

section Construction

private abbrev Coeff (A : Type u) [CommRing A] :=
  ModuleCat.{u + 1} (ULift.{u + 1, u} A)

private abbrev unitCoeff (A : Type u) [CommRing A] :=
  ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)

variable (A : Type u) [CommRing A]

private instance etale_cont {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.IsContinuous (C := Y.Etale) (D := X.Etale)
      (MorphismProperty.Over.pullback @Etale ⊤ f)
      Y.smallEtaleTopology X.smallEtaleTopology :=
  Etale.isContinuous_overPullback f


private theorem etale_quotient_epi (P : SupportQuotientPair.{u}) :
    Epi (etaleSupportQuotientMap A P.a) := by
  unfold etaleSupportQuotientMap
  infer_instance

private theorem proetale_quotient_epi (P : SupportQuotientPair.{u}) :
    Epi (proEtaleSupportQuotientMap A P.a) := by
  unfold proEtaleSupportQuotientMap
  infer_instance

private theorem etale_constant_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f).hom.app
        (unitCoeff A) =
      constantInverse Y.smallEtaleTopology X.smallEtaleTopology f.Etale
        (Etale.upperStarLowerStarAdjunction (Coeff A) f) (unitCoeff A) := by
  let a := Etale.upperStarLowerStarAdjunction (Coeff A) f
  let b := constantSheafAdj Y.smallEtaleTopology (Coeff A)
    (MorphismProperty.Over.mkIdTerminal @Etale Y)
  apply (a.homEquiv _ _).injective
  dsimp only [a]
  unfold constantInverse
  conv_rhs => erw [Equiv.apply_symm_apply]
  apply (b.homEquiv _ _).injective
  change ((b.comp a).ofNatIsoRight (NatIso.ofComponents (fun _ ↦ Iso.refl _))).homEquiv
    _ _ ((Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f).hom.app
      (unitCoeff A)) = _
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  change (toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (unitCoeff A))).app
        (op (f.Etale.obj (Etale.mk (𝟙 Y)))) =
    (toSheafify Y.smallEtaleTopology
      ((Functor.const Y.Etaleᵒᵖ).obj (unitCoeff A))).app (op (Etale.mk (𝟙 Y))) ≫
      (constantDirect Y.smallEtaleTopology X.smallEtaleTopology f.Etale
        (unitCoeff A)).hom.app (op (Etale.mk (𝟙 Y)))
  exact (constantDirect_unit Y.smallEtaleTopology X.smallEtaleTopology f.Etale
    (unitCoeff A) (op (Etale.mk (𝟙 Y)))).symm

private theorem proetale_constant_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantInverseImageMap f (Coeff A) (unitCoeff A) =
      constantInverse (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f)
        (proEtaleSheafAdjunction f (Coeff A)) (unitCoeff A) := by
  rw [constantInverse, Adjunction.homEquiv_counit]
  rfl

private theorem comparison_constant_eq (X : Scheme.{u}) :
    supportQuotientConstantComparison A (T := X) =
      constantInverse X.smallEtaleTopology (ProEt.topology X) (toProEt X)
        (ProEtale.comparisonAdjunction (Coeff A) X) (unitCoeff A) := by
  apply ((ProEtale.comparisonAdjunction (Coeff A) X).homEquiv _ _).injective
  unfold supportQuotientConstantComparison constantInverse
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply ((constantSheafAdj X.smallEtaleTopology (Coeff A)
    (Etale.isTerminalMkId X)).homEquiv _ _).injective
  erw [Equiv.apply_symm_apply]
  change _ = (toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (unitCoeff A))).app (op (Etale.mk (𝟙 X))) ≫
      (constantDirect X.smallEtaleTopology (ProEt.topology X) (toProEt X)
        (unitCoeff A)).hom.app (op (Etale.mk (𝟙 X)))
  exact (constantDirect_unit X.smallEtaleTopology (ProEt.topology X) (toProEt X)
    (unitCoeff A) (op (Etale.mk (𝟙 X)))).symm

private theorem etale_constant_id (X : Scheme.{u}) :
    (Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) (𝟙 X)).hom.app
        (unitCoeff A) =
      (ProEtale.supportSiteEtaleComparisonId (Coeff A) X).hom.app
        ((constantSheaf X.smallEtaleTopology (Coeff A)).obj (unitCoeff A)) := by
  have := etale_cont (𝟙 X)
  rw [etale_constant_eq]
  exact constantInverse_id X.smallEtaleTopology (MorphismProperty.Over.pullback @Etale ⊤ (𝟙 X))
    (Etale.upperStarLowerStarAdjunction (Coeff A) (𝟙 X))
    (MorphismProperty.Over.pullbackId @Etale ⊤ X) (unitCoeff A)

private theorem proetale_constant_id (X : Scheme.{u}) :
    proEtaleConstantInverseImageMap (𝟙 X) (Coeff A) (unitCoeff A) =
      (ProEtale.supportSiteProEtaleComparisonId (Coeff A) X).hom.app
        ((constantSheaf (ProEt.topology X) (Coeff A)).obj (unitCoeff A)) := by
  rw [proetale_constant_eq]
  exact constantInverse_id (ProEt.topology X) (proEtaleBaseChange (𝟙 X))
    (proEtaleSheafAdjunction (𝟙 X) (Coeff A))
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) (unitCoeff A)

private theorem etale_constant_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) (f ≫ g)).hom.app
        (unitCoeff A) =
      (ProEtale.supportSiteEtaleComparisonComp (Coeff A) f g).hom.app
        ((constantSheaf Z.smallEtaleTopology (Coeff A)).obj (unitCoeff A)) ≫
      (Etale.upperStar (Coeff A) f).map
        ((Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) g).hom.app
          (unitCoeff A)) ≫
      (Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f).hom.app (unitCoeff A) := by
  have := etale_cont g
  have := etale_cont f
  have := etale_cont (f ≫ g)
  simp only [etale_constant_eq]
  exact constantInverse_comp Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology
    (MorphismProperty.Over.pullback @Etale ⊤ g)
    (MorphismProperty.Over.pullback @Etale ⊤ f)
    (MorphismProperty.Over.pullback @Etale ⊤ (f ≫ g))
    (Etale.upperStarLowerStarAdjunction (Coeff A) g)
    (Etale.upperStarLowerStarAdjunction (Coeff A) f)
    (Etale.upperStarLowerStarAdjunction (Coeff A) (f ≫ g))
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).symm _

private theorem proetale_constant_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleConstantInverseImageMap (f ≫ g) (Coeff A) (unitCoeff A) =
      (ProEtale.supportSiteProEtaleComparisonComp (Coeff A) f g).hom.app
        ((constantSheaf (ProEt.topology Z) (Coeff A)).obj (unitCoeff A)) ≫
      (ProEtale.upperStar (Coeff A) f).map
        (proEtaleConstantInverseImageMap g (Coeff A) (unitCoeff A)) ≫
      proEtaleConstantInverseImageMap f (Coeff A) (unitCoeff A) := by
  simp only [proetale_constant_eq]
  exact constantInverse_comp (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)
    (proEtaleBaseChange g) (proEtaleBaseChange f) (proEtaleBaseChange (f ≫ g))
    (proEtaleSheafAdjunction g (Coeff A)) (proEtaleSheafAdjunction f (Coeff A))
    (proEtaleSheafAdjunction (f ≫ g) (Coeff A))
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm _

private theorem comparison_constant_square {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ProEtale.upperStar (Coeff A) f).map (supportQuotientConstantComparison A (T := Y)) ≫
        proEtaleConstantInverseImageMap f (Coeff A) (unitCoeff A) =
      (ProEtale.supportSiteComparisonCoefficientPullbackIso (Coeff A) f).inv.app
          ((constantSheaf Y.smallEtaleTopology (Coeff A)).obj (unitCoeff A)) ≫
        (ProEtale.comparisonUpperStar (Coeff A) X).map
          ((Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f).hom.app
            (unitCoeff A)) ≫ supportQuotientConstantComparison A (T := X) := by
  let ap := (ProEtale.comparisonAdjunction (Coeff A) Y).comp
    (proEtaleSheafAdjunction f (Coeff A))
  let ae := (Etale.upperStarLowerStarAdjunction (Coeff A) f).comp
    (ProEtale.comparisonAdjunction (Coeff A) X)
  let d := ProEtale.supportSiteComparisonCoefficientDirectImageIso (Coeff A) f
  have hd (S : Sheaf (ProEt.topology X) (Coeff A)) (W : Y.Etaleᵒᵖ) :
      ((d.inv.app S).hom.app W) = 𝟙 _ := by
    change (𝟙 _ ≫ S.obj.map (𝟙 _) ≫ 𝟙 _) = 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact S.obj.map_id _
  simp only [comparison_constant_eq, proetale_constant_eq, etale_constant_eq]
  apply (ap.homEquiv _ _).injective
  change _ = ap.homEquiv _ _
    (((conjugateIsoEquiv ap ae).symm d).inv.app _ ≫ _)
  have hm := homEquiv_mate ap ae d.symm
    ((ProEtale.comparisonUpperStar (Coeff A) X).map
      (constantInverse Y.smallEtaleTopology X.smallEtaleTopology f.Etale
        (Etale.upperStarLowerStarAdjunction (Coeff A) f) (unitCoeff A)) ≫
      constantInverse X.smallEtaleTopology (ProEt.topology X) (toProEt X)
        (ProEtale.comparisonAdjunction (Coeff A) X) (unitCoeff A))
  simp only [Iso.symm_symm_eq] at hm
  erw [hm]
  have hp := constantInverse_composite_adjunct Y.smallEtaleTopology
    (ProEt.topology Y) (ProEt.topology X) (toProEt Y) (proEtaleBaseChange f)
    (ProEtale.comparisonAdjunction (Coeff A) Y) (proEtaleSheafAdjunction f (Coeff A))
    (unitCoeff A)
  have he := constantInverse_composite_adjunct Y.smallEtaleTopology
    X.smallEtaleTopology (ProEt.topology X) f.Etale (toProEt X)
    (Etale.upperStarLowerStarAdjunction (Coeff A) f)
    (ProEtale.comparisonAdjunction (Coeff A) X) (unitCoeff A)
  erw [hp, he]
  apply ((sheafificationAdjunction Y.smallEtaleTopology (Coeff A)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext W
  change (toSheafify Y.smallEtaleTopology
      ((Functor.const Y.Etaleᵒᵖ).obj (unitCoeff A))).app W ≫
      (constantDirect Y.smallEtaleTopology (ProEt.topology Y) (toProEt Y)
        (unitCoeff A)).hom.app W ≫
      (constantDirect (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f)
        (unitCoeff A)).hom.app ((toProEt Y).op.obj W) =
    (toSheafify Y.smallEtaleTopology
      ((Functor.const Y.Etaleᵒᵖ).obj (unitCoeff A))).app W ≫
      (constantDirect Y.smallEtaleTopology X.smallEtaleTopology f.Etale
        (unitCoeff A)).hom.app W ≫
      (constantDirect X.smallEtaleTopology (ProEt.topology X) (toProEt X)
        (unitCoeff A)).hom.app (f.Etale.op.obj W) ≫
      ((d.inv.app ((constantSheaf (ProEt.topology X) (Coeff A)).obj
        (unitCoeff A))).hom.app W)
  rw [hd]
  rw [← Category.assoc, constantDirect_unit, constantDirect_unit,
    ← Category.assoc, ← Category.assoc, constantDirect_unit, constantDirect_unit]
  erw [Category.comp_id]
  rfl

private theorem comparison_constant_isIso (X : Scheme.{u}) :
    IsIso (supportQuotientConstantComparison A (T := X)) := by
  let B := Coeff A
  let M := unitCoeff A
  let adj := ProEtale.comparisonAdjunction B X
  let adjEt := constantSheafAdj X.smallEtaleTopology B (Etale.isTerminalMkId X)
  let adjPro := constantSheafAdj (ProEt.topology X) B
    ((Etale.isTerminalMkId X).isTerminalObj (toProEt X))
  let e := (adjEt.comp adj).leftAdjointUniq adjPro
  have he : e.hom.app M = supportQuotientConstantComparison A (T := X) := by
    apply (adj.homEquiv _ _).injective
    dsimp only [supportQuotientConstantComparison]
    rw [Equiv.apply_symm_apply]
    apply (adjEt.homEquiv _ _).injective
    change (adjEt.comp adj).homEquiv _ _ (e.hom.app M) = _
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Equiv.apply_symm_apply]
    rfl
  rw [← he]
  infer_instance

variable [Finite A]

private theorem pair_range {P Q : SupportQuotientPair.{u}}
    (f : SupportQuotientPairMap P Q) {x : P.T} (hx : x ∈ Set.range P.a) :
    f.f x ∈ Set.range Q.a := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨f.s z, congrArg (fun k : P.C ⟶ Q.T ↦ k z) f.w⟩

private theorem pair_relation_zero {P Q : SupportQuotientPair.{u}}
    (f : SupportQuotientPairMap P Q) :
    (Etale.upperStar (Coeff A) f.f).map (etaleSupportQuotientArrow A Q.a) ≫
        (Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f.f).hom.app (unitCoeff A) ≫
          etaleSupportQuotientMap A P.a = 0 := by
  apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro x
  let t := P.T.algClosurePoint x
  let Φ := (pointSmallEtale t).sheafFiber (A := (Coeff A))
  by_cases hx : t (IsLocalRing.closedPoint _) ∈ Set.range P.a
  · have hxQ : (t ≫ f.f) (IsLocalRing.closedPoint _) ∉ Set.range Q.a.openComplement.ι := by
      change (t ≫ f.f) (IsLocalRing.closedPoint _) ∈
        (Set.range Q.a.openComplement.ι)ᶜ
      rw [← Q.a.range_eq_compl_range_openComplement_ι]
      exact pair_range f hx
    let G := (Etale.openImmersionRestriction (Coeff A) Q.a.openComplement.ι).obj
      ((constantSheaf Q.T.smallEtaleTopology (Coeff A)).obj (unitCoeff A))
    have hz := Etale.isZero_uliftSheafFiber_openImmersionLowerShriek_obj (Coeff A)
      Q.a.openComplement.ι (t ≫ f.f) hxQ G
    have hz' := hz.of_iso
      (((pointSmallEtale (t ≫ f.f)).uliftSheafFiberIso.{u + 1} (Coeff A)).app
        ((Etale.openImmersionLowerShriek (Coeff A) Q.a.openComplement.ι).obj G)).symm
    have hz'' := hz'.of_iso
      ((Etale.upperStarCompSheafFiberIso (Coeff A) f.f t).app
        ((Etale.openImmersionLowerShriek (Coeff A) Q.a.openComplement.ι).obj G))
    exact hz''.eq_of_src _ _
  · have hz := ((supportQuotient_flat_kflat_stalk_comparison A P.a).2.2.2.2.1
      _ t).2 hx
    exact hz.eq_of_tgt _ _

private theorem etale_pair_exists {P Q : SupportQuotientPair.{u}}
    (f : SupportQuotientPairMap P Q) :
    ∃ c : (Etale.upperStar (Coeff A) f.f).obj (etaleSupportQuotient A Q.a) ⟶
        etaleSupportQuotient A P.a,
      (Etale.upperStar (Coeff A) f.f).map (etaleSupportQuotientMap A Q.a) ≫ c =
        (Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f.f).hom.app (unitCoeff A) ≫
          etaleSupportQuotientMap A P.a := by
  obtain ⟨c, hc⟩ := CokernelCofork.IsColimit.desc'
    (isColimitOfHasCokernelOfPreservesColimit (Etale.upperStar (Coeff A) f.f)
      (etaleSupportQuotientArrow A Q.a)) _ (pair_relation_zero A f)
  exact ⟨c, hc⟩

omit [Finite A] in
private theorem constant_germ_isIso (T : Scheme.{u})
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    IsIso (supportQuotientEtaleConstantGerm A T t) := by
  let Φ := pointSmallEtale t
  let U := Etale.mk (𝟙 T)
  let x : Φ.fiber.obj U := Over.homMk t (Category.comp_id t)
  have h₁ : (Φ.presheafFiberConstIso (unitCoeff A)).inv =
      Φ.toPresheafFiber U x ((Functor.const T.Etaleᵒᵖ).obj (unitCoeff A)) := by
    apply (cancel_mono (Φ.presheafFiberConstIso (unitCoeff A)).hom).mp
    simp only [Iso.inv_hom_id, Φ.toPresheafFiber_presheafFiberConstIso_hom]
  have h : supportQuotientEtaleConstantGerm A T t =
      (Φ.presheafFiberConstIso (unitCoeff A)).inv ≫
        Φ.presheafFiber.map (toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (unitCoeff A))) := by
    rw [h₁, Φ.toPresheafFiber_naturality]
    rfl
  rw [h]
  infer_instance

private theorem etale_stalk_on_support {P Q : SupportQuotientPair.{u}}
    (f : SupportQuotientPairMap P Q)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ P.T)
    (ht : t (IsLocalRing.closedPoint Ω) ∈ Set.range P.a)
    (c : (Etale.upperStar (Coeff A) f.f).obj (etaleSupportQuotient A Q.a) ⟶
      etaleSupportQuotient A P.a)
    (hc : (Etale.upperStar (Coeff A) f.f).map (etaleSupportQuotientMap A Q.a) ≫ c =
      (Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f.f).hom.app (unitCoeff A) ≫
        etaleSupportQuotientMap A P.a) :
    ∃ (eS : (pointSmallEtale t).sheafFiber.obj
        ((Etale.upperStar (Coeff A) f.f).obj (etaleSupportQuotient A Q.a)) ≅ (unitCoeff A))
      (eT : (pointSmallEtale t).sheafFiber.obj (etaleSupportQuotient A P.a) ≅ (unitCoeff A)),
      supportQuotientEtaleConstantGerm A P.T t ≫
        (pointSmallEtale t).sheafFiber.map
          ((Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f.f).inv.app (unitCoeff A)) ≫
        (pointSmallEtale t).sheafFiber.map
          ((Etale.upperStar (Coeff A) f.f).map (etaleSupportQuotientMap A Q.a)) ≫ eS.hom = 𝟙 _ ∧
      supportQuotientEtaleConstantGerm A P.T t ≫
        (pointSmallEtale t).sheafFiber.map (etaleSupportQuotientMap A P.a) ≫ eT.hom = 𝟙 _ ∧
      (pointSmallEtale t).sheafFiber.map c ≫ eT.hom = eS.hom := by
  let Φ := (pointSmallEtale t).sheafFiber (A := (Coeff A))
  let Ψ := (pointSmallEtale (t ≫ f.f)).sheafFiber (A := (Coeff A))
  let F := Etale.upperStar (Coeff A) f.f
  let k := (Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f.f).app (unitCoeff A)
  obtain ⟨eQ, heQ⟩ := ((supportQuotient_flat_kflat_stalk_comparison A Q.a).2.2.2.2.1
    _ (t ≫ f.f)).1 (pair_range f ht)
  have hgQ := constant_germ_isIso A Q.T (t ≫ f.f)
  have hiQ : IsIso (Ψ.map (etaleSupportQuotientMap A Q.a)) := by
    have hh : IsIso (supportQuotientEtaleConstantGerm A Q.T (t ≫ f.f) ≫
        Ψ.map (etaleSupportQuotientMap A Q.a) ≫ eQ.hom) := by
      rw [show supportQuotientEtaleConstantGerm A Q.T (t ≫ f.f) ≫
        Ψ.map (etaleSupportQuotientMap A Q.a) ≫ eQ.hom = 𝟙 _ from heQ]
      infer_instance
    have hi : IsIso (Ψ.map (etaleSupportQuotientMap A Q.a) ≫ eQ.hom) :=
      (isIso_comp_left_iff (supportQuotientEtaleConstantGerm A Q.T (t ≫ f.f)) _).mp hh
    exact (isIso_comp_right_iff _ eQ.hom).mp hi
  have hif : IsIso (Φ.map (F.map (etaleSupportQuotientMap A Q.a))) := by
    exact (NatIso.isIso_map_iff (Etale.upperStarCompSheafFiberIso (Coeff A) f.f t)
      (etaleSupportQuotientMap A Q.a)).mpr hiQ
  have hgt := constant_germ_isIso A P.T t
  let z := supportQuotientEtaleConstantGerm A P.T t ≫ Φ.map k.inv ≫
    Φ.map (F.map (etaleSupportQuotientMap A Q.a))
  have hz : IsIso z := by dsimp only [z]; infer_instance
  let eS := (asIso z).symm
  obtain ⟨eT, heT⟩ := ((supportQuotient_flat_kflat_stalk_comparison A P.a).2.2.2.2.1
    _ t).1 ht
  refine ⟨eS, eT, ?_, heT, ?_⟩
  · change _ ≫ _ ≫ _ ≫ inv z = 𝟙 _
    rw [← Category.assoc, ← Category.assoc]
    exact IsIso.hom_inv_id z
  · apply (cancel_epi z).mp
    change z ≫ Φ.map c ≫ eT.hom = z ≫ inv z
    rw [IsIso.hom_inv_id]
    dsimp only [z]
    simp only [Category.assoc]
    rw [← Φ.map_comp_assoc (F.map (etaleSupportQuotientMap A Q.a)) c, hc]
    change supportQuotientEtaleConstantGerm A P.T t ≫ Φ.map k.inv ≫
      Φ.map (k.hom ≫ etaleSupportQuotientMap A P.a) ≫ eT.hom = _
    rw [Φ.map_comp]
    simp only [Category.assoc]
    rw [← Φ.map_comp_assoc, Iso.inv_hom_id, Φ.map_id, Category.id_comp]
    exact heT

private theorem etale_pair_isIso {P Q : SupportQuotientPair.{u}}
    (f : SupportQuotientPairMap P Q)
    (c : (Etale.upperStar (Coeff A) f.f).obj (etaleSupportQuotient A Q.a) ⟶
      etaleSupportQuotient A P.a)
    (hc : (Etale.upperStar (Coeff A) f.f).map (etaleSupportQuotientMap A Q.a) ≫ c =
      (Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f.f).hom.app (unitCoeff A) ≫
        etaleSupportQuotientMap A P.a)
    (hcart : IsPullback f.s P.a Q.a f.f) : IsIso c := by
  apply isIso_of_isIso_sheafFiber_map
  intro x
  let t := P.T.algClosurePoint x
  let Φ := (pointSmallEtale t).sheafFiber (A := (Coeff A))
  have hi : IsIso (Φ.map c) := by
    by_cases hx : t (IsLocalRing.closedPoint _) ∈ Set.range P.a
    · obtain ⟨eS, eT, _, _, h⟩ := etale_stalk_on_support A f t hx c hc
      have hh : IsIso (Φ.map c ≫ eT.hom) := by rw [h]; infer_instance
      exact (isIso_comp_right_iff _ eT.hom).mp hh
    · have hxQ : (t ≫ f.f) (IsLocalRing.closedPoint _) ∉ Set.range Q.a := by
        simpa only [range_snd_of_isPullback hcart, Set.mem_preimage,
          Scheme.Hom.comp_apply] using hx
      have hzT := ((supportQuotient_flat_kflat_stalk_comparison A P.a).2.2.2.2.1
        _ t).2 hx
      have hzS := ((supportQuotient_flat_kflat_stalk_comparison A Q.a).2.2.2.2.1
        _ (t ≫ f.f)).2 hxQ
      have hzS' := hzS.of_iso
        ((Etale.upperStarCompSheafFiberIso (Coeff A) f.f t).app (etaleSupportQuotient A Q.a))
      have heq : Φ.map c = 0 := hzT.eq_of_tgt _ _
      rw [heq]
      exact (isIsoZero_iff_source_target_isZero _ _).mpr ⟨hzS', hzT⟩
  exact (NatIso.isIso_map_iff
    ((pointSmallEtale t).uliftSheafFiberIso.{u + 1} (Coeff A)) c).mpr hi

omit [Finite A] in
private theorem proetale_pair_transport {P Q : SupportQuotientPair.{u}}
    (f : SupportQuotientPairMap P Q)
    (c : (Etale.upperStar (Coeff A) f.f).obj (etaleSupportQuotient A Q.a) ⟶
      etaleSupportQuotient A P.a)
    (hc : (Etale.upperStar (Coeff A) f.f).map (etaleSupportQuotientMap A Q.a) ≫ c =
      (Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f.f).hom.app (unitCoeff A) ≫
        etaleSupportQuotientMap A P.a)
    (α : (ProEtale.comparisonUpperStar (Coeff A) Q.T).obj
      (etaleSupportQuotient A Q.a) ≅ proEtaleSupportQuotient A Q.a)
    (α' : (ProEtale.comparisonUpperStar (Coeff A) P.T).obj
      (etaleSupportQuotient A P.a) ≅ proEtaleSupportQuotient A P.a)
    (hα : (ProEtale.comparisonUpperStar (Coeff A) Q.T).map
        (etaleSupportQuotientMap A Q.a) ≫ α.hom =
      supportQuotientConstantComparison A (T := Q.T) ≫ proEtaleSupportQuotientMap A Q.a)
    (hα' : (ProEtale.comparisonUpperStar (Coeff A) P.T).map
        (etaleSupportQuotientMap A P.a) ≫ α'.hom =
      supportQuotientConstantComparison A (T := P.T) ≫ proEtaleSupportQuotientMap A P.a) :
    ∃ d : (ProEtale.upperStar (Coeff A) f.f).obj (proEtaleSupportQuotient A Q.a) ⟶
        proEtaleSupportQuotient A P.a,
      (ProEtale.upperStar (Coeff A) f.f).map (proEtaleSupportQuotientMap A Q.a) ≫ d =
        proEtaleConstantInverseImageMap f.f (Coeff A) (unitCoeff A) ≫
          proEtaleSupportQuotientMap A P.a ∧
      (ProEtale.upperStar (Coeff A) f.f).map α.hom ≫ d =
        (ProEtale.supportSiteComparisonCoefficientPullbackIso (Coeff A) f.f).inv.app
            (etaleSupportQuotient A Q.a) ≫
          (ProEtale.comparisonUpperStar (Coeff A) P.T).map c ≫ α'.hom ∧
      (IsIso c → IsIso d) := by
  let F := ProEtale.upperStar (Coeff A) f.f
  let D := ProEtale.comparisonUpperStar (Coeff A) P.T
  let E := ProEtale.comparisonUpperStar (Coeff A) Q.T
  let ρ := ProEtale.supportSiteComparisonCoefficientPullbackIso (Coeff A) f.f
  let d := F.map α.inv ≫ ρ.inv.app (etaleSupportQuotient A Q.a) ≫ D.map c ≫ α'.hom
  have hd : F.map α.hom ≫ d =
      ρ.inv.app (etaleSupportQuotient A Q.a) ≫ D.map c ≫ α'.hom := by
    dsimp only [d]
    rw [← Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.id_comp]
  refine ⟨d, ?_, hd, ?_⟩
  · have hk := comparison_constant_isIso A Q.T
    apply (cancel_epi (F.map (supportQuotientConstantComparison A (T := Q.T)))).mp
    rw [← Category.assoc, ← F.map_comp, ← hα, F.map_comp, Category.assoc, hd]
    have hn := ρ.inv.naturality (etaleSupportQuotientMap A Q.a)
    change F.map (E.map (etaleSupportQuotientMap A Q.a)) ≫
      ρ.inv.app (etaleSupportQuotient A Q.a) =
      ρ.inv.app _ ≫ D.map ((Etale.upperStar (Coeff A) f.f).map
        (etaleSupportQuotientMap A Q.a)) at hn
    rw [← Category.assoc, ← Category.assoc, hn]
    simp only [Category.assoc]
    rw [← D.map_comp_assoc, hc, D.map_comp, Category.assoc, hα']
    have hs : F.map (supportQuotientConstantComparison A (T := Q.T)) ≫
        proEtaleConstantInverseImageMap f.f (Coeff A) (unitCoeff A) =
      ρ.inv.app ((constantSheaf Q.T.smallEtaleTopology (Coeff A)).obj (unitCoeff A)) ≫
        D.map ((Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f.f).hom.app
          (unitCoeff A)) ≫ supportQuotientConstantComparison A (T := P.T) :=
      comparison_constant_square A f.f
    simpa only [Category.assoc, Functor.id_obj] using
      (congrArg (fun k ↦ k ≫ proEtaleSupportQuotientMap A P.a) hs).symm
  · intro hi
    dsimp only [d]
    infer_instance

end Construction

/-- Unique normalized ordinary support-quotient maps, their stalks, Cartesian
isomorphisms, identities, compositions and the normalized etale/pro-etale comparison.
Source: Tag 03Q1 (1), (3), and the final paragraph of the blueprint proof of
`lem-pur-kunneth-supported` (blueprint: lem-pur-support-quotient-pair-pullback).

Proof (the node's eight steps):
1. Exact constant-coefficient etale pullback (`prop-weil-pbc-inverse-image-modules-exact`)
   carries the defining cokernel presentation to a cokernel presentation, with epic
   pulled-back quotient map. Its coefficient identification preserves constant sections.
2. The defining relation maps to zero in the target quotient: on its support the source
   extension-by-zero stalk is zero, by the factorization, inverse-image stalk formula and
   extension-by-zero stalk formula (`lem-weil-pbc-inverse-image-stalk-germ`,
   `lem-weil-pbc-extension-by-zero-stalks`); off the support the target stalk is zero
   (`lem-pur-support-quotient-flat`). Exact stalks and conservativity applied to the image
   give equality to zero as an ordinary module morphism
   (`prop-weil-pbc-geometric-stalks-exact`, `lemma-weil-pbc-geometric-stalk-conservative`).
3. The cokernel universal property gives the unique etale map. Its normalized stalk on
   the closed support is the identity, since both quotient maps preserve the constant
   generator; off the support its target is zero.
4. For a Cartesian closed subscheme the two stalks are simultaneously A or zero; thus
   the etale map is an isomorphism by geometric-stalk conservativity.
5. Naturality of `lem-weil-pbc-comparison-pullback` at every constant section from the
   final sheaf, and finite-product preservation, normalize its component on coefficients.
   Uniqueness of sheafification makes this component the constant-section identity.
   The same argument normalizes identity and composition comparisons; the pro-etale
   coefficient-composition equation is `lem-pur-proetale-constant-ring-composition`.
6. Define the pro-etale map by transporting the etale map through the quotient
   comparisons of `lem-pur-support-quotient-flat` and the pullback comparison. Their
   normalizations give the quotient equation and the comparison square. Exact comparison
   (`lem-sf-comparison-pullback-exact`) preserves the quotient epimorphism, giving uniqueness.
7. In the Cartesian case all factors in this transport are isomorphisms, so is the map.
8. The identity satisfies the quotient equation. The composite of two pair maps also
   satisfies it, using the coefficient-normalized composition comparison and the composed
   factorization. Uniqueness gives both equalities of ordinary sheaf morphisms.
No flatness of a scheme map, reducedness, or pro-etale geometric-stalk conservativity is used.
-/
theorem supportQuotient_pair_pullback (A : Type u) [CommRing A] [Finite A] :
    ∃ (cEt : EtaleSupportQuotientPairMaps A) (cPro : ProEtaleSupportQuotientPairMaps A),
      (∀ {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q),
        (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).map
            (etaleSupportQuotientMap A Q.a) ≫ cEt f =
          (Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f.f).hom.app
            (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)) ≫
              etaleSupportQuotientMap A P.a ∧
        ∀ d, (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).map
            (etaleSupportQuotientMap A Q.a) ≫ d =
          (Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f.f).hom.app
            (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)) ≫
              etaleSupportQuotientMap A P.a → d = cEt f) ∧
      (∀ {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q),
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).map
            (proEtaleSupportQuotientMap A Q.a) ≫ cPro f =
          proEtaleConstantInverseImageMap f.f
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)) ≫
              proEtaleSupportQuotientMap A P.a ∧
        ∀ d, (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).map
            (proEtaleSupportQuotientMap A Q.a) ≫ d =
          proEtaleConstantInverseImageMap f.f
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)) ≫
              proEtaleSupportQuotientMap A P.a → d = cPro f) ∧
      (∀ {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q)
          (Ω : Type u) [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ P.T),
        (t (IsLocalRing.closedPoint Ω) ∈ Set.range P.a →
          ∃ (eS : (pointSmallEtale t).sheafFiber.obj
              ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).obj
                (etaleSupportQuotient A Q.a)) ≅
              ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))
            (eT : (pointSmallEtale t).sheafFiber.obj (etaleSupportQuotient A P.a) ≅
              ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)),
            supportQuotientEtaleConstantGerm A P.T t ≫
              (pointSmallEtale t).sheafFiber.map
                ((Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A) f.f).inv.app
                  (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))) ≫
              (pointSmallEtale t).sheafFiber.map
                ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).map
                  (etaleSupportQuotientMap A Q.a)) ≫ eS.hom = 𝟙 _ ∧
            supportQuotientEtaleConstantGerm A P.T t ≫
              (pointSmallEtale t).sheafFiber.map (etaleSupportQuotientMap A P.a) ≫
                eT.hom = 𝟙 _ ∧
            (pointSmallEtale t).sheafFiber.map (cEt f) ≫ eT.hom = eS.hom) ∧
        (t (IsLocalRing.closedPoint Ω) ∉ Set.range P.a →
          IsZero ((pointSmallEtale t).sheafFiber.obj (etaleSupportQuotient A P.a)) ∧
            (pointSmallEtale t).sheafFiber.map (cEt f) = 0)) ∧
      (∀ {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q),
        IsPullback f.s P.a Q.a f.f → IsIso (cEt f) ∧ IsIso (cPro f)) ∧
      (∀ P : SupportQuotientPair.{u},
        cEt (SupportQuotientPairMap.id P) =
          (ProEtale.supportSiteEtaleComparisonId
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) P.T).hom.app
              (etaleSupportQuotient A P.a) ∧
        cPro (SupportQuotientPairMap.id P) =
          (ProEtale.supportSiteProEtaleComparisonId
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) P.T).hom.app
              (proEtaleSupportQuotient A P.a)) ∧
      (∀ {P Q R : SupportQuotientPair.{u}} (g : SupportQuotientPairMap P Q)
          (f : SupportQuotientPairMap Q R),
        cEt (g.comp f) =
          (ProEtale.supportSiteEtaleComparisonComp
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g.f f.f).hom.app
              (etaleSupportQuotient A R.a) ≫
            (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g.f).map (cEt f) ≫
              cEt g ∧
        cPro (g.comp f) =
          (ProEtale.supportSiteProEtaleComparisonComp
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g.f f.f).hom.app
              (proEtaleSupportQuotient A R.a) ≫
            (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g.f).map
              (cPro f) ≫ cPro g) ∧
      (∀ {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q)
          (α : (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Q.T).obj
              (etaleSupportQuotient A Q.a) ≅ proEtaleSupportQuotient A Q.a)
          (α' : (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) P.T).obj
              (etaleSupportQuotient A P.a) ≅ proEtaleSupportQuotient A P.a),
        (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Q.T).map
              (etaleSupportQuotientMap A Q.a) ≫ α.hom =
          supportQuotientConstantComparison A (T := Q.T) ≫
            proEtaleSupportQuotientMap A Q.a →
        (ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) P.T).map
              (etaleSupportQuotientMap A P.a) ≫ α'.hom =
          supportQuotientConstantComparison A (T := P.T) ≫
            proEtaleSupportQuotientMap A P.a →
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).map α.hom ≫
            cPro f =
          (ProEtale.supportSiteComparisonCoefficientPullbackIso
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f.f).inv.app
              (etaleSupportQuotient A Q.a) ≫
            (ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) P.T).map (cEt f) ≫ α'.hom) := by
  classical
  let cEt : EtaleSupportQuotientPairMaps A := fun f ↦ (etale_pair_exists A f).choose
  have hcEt {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q) :=
    (etale_pair_exists A f).choose_spec
  let α (P : SupportQuotientPair.{u}) :=
    (supportQuotient_flat_kflat_stalk_comparison A P.a).2.2.2.2.2.choose
  have hα (P : SupportQuotientPair.{u}) :=
    (supportQuotient_flat_kflat_stalk_comparison A P.a).2.2.2.2.2.choose_spec.1
  let cPro : ProEtaleSupportQuotientPairMaps A := fun {P Q} f ↦
    (proetale_pair_transport A f (cEt f) (hcEt f) (α Q) (α P) (hα Q) (hα P)).choose
  have hcPro {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q) :=
    (proetale_pair_transport A f (cEt f) (hcEt f) (α Q) (α P) (hα Q) (hα P)).choose_spec
  have epiEt {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q) :
      Epi ((Etale.upperStar (Coeff A) f.f).map (etaleSupportQuotientMap A Q.a)) := by
    have := etale_quotient_epi A Q
    infer_instance
  have epiPro {P Q : SupportQuotientPair.{u}} (f : SupportQuotientPairMap P Q) :
      Epi ((ProEtale.upperStar (Coeff A) f.f).map (proEtaleSupportQuotientMap A Q.a)) := by
    have := proetale_quotient_epi A Q
    infer_instance
  refine ⟨cEt, cPro, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P Q f
    refine ⟨hcEt f, fun d hd ↦ ?_⟩
    have := epiEt f
    exact (cancel_epi _).mp (hd.trans (hcEt f).symm)
  · intro P Q f
    refine ⟨(hcPro f).1, fun d hd ↦ ?_⟩
    have := epiPro f
    exact (cancel_epi _).mp (hd.trans (hcPro f).1.symm)
  · intro P Q f Ω _ _ t
    refine ⟨fun ht ↦ etale_stalk_on_support A f t ht (cEt f) (hcEt f), ?_⟩
    intro ht
    have hz := ((supportQuotient_flat_kflat_stalk_comparison A P.a).2.2.2.2.1
      Ω t).2 ht
    exact ⟨hz, hz.eq_of_tgt _ _⟩
  · intro P Q f hf
    have hi := etale_pair_isIso A f (cEt f) (hcEt f) hf
    exact ⟨hi, (hcPro f).2.2 hi⟩
  · intro P
    constructor
    · have : Epi ((Etale.upperStar (Coeff A) (𝟙 P.T)).map
          (etaleSupportQuotientMap A P.a)) := epiEt (SupportQuotientPairMap.id P)
      apply (cancel_epi ((Etale.upperStar (Coeff A) (𝟙 P.T)).map
        (etaleSupportQuotientMap A P.a))).mp
      erw [hcEt (SupportQuotientPairMap.id P)]
      change _ = (Etale.upperStar (Coeff A) (𝟙 P.T)).map (etaleSupportQuotientMap A P.a) ≫ _
      erw [(ProEtale.supportSiteEtaleComparisonId (Coeff A) P.T).hom.naturality]
      simp only [SupportQuotientPairMap.id, Functor.id_obj, Functor.id_map,
        etale_constant_id A P.T]
    · have : Epi ((ProEtale.upperStar (Coeff A) (𝟙 P.T)).map
          (proEtaleSupportQuotientMap A P.a)) := epiPro (SupportQuotientPairMap.id P)
      apply (cancel_epi ((ProEtale.upperStar (Coeff A) (𝟙 P.T)).map
        (proEtaleSupportQuotientMap A P.a))).mp
      erw [(hcPro (SupportQuotientPairMap.id P)).1]
      change _ = (ProEtale.upperStar (Coeff A) (𝟙 P.T)).map (proEtaleSupportQuotientMap A P.a) ≫ _
      erw [(ProEtale.supportSiteProEtaleComparisonId (Coeff A) P.T).hom.naturality]
      simp only [SupportQuotientPairMap.id, Functor.id_obj, Functor.id_map,
        proetale_constant_id A P.T]
  · intro P Q R g f
    constructor
    · have : Epi ((Etale.upperStar (Coeff A) (g.f ≫ f.f)).map
          (etaleSupportQuotientMap A R.a)) := epiEt (g.comp f)
      apply (cancel_epi ((Etale.upperStar (Coeff A) (g.f ≫ f.f)).map
        (etaleSupportQuotientMap A R.a))).mp
      erw [hcEt (g.comp f)]
      change _ = (Etale.upperStar (Coeff A) (g.f ≫ f.f)).map
        (etaleSupportQuotientMap A R.a) ≫ _
      change (Etale.constantSheafCompUpperStarIso (ULift.{u + 1, u} A)
          (g.f ≫ f.f)).hom.app (unitCoeff A) ≫ etaleSupportQuotientMap A P.a = _
      have hn := (ProEtale.supportSiteEtaleComparisonComp (Coeff A) g.f f.f).hom.naturality
        (etaleSupportQuotientMap A R.a)
      change (Etale.upperStar (Coeff A) (g.f ≫ f.f)).map (etaleSupportQuotientMap A R.a) ≫
          (ProEtale.supportSiteEtaleComparisonComp (Coeff A) g.f f.f).hom.app
            (etaleSupportQuotient A R.a) =
        (ProEtale.supportSiteEtaleComparisonComp (Coeff A) g.f f.f).hom.app
            ((constantSheaf (R.T.smallEtaleTopology) (Coeff A)).obj (unitCoeff A)) ≫
          (Etale.upperStar (Coeff A) g.f).map
            ((Etale.upperStar (Coeff A) f.f).map (etaleSupportQuotientMap A R.a)) at hn
      rw [← Category.assoc, ← Category.assoc, hn]
      simp only [Category.assoc]
      change _ = _ ≫ (Etale.upperStar (Coeff A) g.f).map
        ((Etale.upperStar (Coeff A) f.f).map (etaleSupportQuotientMap A R.a)) ≫ _
      rw [← (Etale.upperStar (Coeff A) g.f).map_comp_assoc]
      erw [hcEt f]
      rw [(Etale.upperStar (Coeff A) g.f).map_comp]
      simp only [Category.assoc]
      erw [hcEt g]
      rw [etale_constant_comp A g.f f.f]
      simp only [Category.assoc]
    · have : Epi ((ProEtale.upperStar (Coeff A) (g.f ≫ f.f)).map
          (proEtaleSupportQuotientMap A R.a)) := epiPro (g.comp f)
      apply (cancel_epi ((ProEtale.upperStar (Coeff A) (g.f ≫ f.f)).map
        (proEtaleSupportQuotientMap A R.a))).mp
      erw [(hcPro (g.comp f)).1]
      change _ = (ProEtale.upperStar (Coeff A) (g.f ≫ f.f)).map
        (proEtaleSupportQuotientMap A R.a) ≫ _
      change proEtaleConstantInverseImageMap (g.f ≫ f.f) (Coeff A) (unitCoeff A) ≫
        proEtaleSupportQuotientMap A P.a = _
      have hn := (ProEtale.supportSiteProEtaleComparisonComp (Coeff A) g.f f.f).hom.naturality
        (proEtaleSupportQuotientMap A R.a)
      change (ProEtale.upperStar (Coeff A) (g.f ≫ f.f)).map (proEtaleSupportQuotientMap A R.a) ≫
          (ProEtale.supportSiteProEtaleComparisonComp (Coeff A) g.f f.f).hom.app
            (proEtaleSupportQuotient A R.a) =
        (ProEtale.supportSiteProEtaleComparisonComp (Coeff A) g.f f.f).hom.app
            ((constantSheaf (ProEt.topology R.T) (Coeff A)).obj (unitCoeff A)) ≫
          (ProEtale.upperStar (Coeff A) g.f).map
            ((ProEtale.upperStar (Coeff A) f.f).map (proEtaleSupportQuotientMap A R.a)) at hn
      rw [← Category.assoc, ← Category.assoc, hn]
      simp only [Category.assoc]
      change _ = _ ≫ (ProEtale.upperStar (Coeff A) g.f).map
        ((ProEtale.upperStar (Coeff A) f.f).map (proEtaleSupportQuotientMap A R.a)) ≫ _
      rw [← (ProEtale.upperStar (Coeff A) g.f).map_comp_assoc]
      erw [(hcPro f).1]
      rw [(ProEtale.upperStar (Coeff A) g.f).map_comp]
      simp only [Category.assoc]
      erw [(hcPro g).1]
      rw [proetale_constant_comp A g.f f.f]
      simp only [Category.assoc]
  · intro P Q f β β' hβ hβ'
    have hQ : β = α Q :=
      (supportQuotient_flat_kflat_stalk_comparison A Q.a).2.2.2.2.2.choose_spec.2 β hβ
    have hP : β' = α P :=
      (supportQuotient_flat_kflat_stalk_comparison A P.a).2.2.2.2.2.choose_spec.2 β' hβ'
    subst β
    subst β'
    exact (hcPro f).2.1


end AlgebraicGeometry.Scheme
