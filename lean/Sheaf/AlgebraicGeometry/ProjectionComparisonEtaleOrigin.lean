/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import all Sheaf.SixFunctors.ComparisonOpenTensorCoherence
import all Sheaf.Paper.CompactSupportExchangeTransport
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
import Sheaf.Paper.DerivedSquarePasting
import all Sheaf.Paper.SpDirectImageEtaleMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula

/-!
# Etale-origin comparison of compact-support projection maps

Source: main-20261015 blueprint, sec-six-functors-basics/sk-prop-cohsm,
first paragraph of thm-pur-cohomological-smoothness.proof.md; Stacks Tags 0E48,
09AF and 0GL1 (blueprint: lem-pur-projection-comparison-etale-origin).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Finiteness of the positive-level coefficient quotient, from the recorded coefficient
extension theorem. Source: Serre, Local Fields, II, section 2
(blueprint: def-smooth-purity-projection-comparison-equation). -/
instance projectionComparisonCoefficient_finite
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)] :
    Finite (Padic.coefficientExtensionRing l E n) :=
  Padic.finite_coefficientExtensionRing l E n (Fact.out : 1 ≤ n)

/-- The derived pullback comparison used in the target transport.
Source: Stacks Tag 099R
(blueprint: def-smooth-purity-projection-comparison-equation). -/
noncomputable def projectionComparisonPullbackIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).leftDerivedFunctorIsoMapDerivedCategory.symm
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ≪≫
    Functor.leftDerivedFunctorCompNatIso
      (Etale.upperStar (ModuleCat.{u + 1} A) f)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f)
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f) ≪≫
    Functor.isoWhiskerLeft
      (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).leftDerivedFunctorIsoMapDerivedCategory

/-- The canonical target transport from the comparison of pullback and tensor.
Source: Stacks Tags 07A4 and 099R (blueprint: def-smooth-purity-projection-comparison-equation). -/
noncomputable def projectionComparisonTargetIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj H)) ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H)) := by
  exact
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)).mapIso
      (asIso ((projectionComparisonPullbackIso A f).hom.app H)) ≪≫
    ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) M).app
      ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H)).symm

/-- Tensor target used in the bounded-below witness.
Source: main-20261015 blueprint (blueprint: def-smooth-purity-projection-comparison-equation). -/
noncomputable def projectionComparisonTensor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) :=
  (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H))

/-- The asserted equality, with every target identification written explicitly.
The left route is PF-pro, P of the specified target identification, then C at the tensor.
The right route is C at M tensor identity, the inverse comparison tensor map, then V(PF-et).
Source: Stacks Tag 0E48 and the blueprint projection comparison, displayed equation
(blueprint: def-smooth-purity-projection-comparison-equation). -/
@[irreducible] def ProjectionComparisonEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y)
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (hD : _root_.DerivedCategory.TStructure.t.plus
      (projectionComparisonTensor A (f := f) M H)) : Prop :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj H) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (projectionComparisonTargetIso A f M H).hom ≫
      (compactSupportSiteComparison A c).hom.app
        ⟨((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H), hD⟩ =
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map
      ((compactSupportSiteComparison A c).hom.app ⟨M, hM⟩)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj H) ≫
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A)
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj M)).inv.app H) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        (((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app H)

/-- The full existential conclusion of the etale-origin comparison statement.
Source: main-20261015 blueprint, thm-pur-cohomological-smoothness.proof.md
(blueprint: def-smooth-purity-projection-comparison-equation). -/
@[irreducible] def projectionComparisonConclusion
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (M : Etale.DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (H : Etale.DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y)
    (_hM : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) X M)
    (_hH : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) Y H)
    (_hTor : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn
      (Padic.coefficientExtensionRing l E n) Y a b H) : Prop :=
  ∃ (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (hD : _root_.DerivedCategory.TStructure.t.plus
      (projectionComparisonTensor (Padic.coefficientExtensionRing l E n) (f := f) M H)),
    ProjectionComparisonEquation (Padic.coefficientExtensionRing l E n) c M H hM hD



attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryNatIso
  Functor.sheafPullbackConstruction.sheafPullback
  conjugateIsoEquiv Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
  Functor.sheafPushforwardContinuousComp'
  supportSiteComparisonCoefficientPullbackIso comparisonCoefficientPullbackIso
  Etale.upperStarComp upperStarComp

section ExactTriangle

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category D₀] [Category D₁] [Category D₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian D₀] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (F₀ : C₀ ⥤ C₂)
  (P : D₀ ⥤ D₁) (Q : D₁ ⥤ D₂) (P₀ : D₀ ⥤ D₂)
  (E₀ : C₀ ⥤ D₀) (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
  [F.Additive] [G.Additive] [F₀.Additive]
  [P.Additive] [Q.Additive] [P₀.Additive]
  [E₀.Additive] [E₁.Additive] [E₂.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits P₀] [PreservesFiniteColimits P₀]
  [PreservesFiniteLimits E₀] [PreservesFiniteColimits E₀]
  [PreservesFiniteLimits E₁] [PreservesFiniteColimits E₁]
  [PreservesFiniteLimits E₂] [PreservesFiniteColimits E₂]

private theorem exact_comparison_triangle
    (ce : F₀ ≅ F ⋙ G) (cp : P₀ ≅ P ⋙ Q)
    (a : F ⋙ E₁ ≅ E₀ ⋙ P) (b : G ⋙ E₂ ≅ E₁ ⋙ Q)
    (c : F₀ ⋙ E₂ ≅ E₀ ⋙ P₀)
    (h : ∀ K, E₂.map (ce.hom.app K) ≫ b.hom.app (F.obj K) ≫
      Q.map (a.hom.app K) = c.hom.app K ≫ cp.hom.app (E₀.obj K)) :
    (Functor.isoWhiskerRight (Functor.mapDerivedCategoryTriangleIso ce) D(E₂)).hom ≫
      (Functor.isoWhiskerLeft D(F) (Functor.mapDerivedCategorySquareIso b)).hom ≫
      (Functor.isoWhiskerRight (Functor.mapDerivedCategorySquareIso a) D(Q)).hom =
    (Functor.mapDerivedCategorySquareIso c).hom ≫
      (Functor.isoWhiskerLeft D(E₀) (Functor.mapDerivedCategoryTriangleIso cp)).hom := by
  have hp := Functor.mapDerivedCategorySquareIso_paste F G P Q E₀ E₁ E₂ a b
  have hi : Functor.isoWhiskerRight ce E₂ ≪≫ Functor.isoWhiskerLeft F b ≪≫
      Functor.isoWhiskerRight a Q = c ≪≫ Functor.isoWhiskerLeft E₀ cp := by
    apply Iso.ext
    apply NatTrans.ext
    funext K
    exact h K
  have hn := congrArg (fun t ↦ (Functor.mapDerivedCategoryNatIso t).hom) hi
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hn
  have hr := Functor.mapDerivedCategoryNatIso_isoWhiskerRight ce E₂
  have hl := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft E₀ cp
  have hp' := congrArg (fun t ↦ t ≫
    (Functor.isoWhiskerLeft D(E₀) (Functor.mapDerivedCategoryCompIso P Q)).hom) hp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hp'
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_comp, Category.assoc] at hp' ⊢
  rw [← hp']
  simp only [Iso.symm_hom]
  apply (cancel_epi (Functor.mapDerivedCategoryCompIso F₀ E₂).hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← reassoc_of% hr]
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    Functor.mapDerivedCategoryNatIso_trans]
  rw [reassoc_of% hn]
  simp only [Functor.isoWhiskerLeft_hom, Iso.trans_hom,
    Functor.whiskerLeft_comp]
  rw [← reassoc_of% hl]

end ExactTriangle

section TransportTriangle

variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category D₀] [Category D₁] [Category D₂]
  {F₀ LF₀ : C₀ ⥤ C₂} {F LF : C₀ ⥤ C₁} {G LG : C₁ ⥤ C₂}
  {P₀ LP₀ : D₀ ⥤ D₂} {P LP : D₀ ⥤ D₁} {Q LQ : D₁ ⥤ D₂}
  (E₀ : C₀ ⥤ D₀) (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)

private theorem transport_triangle
    (e₀ : LF₀ ≅ F₀) (e₁ : LF ≅ F) (e₂ : LG ≅ G)
    (p₀ : LP₀ ≅ P₀) (p₁ : LP ≅ P) (p₂ : LQ ≅ Q)
    (a : F ⋙ E₁ ≅ E₀ ⋙ P) (b : G ⋙ E₂ ≅ E₁ ⋙ Q)
    (d : F₀ ⋙ E₂ ≅ E₀ ⋙ P₀) (ce : F₀ ≅ F ⋙ G) (cp : P₀ ≅ P ⋙ Q)
    (H : C₀)
    (h : E₂.map (ce.hom.app H) ≫ b.hom.app (F.obj H) ≫ Q.map (a.hom.app H) =
      d.hom.app H ≫ cp.hom.app (E₀.obj H)) :
    E₂.map (e₀.hom.app H ≫ ce.hom.app H ≫ G.map (e₁.inv.app H) ≫
        e₂.inv.app (LF.obj H)) ≫
      (E₂.map (e₂.hom.app _) ≫ b.hom.app _ ≫ p₂.inv.app _) ≫
      LQ.map (E₁.map (e₁.hom.app H) ≫ a.hom.app H ≫ p₁.inv.app (E₀.obj H)) =
    (E₂.map (e₀.hom.app H) ≫ d.hom.app H ≫ p₀.inv.app _) ≫
      (p₀.hom.app _ ≫ cp.hom.app (E₀.obj H) ≫ Q.map (p₁.inv.app _) ≫ p₂.inv.app _) := by
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← E₂.map_comp_assoc (e₂.inv.app _), Iso.inv_hom_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← p₂.inv.naturality_assoc, ← p₂.inv.naturality_assoc, ← p₂.inv.naturality]
  have hb := b.hom.naturality (e₁.inv.app H)
  dsimp only [Functor.comp_map] at hb
  rw [reassoc_of% hb]
  rw [← Q.map_comp_assoc (E₁.map (e₁.inv.app H)), ← E₁.map_comp,
    Iso.inv_hom_id_app, E₁.map_id, Q.map_id, Category.id_comp]
  rw [reassoc_of% h]

private theorem inverse_square {T : Type*} [Category T] {W X Y Z : T}
    (e : W ≅ X) (p : Y ≅ Z) (a : X ⟶ Z) (b : W ⟶ Y)
    (h : e.hom ≫ a = b ≫ p.hom) : e.inv ≫ b = a ≫ p.inv := by
  apply (cancel_epi e.hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem tensor_square {C D : Type*} [Category C] [Category D]
    (V : C ⥤ D) (T : C ⥤ C) (P : D ⥤ D) (t : T ⋙ V ≅ V ⋙ P)
    {K L : C} {U W : D} (q : K ⟶ L) (a : V.obj L ⟶ W)
    (b : V.obj K ⟶ U) (r : U ⟶ W) (h : V.map q ≫ a = b ≫ r) :
    V.map (T.map q) ≫ (t.hom.app L ≫ P.map a) =
      (t.hom.app K ≫ P.map b) ≫ P.map r := by
  have hn := t.hom.naturality q
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← P.map_comp, h]

private theorem tensor_iso_square {C D : Type*} [Category C] [Category D]
    (V : C ⥤ D) (T : C ⥤ C) (P : D ⥤ D) (t : T ⋙ V ≅ V ⋙ P)
    {K L : C} {U W : D} (q : K ≅ L) (a : V.obj L ≅ W)
    (b : V.obj K ≅ U) (r : U ≅ W) (h : V.mapIso q ≪≫ a = b ≪≫ r) :
    V.mapIso (T.mapIso q) ≪≫ (t.app L ≪≫ P.mapIso a) =
      (t.app K ≪≫ P.mapIso b) ≪≫ P.mapIso r := by
  apply Iso.ext
  have hh := congrArg Iso.hom h
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hh
  simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    using tensor_square V T P t q.hom a.hom b.hom r.hom hh

private theorem inverse_projection_arrows {C : Type*} [Category C]
    {A B D E F G : C} (pe : A ⟶ B) (pp : F ⟶ G)
    (i : F ⟶ E) (ii : E ⟶ F) (j : D ⟶ B) (jj : B ⟶ D)
    (t : A ⟶ E) (tt : E ⟶ A) (s : D ⟶ G) (ss : G ⟶ D)
    (hi : i ≫ ii = 𝟙 F) (ht : tt ≫ t = 𝟙 E)
    (hs : s ≫ ss = 𝟙 D) (hj : jj ≫ j = 𝟙 B)
    (h : pe ≫ jj ≫ s = t ≫ ii ≫ pp) :
    pp ≫ ss ≫ j = i ≫ tt ≫ pe := by
  have hz := congrArg (fun z ↦ i ≫ tt ≫ z ≫ ss ≫ j) h
  simpa only [Category.assoc, reassoc_of% hi, reassoc_of% ht, reassoc_of% hs, hj,
    Category.id_comp, Category.comp_id] using hz.symm


private theorem append_map {C D : Type*} [Category C] [Category D]
    (P : C ⥤ D) {A : D} {B E F : C} (u : A ⟶ P.obj B) (v : B ⟶ E) (w : E ⟶ F) :
    u ≫ P.map v ≫ P.map w = u ≫ P.map (v ≫ w) := by
  rw [P.map_comp]

private theorem paste_projection_square
    {E F C D : Type*} [Category E] [Category F] [Category C] [Category D]
    (V : C ⥤ D) (Re : E ⥤ C) (Rp : F ⥤ D) (W : E ⥤ F)
    (B : Re ⋙ V ⟶ W ⋙ Rp)
    {a b : E} {j t u v : F} {x : C} {s s₂ s₃ : D}
    (ge : a ⟶ b) (ed : W.obj b ⟶ j) (hf : j ⟶ t)
    (d : W.obj a ⟶ u) (em : u ⟶ v) (gp : v ⟶ t)
    (pe : x ⟶ Re.obj a) (tt : V.obj x ⟶ s)
    (bm : s ⟶ s₂) (ee : s₂ ⟶ s₃) (pp₂ : s₂ ⟶ Rp.obj u) (pp : s₃ ⟶ Rp.obj v)
    (pfet : x ⟶ Re.obj b) (pfp : s₃ ⟶ Rp.obj t)
    (bd : V.obj (Re.obj b) ⟶ Rp.obj j) (bM : s ⟶ s₃)
    (hfe : pfet = pe ≫ Re.map ge) (hfp : pfp = pp ≫ Rp.map gp)
    (hbd : bd = B.app b ≫ Rp.map ed) (hbm : bM = bm ≫ ee)
    (ho : W.map ge ≫ ed ≫ hf = d ≫ em ≫ gp)
    (hp : V.map pe ≫ B.app a ≫ Rp.map d = tt ≫ bm ≫ pp₂)
    (hn : ee ≫ pp = pp₂ ≫ Rp.map em) :
    V.map pfet ≫ bd ≫ Rp.map hf = tt ≫ bM ≫ pfp := by
  have he := B.naturality ge
  dsimp only [Functor.comp_map] at he
  rw [hfe, hfp, hbd, hbm]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% he]
  simp only [← Rp.map_comp]
  rw [ho]
  simp only [Rp.map_comp]
  rw [reassoc_of% hp, ← reassoc_of% hn]

private theorem paste_open_square
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (W : E ⥤ F) (Je : C ⥤ E) (Jp : D ⥤ F) (V : C ⥤ D)
    (e : Je ⋙ W ⟶ V ⋙ Jp)
    {a b : C} {x : E} {k l w : D} {s s₀ v z : F}
    (ge : x ⟶ Je.obj a) (q : a ⟶ b) (hf : V.obj b ⟶ k)
    (hfi : V.obj a ⟶ l) (r : l ⟶ w) (cp : w ⟶ k)
    (d₀ : W.obj x ⟶ s) (em₀ : s ⟶ s₀) (gp₀ : s₀ ⟶ Jp.obj l)
    (rl : s ⟶ v) (rr : s₀ ⟶ z) (em : v ⟶ z) (gp : z ⟶ Jp.obj w)
    (ho : W.map ge ≫ e.app a ≫ Jp.map hfi = d₀ ≫ em₀ ≫ gp₀)
    (ht : V.map q ≫ hf = hfi ≫ r ≫ cp)
    (hg : gp₀ ≫ Jp.map r = rr ≫ gp)
    (hb : em₀ ≫ rr = rl ≫ em) :
    W.map (ge ≫ Je.map q) ≫ e.app b ≫ Jp.map hf =
      (d₀ ≫ rl) ≫ em ≫ (gp ≫ Jp.map cp) := by
  have he := e.naturality q
  dsimp only [Functor.comp_map] at he
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% he]
  simp only [← Jp.map_comp]
  rw [ht]
  simp only [Jp.map_comp]
  rw [reassoc_of% ho, reassoc_of% hg, reassoc_of% hb]

end TransportTriangle

private theorem bounded_of_constructible
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (M : Etale.DerivedCategoryModule A X)
    (hM : Etale.DerivedCategory.isBoundedConstructible A X M) :
    _root_.DerivedCategory.TStructure.t.bounded M := by
  obtain ⟨r, s, _hrs, hbound⟩ := hM.2
  exact ⟨⟨r, (_root_.DerivedCategory.isGE_iff M r).2
      (fun i hi ↦ hbound i (Or.inl hi))⟩,
     ⟨s, (_root_.DerivedCategory.isLE_iff M s).2
      (fun i hi ↦ hbound i (Or.inr hi))⟩⟩

private theorem plus_tensor_of_tor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y)
    (hM : _root_.DerivedCategory.TStructure.t.bounded M)
    (hH : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn A Y a b H) :
    _root_.DerivedCategory.TStructure.t.plus (projectionComparisonTensor A (f := f) M H) := by
  obtain ⟨a, b, ht⟩ := hH
  exact Etale.plus_derivedTensor_leftDerivedUpperStar f hM
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht)

private theorem proper_comparison_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).map
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
      (spDirectImageComparisonIso A f K.obj K.property).hom =
    (rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} A)).hom.app K := by
  simp only [spDirectImageComparisonIso, rightDerivedLowerStarComparisonIso',
    rightDerivedLowerStarComparisonPlusIso, Functor.mapDerivedCategoryPlusCompatibility,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, asIso_hom,
    fixedComparisonDirectImageMatePlus]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

private theorem compact_comparison_inv
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (compactSupportSiteComparison A c).inv.app K =
      (spDirectImageComparisonIso A c.g
        (D(Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj K.obj)
        ((D+(Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)).obj K).property).hom ≫
      R(lowerStar (ModuleCat.{u + 1} A) c.g).map
        ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} A) c.i).hom.app K.obj) := by
  have h := compactComparison_hom A c K
  have he : (compactExchangeTransportComparison A c).hom.app K =
      D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) c).hom.app K) ≫
        (compactSupportSiteComparison A c).inv.app K := by
    simp only [compactExchangeTransportComparison, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp]
  rw [he] at h
  apply (cancel_epi (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).map
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).hom.app K))).1
  rw [h]
  rw [← Category.assoc]
  erw [← proper_comparison_normalization A c.g
    ((D+(Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)).obj K)]
  congr 1
  simp only [Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Functor.mapDerivedCategoryPlusCompatibility,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp, Category.comp_id,
    Functor.map_comp, CategoryTheory.Functor.map_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

attribute [local implicit_reducible] upperStar Etale.upperStar comparisonUpperStar

private theorem support_comparison_eq
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}} (h : U ⟶ V) :
    @Eq (Etale.upperStar (ModuleCat.{u + 1} A) h ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) U ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) V ⋙ upperStar (ModuleCat.{u + 1} A) h)
      (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) h)
      (comparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) h) := by
  rw [supportComparison_eq]
  unfold comparisonCoefficientPullbackIso
  rfl

private theorem etale_composition_eq
    (A : Type (u + 1)) [CommRing A]
    {X Z Y : Scheme.{u}} (i : X ⟶ Z) (g : Z ⟶ Y) :
    @Eq (Etale.upperStar (ModuleCat.{u + 1} A) (i ≫ g) ≅
      Etale.upperStar (ModuleCat.{u + 1} A) g ⋙ Etale.upperStar (ModuleCat.{u + 1} A) i)
      (Etale.upperStarComp (ModuleCat.{u + 1} A) i g)
      (etaleComparisonComp (ModuleCat.{u + 1} A) i g) := by
  unfold Etale.upperStarComp etaleComparisonComp Etale.lowerStarComp
  rfl

private theorem proetale_composition_eq
    (A : Type (u + 1)) [CommRing A]
    {X Z Y : Scheme.{u}} (i : X ⟶ Z) (g : Z ⟶ Y) :
    @Eq (upperStar (ModuleCat.{u + 1} A) (i ≫ g) ≅
      upperStar (ModuleCat.{u + 1} A) g ⋙ upperStar (ModuleCat.{u + 1} A) i)
      (upperStarComp (ModuleCat.{u + 1} A) i g)
      (proEtaleComparisonComp (ModuleCat.{u + 1} A) i g) := by
  unfold upperStarComp proEtaleComparisonComp lowerStarComp
  rfl

private theorem comparison_pullback_hom
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : Etale.DerivedCategoryModule A Y) :
    (comparisonOpenDerivedPullbackIso A f).hom.app H =
      D(comparisonUpperStar (ModuleCat.{u + 1} A) X).map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) f).hom.app H) ≫
      (Functor.mapDerivedCategorySquareIso
        (F₁ := Etale.upperStar (ModuleCat.{u + 1} A) f)
        (F₂ := comparisonUpperStar (ModuleCat.{u + 1} A) X)
        (G₁ := comparisonUpperStar (ModuleCat.{u + 1} A) Y)
        (G₂ := upperStar (ModuleCat.{u + 1} A) f)
        (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) f)).hom.app H ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).inv.app
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj H) := by
  simp only [comparisonOpenDerivedPullbackIso, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc]

private theorem comparison_pullback_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (i : X ⟶ Z) (g : Z ⟶ Y)
    (H : Etale.DerivedCategoryModule A Y) :
    D(comparisonUpperStar (ModuleCat.{u + 1} A) X).map
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i g).hom.app H) ≫
      (comparisonOpenDerivedPullbackIso A i).hom.app
        (L(Etale.upperStar (ModuleCat.{u + 1} A) g).obj H) ≫
      L(upperStar (ModuleCat.{u + 1} A) i).map
        ((comparisonOpenDerivedPullbackIso A g).hom.app H) =
    (comparisonOpenDerivedPullbackIso A (i ≫ g)).hom.app H ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i g).hom.app
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj H) := by
  have hd₀ := exact_comparison_triangle
    (Etale.upperStar (ModuleCat.{u + 1} A) g) (Etale.upperStar (ModuleCat.{u + 1} A) i)
      (Etale.upperStar (ModuleCat.{u + 1} A) (i ≫ g))
    (upperStar (ModuleCat.{u + 1} A) g) (upperStar (ModuleCat.{u + 1} A) i)
      (upperStar (ModuleCat.{u + 1} A) (i ≫ g))
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y) (comparisonUpperStar (ModuleCat.{u + 1} A) Z)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (Etale.upperStarComp (ModuleCat.{u + 1} A) i g) (upperStarComp (ModuleCat.{u + 1} A) i g)
    (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) g)
    (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) i)
    (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) (i ≫ g)) (fun K ↦ by
      simpa only [support_comparison_eq, etale_composition_eq, proetale_composition_eq,
        comparisonCoefficientPullback,
        etaleComparisonPullback, proEtaleComparisonPullback,
        Etale.upperStar, upperStar, comparisonUpperStar,
        Scheme.smallEtaleTopology] using
        ((supportSiteComparison_pullback_coherent.2.2 A).2.1 X Z Y i g K))
  have hd := congr_app hd₀ H
  simp only [NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hd
  let VX := D(comparisonUpperStar (ModuleCat.{u + 1} A) X)
  let VZ := D(comparisonUpperStar (ModuleCat.{u + 1} A) Z)
  let VY := D(comparisonUpperStar (ModuleCat.{u + 1} A) Y)
  let Ei := D(Etale.upperStar (ModuleCat.{u + 1} A) i)
  let Pi := L(upperStar (ModuleCat.{u + 1} A) i)
  let Di := D(upperStar (ModuleCat.{u + 1} A) i)
  let e₀ := Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (i ≫ g)
  let e₁ := Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g
  let e₂ := Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) i
  let p₀ := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (i ≫ g)
  let p₁ := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g
  let p₂ := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) i
  let a := Functor.mapDerivedCategorySquareIso
    (F₁ := Etale.upperStar (ModuleCat.{u + 1} A) g)
      (F₂ := comparisonUpperStar (ModuleCat.{u + 1} A) Z)
    (G₁ := comparisonUpperStar (ModuleCat.{u + 1} A) Y) (G₂ := upperStar (ModuleCat.{u + 1} A) g)
    (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) g)
  let b := Functor.mapDerivedCategorySquareIso
    (F₁ := Etale.upperStar (ModuleCat.{u + 1} A) i)
      (F₂ := comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (G₁ := comparisonUpperStar (ModuleCat.{u + 1} A) Z) (G₂ := upperStar (ModuleCat.{u + 1} A) i)
    (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) i)
  let d := Functor.mapDerivedCategorySquareIso
    (F₁ := Etale.upperStar (ModuleCat.{u + 1} A) (i ≫ g))
      (F₂ := comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (G₁ := comparisonUpperStar (ModuleCat.{u + 1} A) Y) (G₂ := upperStar (ModuleCat.{u + 1} A)
      (i ≫ g))
    (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) (i ≫ g))
  let ce := Functor.mapDerivedCategoryTriangleIso (Etale.upperStarComp (ModuleCat.{u + 1} A) i g)
  let cp := Functor.mapDerivedCategoryTriangleIso (upperStarComp (ModuleCat.{u + 1} A) i g)
  rw [Etale.leftDerivedUpperStarComp_hom_app, leftDerivedUpperStarComp_hom_app]
  simp only [comparison_pullback_hom]
  change VX.map (e₀.hom.app H ≫ ce.hom.app H ≫ Ei.map (e₁.inv.app H) ≫
      e₂.inv.app (L(Etale.upperStar (ModuleCat.{u + 1} A) g).obj H)) ≫
    (VX.map (e₂.hom.app _) ≫ b.hom.app _ ≫ p₂.inv.app _) ≫
    Pi.map (VZ.map (e₁.hom.app H) ≫ a.hom.app H ≫ p₁.inv.app (VY.obj H)) =
    (VX.map (e₀.hom.app H) ≫ d.hom.app H ≫ p₀.inv.app _) ≫
    (p₀.hom.app _ ≫ cp.hom.app (VY.obj H) ≫ Di.map (p₁.inv.app _) ≫ p₂.inv.app _)
  exact transport_triangle VY VZ VX e₀ e₁ e₂ p₀ p₁ p₂ a b d ce cp H hd


attribute [local irreducible] comparisonOpenDerivedPullbackIso
  Etale.leftDerivedUpperStarComp leftDerivedUpperStarComp

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem comparison_pullback_comp_nat
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (i : X ⟶ Z) (g : Z ⟶ Y) :
    Functor.whiskerRight (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      i g).hom D(comparisonUpperStar (ModuleCat.{u + 1} A) X) ≫
      Functor.whiskerLeft L(Etale.upperStar (ModuleCat.{u + 1} A) g)
        (comparisonOpenDerivedPullbackIso A i).hom ≫
      Functor.whiskerRight (comparisonOpenDerivedPullbackIso A g).hom
        L(upperStar (ModuleCat.{u + 1} A) i) =
    (comparisonOpenDerivedPullbackIso A (i ≫ g)).hom ≫
      Functor.whiskerLeft D(comparisonUpperStar (ModuleCat.{u + 1} A) Y)
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i g).hom := by
  apply NatTrans.ext
  funext H
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj]
    using comparison_pullback_comp A i g H

private theorem comparison_pullback_compactification_nat
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Functor.whiskerRight (Etale.leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom
        D(comparisonUpperStar (ModuleCat.{u + 1} A) X) ≫
      (comparisonOpenDerivedPullbackIso A f).hom =
    Functor.whiskerLeft L(Etale.upperStar (ModuleCat.{u + 1} A) c.g)
      (comparisonOpenDerivedPullbackIso A c.i).hom ≫
      Functor.whiskerRight (comparisonOpenDerivedPullbackIso A c.g).hom
        L(upperStar (ModuleCat.{u + 1} A) c.i) ≫
      Functor.whiskerLeft D(comparisonUpperStar (ModuleCat.{u + 1} A) Y)
        (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom := by
  rcases c with ⟨Z, g, i, comm, hg, hi⟩
  subst f
  have h := comparison_pullback_comp_nat A i g
  have h' := inverse_square
    (Functor.isoWhiskerRight (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i g)
      D(comparisonUpperStar (ModuleCat.{u + 1} A) X))
    (Functor.isoWhiskerLeft D(comparisonUpperStar (ModuleCat.{u + 1} A) Y)
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i g))
    (Functor.whiskerLeft L(Etale.upperStar (ModuleCat.{u + 1} A) g)
      (comparisonOpenDerivedPullbackIso A i).hom ≫
      Functor.whiskerRight (comparisonOpenDerivedPullbackIso A g).hom
        L(upperStar (ModuleCat.{u + 1} A) i))
    (comparisonOpenDerivedPullbackIso A (i ≫ g)).hom h
  simpa only [Etale.leftDerivedUpperStarCompactificationIso,
    leftDerivedUpperStarCompactificationIso, eqToIso_refl, Iso.trans_refl,
    Iso.symm_hom, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Category.assoc] using h'

private theorem comparison_pullback_compactification
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (H : Etale.DerivedCategoryModule A Y) :
    D(comparisonUpperStar (ModuleCat.{u + 1} A) X).map
        ((Etale.leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom.app H) ≫
      (comparisonOpenDerivedPullbackIso A f).hom.app H =
    (comparisonOpenDerivedPullbackIso A c.i).hom.app
        (L(Etale.upperStar (ModuleCat.{u + 1} A) c.g).obj H) ≫
      L(upperStar (ModuleCat.{u + 1} A) c.i).map
        ((comparisonOpenDerivedPullbackIso A c.g).hom.app H) ≫
      (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom.app
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj H) := by
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj]
    using congr_app (comparison_pullback_compactification_nat A c) H

private theorem comparison_pullback_compactification_iso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (H : Etale.DerivedCategoryModule A Y) :
    D(comparisonUpperStar (ModuleCat.{u + 1} A) X).mapIso
        ((Etale.leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).app H) ≪≫
      (comparisonOpenDerivedPullbackIso A f).app H =
    (comparisonOpenDerivedPullbackIso A c.i).app (L(Etale.upperStar (ModuleCat.{u + 1} A)
      c.g).obj H) ≪≫
      L(upperStar (ModuleCat.{u + 1} A)
        c.i).mapIso ((comparisonOpenDerivedPullbackIso A c.g).app H) ≪≫
      (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj H) := by
  apply Iso.ext
  simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    using comparison_pullback_compactification A c H

attribute [local irreducible] derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
  comparisonOpenTensorIso
  Etale.leftDerivedUpperStarCompactificationIso leftDerivedUpperStarCompactificationIso

private theorem tensor_target_compactification_iso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) :
    D(comparisonUpperStar (ModuleCat.{u + 1} A) X).mapIso
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).mapIso
          ((Etale.leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).app H)) ≪≫
      comparisonOpenTensorIso A f M H =
    comparisonOpenTensorIso A c.i M (L(Etale.upperStar (ModuleCat.{u + 1} A) c.g).obj H) ≪≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M)).mapIso
        (L(upperStar (ModuleCat.{u + 1} A) c.i).mapIso
          ((comparisonOpenDerivedPullbackIso A c.g).app H) ≪≫
          (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).app
            (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj H)) := by
  unfold comparisonOpenTensorIso
  exact tensor_iso_square D(comparisonUpperStar (ModuleCat.{u + 1} A) X)
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M)
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M))
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso (ModuleCat.{u + 1} A) M)
    ((Etale.leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).app H)
    ((comparisonOpenDerivedPullbackIso A f).app H)
   
          ((comparisonOpenDerivedPullbackIso A c.i).app
      (L(Etale.upperStar (ModuleCat.{u + 1} A) c.g).obj H))
    (L(upperStar (ModuleCat.{u + 1} A) c.i).mapIso
          ((comparisonOpenDerivedPullbackIso A c.g).app H) ≪≫
      (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj H))
    (comparison_pullback_compactification_iso A c H)

private theorem tensor_target_compactification
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) :
    D(comparisonUpperStar (ModuleCat.{u + 1} A) X).map
        ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M |>.map
          ((Etale.leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom.app H)) ≫
      (comparisonOpenTensorIso A f M H).hom =
    (comparisonOpenTensorIso A c.i M (L(Etale.upperStar (ModuleCat.{u + 1} A) c.g).obj H)).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M)).map
        (L(upperStar (ModuleCat.{u + 1} A) c.i).map
          ((comparisonOpenDerivedPullbackIso A c.g).hom.app H) ≫
          (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom.app
            (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj H)) := by
  simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    using congrArg Iso.hom (tensor_target_compactification_iso A c M H)

private theorem target_comparison_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) :
    projectionComparisonTargetIso A f M H = (comparisonOpenTensorIso A f M H).symm := by
  have h : projectionComparisonPullbackIso A f =
      (comparisonOpenDerivedPullbackIso A f).symm := comparisonPullback_transport A f
  apply Iso.ext
  simp only [projectionComparisonTargetIso, h, comparisonOpenTensorIso,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.app_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, asIso_hom]


section CompactificationTensor

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

local notation "C" => ModuleCat A
local notation "VX" => D(comparisonUpperStar C X)
local notation "VZ" => D(comparisonUpperStar C c.Z)
local notation "VY" => D(comparisonUpperStar C Y)
local notation "Je" => D(Etale.openImmersionLowerShriek C c.i)
local notation "Jp" => D(openImmersionLowerShriek C c.i)
local notation "Ge" => L(Etale.upperStar C c.g)
local notation "Gp" => L(upperStar C c.g)
local notation "Re" => R(Etale.lowerStar C c.g)
local notation "Rp" => R(lowerStar C c.g)
local notation "TXe" => Etale.derivedTensor C X
local notation "TZp" => derivedTensor C c.Z
local notation "TXp" => derivedTensor C X
local notation "TYp" => derivedTensor C Y
local notation "e" => mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso C c.i
local notation "ce" => Etale.leftDerivedUpperStarCompactificationIso C c
local notation "cp" => leftDerivedUpperStarCompactificationIso C c
local notation "γe" => Iso.inv (Etale.derivedOpenImmersionLowerShriekProjectionIso C c.i)
local notation "γp" => Iso.inv (derivedOpenImmersionLowerShriekProjectionIso C c.i)
local notation "t" K => derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso C K

private theorem open_tensor_compactification_square
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) :
    (VZ).map (((γe).app M).app ((Ge).obj H) ≫ (Je).map (((TXe).obj M).map ((ce).hom.app H))) ≫
      (e).hom.app (projectionComparisonTensor A (f := f) M H) ≫
      (Jp).map (comparisonOpenTensorIso A f M H).hom =
    ((t ((Je).obj M)).hom.app ((Ge).obj H) ≫
      ((TZp).obj ((VZ).obj ((Je).obj M))).map
        ((comparisonOpenDerivedPullbackIso A c.g).hom.app H)) ≫
      ((TZp).map ((e).hom.app M)).app ((Gp).obj ((VY).obj H)) ≫
      (((γp).app ((VX).obj M)).app ((Gp).obj ((VY).obj H)) ≫
        (Jp).map (((TXp).obj ((VX).obj M)).map ((cp).hom.app ((VY).obj H)))) := by
  dsimp only [projectionComparisonTensor]
  refine paste_open_square (VZ) (Je) (Jp) (VX) (e).hom
    (((γe).app M).app ((Ge).obj H))
    (((TXe).obj M).map ((ce).hom.app H))
    (comparisonOpenTensorIso A f M H).hom
    (comparisonOpenTensorIso A c.i M ((Ge).obj H)).hom
    (((TXp).obj ((VX).obj M)).map
      (L(upperStar C c.i).map ((comparisonOpenDerivedPullbackIso A c.g).hom.app H)))
    (((TXp).obj ((VX).obj M)).map ((cp).hom.app ((VY).obj H)))
    ((t ((Je).obj M)).hom.app ((Ge).obj H))
    (((TZp).map ((e).hom.app M)).app ((VZ).obj ((Ge).obj H)))
    (((γp).app ((VX).obj M)).app ((VZ).obj ((Ge).obj H)))
    (((TZp).obj ((VZ).obj ((Je).obj M))).map
      ((comparisonOpenDerivedPullbackIso A c.g).hom.app H))
    (((TZp).obj ((Jp).obj ((VX).obj M))).map
      ((comparisonOpenDerivedPullbackIso A c.g).hom.app H))
    (((TZp).map ((e).hom.app M)).app ((Gp).obj ((VY).obj H)))
    (((γp).app ((VX).obj M)).app ((Gp).obj ((VY).obj H)))
    (comparison_open_tensor_coherence A c.i M ((Ge).obj H)) ?_ ?_ ?_
  · simpa only [Functor.map_comp] using tensor_target_compactification A c M H
  · have hg := ((γp).app ((VX).obj M)).naturality
      ((comparisonOpenDerivedPullbackIso A c.g).hom.app H)
    change ((TZp).obj ((Jp).obj ((VX).obj M))).map
        ((comparisonOpenDerivedPullbackIso A c.g).hom.app H) ≫
        ((γp).app ((VX).obj M)).app ((Gp).obj ((VY).obj H)) =
      ((γp).app ((VX).obj M)).app ((VZ).obj ((Ge).obj H)) ≫
        (Jp).map (((TXp).obj ((VX).obj M)).map
          (L(upperStar C c.i).map
            ((comparisonOpenDerivedPullbackIso A c.g).hom.app H))) at hg
    exact hg.symm
  · have hb := ((TZp).map ((e).hom.app M)).naturality
      ((comparisonOpenDerivedPullbackIso A c.g).hom.app H)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hb
    exact hb.symm

private theorem compact_comparison_inv_mate
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology C)) :
    (compactSupportSiteComparison A c).inv.app K =
      (BoundaryComparison.directImageMate C c.g).app ((Je).obj K.obj) ≫
        (Rp).map ((e).hom.app K.obj) := by
  rw [compact_comparison_inv]
  congr 1
  exact sp_comparison_hom A c.g _ _

attribute [local implicit_reducible] projectionComparisonTensor
  Etale.derivedTensorRightDerivedLowerStar
  Etale.rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerStar rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [local irreducible] Etale.derivedTensor derivedTensor
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Etale.projectionMapOfCompactification projectionMapOfCompactification
  Etale.rightDerivedLowerStarProjectionMap rightDerivedLowerStarProjectionMap
  Etale.derivedOpenImmersionLowerShriekProjectionIso derivedOpenImmersionLowerShriekProjectionIso
  BoundaryComparison.directImageMate compactSupportSiteComparison
  mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso

private theorem compact_projection_square
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y)
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (hD : _root_.DerivedCategory.TStructure.t.plus
      (projectionComparisonTensor A (f := f) M H)) :
    (VY).map (((Etale.projectionMapOfCompactification C c).app M).app H) ≫
      (compactSupportSiteComparison A c).inv.app
        ⟨projectionComparisonTensor A (f := f) M H, hD⟩ ≫
      (rightDerivedLowerShriekOfCompactification C c).map
        (comparisonOpenTensorIso A f M H).hom =
    (t ((Etale.rightDerivedLowerShriekOfCompactification C c).obj M)).hom.app H ≫
      ((TYp).map ((compactSupportSiteComparison A c).inv.app ⟨M, hM⟩)).app ((VY).obj H) ≫
      ((projectionMapOfCompactification C c).app ((VX).obj M)).app ((VY).obj H) := by
  have hfe : ((Etale.projectionMapOfCompactification C c).app M).app H =
      (((Etale.rightDerivedLowerStarProjectionMap C c.g).app ((Je).obj M)).app H) ≫ (Re).map
        (((γe).app M).app ((Ge).obj H) ≫ (Je).map (((TXe).obj M).map ((ce).hom.app H))) := by
    exact (Etale.projectionMapOfCompactification_app_app C c M H).trans
      (append_map (Re) (((Etale.rightDerivedLowerStarProjectionMap C c.g).app ((Je).obj M)).app H)
        (((γe).app M).app ((Ge).obj H))
        ((Je).map (((TXe).obj M).map ((ce).hom.app H))))
  have hfp : ((projectionMapOfCompactification C c).app ((VX).obj M)).app ((VY).obj H) =
      (((rightDerivedLowerStarProjectionMap C c.g).app ((Jp).obj ((VX).obj M))).app ((VY).obj H)) ≫
        (Rp).map (((γp).app ((VX).obj M)).app ((Gp).obj ((VY).obj H)) ≫ (Jp).map (((TXp).obj
        ((VX).obj M)).map ((cp).hom.app ((VY).obj H)))) := by
    exact (projectionMapOfCompactification_app_app C c ((VX).obj M) ((VY).obj H)).trans
      (append_map (Rp) (((rightDerivedLowerStarProjectionMap C c.g).app ((Jp).obj ((VX).obj M))).app
        ((VY).obj H)) (((γp).app ((VX).obj M)).app ((Gp).obj ((VY).obj H)))
        ((Jp).map (((TXp).obj ((VX).obj M)).map ((cp).hom.app ((VY).obj H)))))
  have ho := open_tensor_compactification_square A c M H
  change (VZ).map (((γe).app M).app ((Ge).obj H) ≫ (Je).map (((TXe).obj M).map ((ce).hom.app H))) ≫
    (e).hom.app _ ≫ (Jp).map _ =
    ((t ((Je).obj M)).hom.app ((Ge).obj H) ≫ ((TZp).obj ((VZ).obj ((Je).obj M))).map
      ((comparisonOpenDerivedPullbackIso A c.g).hom.app H)) ≫ ((TZp).map ((e).hom.app M)).app _ ≫
      (((γp).app ((VX).obj M)).app ((Gp).obj ((VY).obj H)) ≫ (Jp).map (((TXp).obj ((VX).obj M)).map
      ((cp).hom.app ((VY).obj H)))) at ho
  have hpb : BoundaryComparison.pullbackSquare C c.g =
      (comparisonOpenDerivedPullbackIso A c.g).symm :=
    (sp_pullback_square C c.g).trans (comparisonPullback_transport A c.g)
  have hp := sp_projection_square C c.g ((Je).obj M) H
  simp only [hpb, Iso.symm_inv, Iso.app_hom] at hp
  change (VY).map (((Etale.rightDerivedLowerStarProjectionMap C c.g).app ((Je).obj M)).app H) ≫
    (BoundaryComparison.directImageMate C c.g).app _ ≫ (Rp).map ((t ((Je).obj M)).hom.app ((Ge).obj
    H) ≫ ((TZp).obj ((VZ).obj ((Je).obj M))).map ((comparisonOpenDerivedPullbackIso A c.g).hom.app
    H)) = _ at hp
  have hn := NatTrans.naturality_app (rightDerivedLowerStarProjectionMap C c.g)
    ((VY).obj H) ((e).hom.app M)
  change ((TYp).map ((Rp).map ((e).hom.app M))).app _ ≫ (((rightDerivedLowerStarProjectionMap C
    c.g).app ((Jp).obj ((VX).obj M))).app ((VY).obj H)) =
    ((rightDerivedLowerStarProjectionMap C c.g).app ((VZ).obj ((Je).obj M))).app _ ≫
      (Rp).map (((TZp).map ((e).hom.app M)).app _) at hn
  have hbm := congrArg (fun z ↦ ((TYp).map z).app ((VY).obj H))
    (compact_comparison_inv_mate A c ⟨M, hM⟩)
  simp only [Functor.map_comp, NatTrans.comp_app] at hbm
  have hbd := compact_comparison_inv_mate A c
    ⟨projectionComparisonTensor A (f := f) M H, hD⟩
  change (compactSupportSiteComparison A c).inv.app
      ⟨projectionComparisonTensor A (f := f) M H, hD⟩ =
    (BoundaryComparison.directImageMate C c.g).app _ ≫ (Rp).map ((e).hom.app _) at hbd
  have result := paste_projection_square (VY) (Re) (Rp) (VZ) (BoundaryComparison.directImageMate C
    c.g)
    (((γe).app M).app ((Ge).obj H) ≫ (Je).map (((TXe).obj M).map ((ce).hom.app H))) ((e).hom.app _)
      ((Jp).map (comparisonOpenTensorIso A f M H).hom)
    ((t ((Je).obj M)).hom.app ((Ge).obj H) ≫ ((TZp).obj ((VZ).obj ((Je).obj M))).map
      ((comparisonOpenDerivedPullbackIso A c.g).hom.app H)) (((TZp).map ((e).hom.app M)).app _)
      (((γp).app ((VX).obj M)).app ((Gp).obj ((VY).obj H)) ≫ (Jp).map (((TXp).obj ((VX).obj M)).map
      ((cp).hom.app ((VY).obj H)))) (((Etale.rightDerivedLowerStarProjectionMap C c.g).app ((Je).obj
      M)).app H)
    ((t ((Etale.rightDerivedLowerShriekOfCompactification C c).obj M)).hom.app H)
    (((TYp).map ((BoundaryComparison.directImageMate C c.g).app ((Je).obj M))).app ((VY).obj H))
    (((TYp).map ((Rp).map ((e).hom.app M))).app ((VY).obj H))
    (((rightDerivedLowerStarProjectionMap C c.g).app ((VZ).obj ((Je).obj M))).app
      ((VY).obj H)) (((rightDerivedLowerStarProjectionMap C c.g).app ((Jp).obj ((VX).obj M))).app
        ((VY).obj H))
    (((Etale.projectionMapOfCompactification C c).app M).app H)
    (((projectionMapOfCompactification C c).app ((VX).obj M)).app ((VY).obj H))
    ((compactSupportSiteComparison A c).inv.app
      ⟨projectionComparisonTensor A (f := f) M H, hD⟩)
    (((TYp).map ((compactSupportSiteComparison A c).inv.app ⟨M, hM⟩)).app ((VY).obj H))
    hfe hfp hbd hbm ho hp hn
  exact result


-- Definitions abstract nested instance proofs into auxiliary theorems; theorem types
-- retain their elaborated proofs. Inline the concrete private proof helpers and apply
-- that same abstraction to their instance arguments. This shares the equation's cached
-- instances and avoids expensive conversions in the localized Hom types. The resulting
-- proof term is checked by the kernel in the usual way.
open Lean Meta in
private meta def normalizeProjectionInstances (proof : Expr) (helpers : Array Name) :
    MetaM Expr := do
  let proof ← Meta.transform proof (skipConstInApp := true) (pre := fun expr => do
    if let .const n us := expr.getAppFn then
      if helpers.contains n then
        let ci ← getConstInfo n
        return .visit ((← instantiateValueLevelParams ci us (allowOpaque := true)).beta
          expr.getAppArgs)
    if ← AbstractNestedProofs.isNonTrivialProof expr then
      let ty ← inferType expr
      if let .const n _ := ty.getAppFn then
        if isClass (← getEnv) n then
          let expr ← abstractProof expr (postprocessType := fun ty => abstractNestedProofs ty)
          return .done expr
    return .continue)
  if proof.hasSorry then
    throwError "Instance proof normalization left an unfinished proof"
  return proof

open Lean Meta Elab Tactic in
local elab "start_shared_proof" : tactic => do
  withMainContext do
    let g ← getMainGoal
    let h ← mkFreshExprSyntheticOpaqueMVar (← g.getType)
    g.setTag h.mvarId!.name
    replaceMainGoal [h.mvarId!, g]

open Lean Meta Elab Tactic in
local elab "finish_shared_proof" : tactic => do
  withMainContext do
    let g ← getMainGoal
    let h : MVarId := ⟨← g.getTag⟩
    let proof ← instantiateMVars (mkMVar h)
    if proof.hasMVar then
      throwError "The intermediate proof has unresolved goals"
    let helpers : Array Name := #[
      ``proper_comparison_normalization,
      ``compact_comparison_inv,
      ``support_comparison_eq,
      ``etale_composition_eq,
      ``proetale_composition_eq,
      ``comparison_pullback_hom,
      ``comparison_pullback_comp,
      ``comparison_pullback_comp_nat,
      ``comparison_pullback_compactification_nat,
      ``comparison_pullback_compactification,
      ``comparison_pullback_compactification_iso,
      ``tensor_target_compactification_iso,
      ``tensor_target_compactification,
      ``target_comparison_eq,
      ``open_tensor_compactification_square,
      ``compact_comparison_inv_mate,
      ``compact_projection_square]
    let proof ← normalizeProjectionInstances proof helpers
    g.assign proof
    replaceMainGoal []

-- The two goals intentionally separate elaboration from sharing its completed proof.
set_option linter.style.multiGoal false in
private theorem projection_equation_of_plus
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y)
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (hD : _root_.DerivedCategory.TStructure.t.plus
      (projectionComparisonTensor A (f := f) M H)) :
    ProjectionComparisonEquation A c M H hM hD := by
  start_shared_proof
  · unfold ProjectionComparisonEquation
    dsimp only [derivedTensorRightDerivedLowerShriek,
      rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
      Etale.derivedTensorRightDerivedLowerShriek,
      Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
      Functor.comp_obj, ObjectProperty.ι_obj,
      Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
      Functor.postcompose₂_obj_obj_obj_obj, Functor.id_obj]
    rw [target_comparison_eq]
    apply inverse_projection_arrows
    · exact (((TYp).mapIso ((compactSupportSiteComparison A c).app ⟨M, hM⟩)).app
        ((VY).obj H)).hom_inv_id
    · exact Iso.inv_hom_id_app
        (t ((Etale.rightDerivedLowerShriekOfCompactification C c).obj M)) H
    · exact ((rightDerivedLowerShriekOfCompactification C c).mapIso
        (comparisonOpenTensorIso A f M H)).hom_inv_id
    · exact Iso.inv_hom_id_app (compactSupportSiteComparison A c)
        ⟨projectionComparisonTensor A (f := f) M H, hD⟩
    · exact compact_projection_square A c M H hM hD
  · finish_shared_proof

end CompactificationTensor

/-- At positive finite coefficient level, the canonical compact-support site comparison
intertwines the two compactification projection maps on bounded constructible inputs,
with finite Tor amplitude only for H. The existential proofs record the bounded-below
domains of the two comparisons, rather than impose additional hypotheses. Naturality
in M,H is that of the specified bifunctor transformations and their natural inverses.
Source: main-20261015 blueprint, thm-pur-cohomological-smoothness.proof.md, paragraph 1;
Stacks Tags 0E48, 09AF, 0GL1
(blueprint: lem-pur-projection-comparison-etale-origin).

Proof:
1. The coefficient ring is finite. Choose a lower bound r for M and a Tor interval
   [a,b] for H. By lem-kun-0f1m take a flat-term K-flat model of H bounded below by a.
   Pullback preserves this model and its bound. Exact open extension preserves the
   lower bound r. By lem-kun-derived-tensor-t-est the two tensor inputs have lower
   bound a+r. Thus M and M tensor f*H lie in the domains of C.
2. On these flat K-flat models the canonical tensor and pullback comparisons agree
   on pure tensors, including the total differential signs and the j*p*=f* identity.
3. Apply lem-weil-pbc-ringed-exchange-tensor-coherence to the proper-factor site
   comparison square. Its exchange is the canonical counit mate fixed in
   lem-weil-pbc-comparison-direct-image-canonical-mate. This gives the proper square.
4. Extend lem-cbc-proetale-extension-zero-comparison termwise. Exactness on both sites
   makes it descend. Restrict the open tensor square back to X. Both routes become
   the identity tensor map by lem-sf-open-tensor-normalization and the pure-tensor
   formula for lem-pur-etale-open-derived-tensor. Full faithfulness of open extension
   proves the open square, without local freeness of M.
5. By lem-pur-compact-support-site-coherence, B=C inverse is exactly proper mate
   followed by proper image of the open comparison. Both projections are the proper
   counit mate followed by proper image of the corresponding open tensor map.
6. Paste the proper and open squares. Naturality of the proper mate at the open
   tensor arrow and naturality of projection in its first input give
   B_D V(PF-et) = PF-pro (B_M tensor 1) t inverse, with the specified target transport.
7. Precompose by t(C_M tensor 1), postcompose by C_D, and cancel inverse pairs.
   This is ProjectionComparisonEquation. All factors are natural in both inputs,
   so the equation is natural. Zero inputs, empty X and identity factors obey the
   same equations; smoothness and exceptional pullback are never used.
-/
theorem projectionComparison_etaleOrigin
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (M : Etale.DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (H : Etale.DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y)
    (_hM : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) X M)
    (_hH : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) Y H)
    (_hTor : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn
      (Padic.coefficientExtensionRing l E n) Y a b H) :
    projectionComparisonConclusion D l _hl E n f c M H _hM _hH _hTor := by
  unfold projectionComparisonConclusion
  have : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n (Fact.out : 1 ≤ n)
  have hMb := bounded_of_constructible (Padic.coefficientExtensionRing l E n) X M _hM
  have hD := plus_tensor_of_tor (Padic.coefficientExtensionRing l E n) f M H hMb _hTor
  exact ⟨hMb.1, hD, projection_equation_of_plus _ c M H hMb.1 hD⟩


end AlgebraicGeometry.ProEtale
