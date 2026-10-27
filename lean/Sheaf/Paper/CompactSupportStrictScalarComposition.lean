module

public import Sheaf.Paper.CompactSupportScalarLimitReduction
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Compactification.RefinementCategory

import Sheaf.Paper.CompactSupportCompleteRestrictionFaithful
import Sheaf.Paper.ConstantCompletedScalarAssociativity
import all Sheaf.Paper.OrdinaryOpenScalarComposition
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Sheaf.Paper.ScalarLimitTensorComposition
import Sheaf.Paper.ScalarLimitTensorRestriction
import Sheaf.Paper.StrictProperRestrictionComposition

/-! # Composition of strict compact-support scalar mates

Source: Stacks Tags 07A6 (lemma-adjoint), 0E8I and 0941; the auxiliary
composition calculation in returned comparison Step 11.
(blueprint: lem-pur-compact-support-strict-scalar-composition).

The tensor associators below are conjugates of the identity-on-sections restriction
comparisons. Arithmetic reassociation is the localization of the actual index equality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : F →ₐ[ℚ_[l]] L)

/-- The actual constant coefficient maps compose, including identity embeddings.
Source: tensor balancing, auxiliary proof Steps 1 and 6
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: the integral inclusions compose on elements of the fields; functoriality
of the constant sheaf and the universe lift preserves that equality. -/
theorem constantMap_composition (W : Scheme.{u}) :
    constantMap l E F i W ≫ constantMap l F L j W =
      constantMap l E L (j.comp i) W := by
  unfold constantMap
  rw [← Functor.map_comp]
  congr 1

/-- Ordinary constant tensor associativity, normalized by the tensor-unit adjunctions.
Source: Stacks 07A6; auxiliary proof Steps 1--2
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionOrdinary (W : Scheme.{u}) :
    pbcExtend (constantMap l E F i W) ⋙ pbcExtend (constantMap l F L j W) ≅
      pbcExtend (constantMap l E L (j.comp i) W) :=
  (((pbcScalarAdjunction (constantMap l E F i W)).comp
      (pbcScalarAdjunction (constantMap l F L j W))).ofNatIsoRight
    (pbcRestrictComp _ _ _ (constantMap_composition l E F i L j W))).leftAdjointUniq
      (pbcScalarAdjunction (constantMap l E L (j.comp i) W))

/-- Tensor associativity on derived constant-coefficient module sheaves.
Source: Stacks 06YY; auxiliary proof Step 7
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionBase (W : Scheme.{u}) :
    baseTensor l E F i W ⋙ baseTensor l F L j W ≅ baseTensor l E L (j.comp i) W :=
  haveI := (baseTensor_exact l E F i W).1
  haveI := (baseTensor_exact l E F i W).2
  haveI := (baseTensor_exact l F L j W).1
  haveI := (baseTensor_exact l F L j W).2
  haveI := (baseTensor_exact l E L (j.comp i) W).1
  haveI := (baseTensor_exact l E L (j.comp i) W).2
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (compositionOrdinary l E F i L j W)

/-- The same ordinary associator on whole strict towers.
Source: Stacks 0940; auxiliary proof Step 2
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionTowerOrdinary (W : Scheme.{u}) :
    tensor l E F i W ⋙ tensor l F L j W ≅ tensor l E L (j.comp i) W :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (compositionOrdinary l E F i L j W)

/-- The associator alpha in the strict derived diagram category, before taking limits.
Source: Stacks 0940; auxiliary proof Steps 2--5
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionTower (W : Scheme.{u}) :
    T l E F i W ⋙ T l F L j W ≅ T l E L (j.comp i) W :=
  haveI := (tensor_exact l E F i W).1
  haveI := (tensor_exact l E F i W).2
  haveI := (tensor_exact l F L j W).1
  haveI := (tensor_exact l F L j W).2
  haveI := (tensor_exact l E L (j.comp i) W).1
  haveI := (tensor_exact l E L (j.comp i) W).2
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (compositionTowerOrdinary l E F i L j W)

/-- Ordinary completed tensor associativity with the published scalar adjunction units.
Source: Stacks 07A6; auxiliary proof Step 9
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionCompleted (W : Scheme.{u}) :
    pbcDerivedExtend (completedCoefficientMap l E F i W) ⋙
        pbcDerivedExtend (completedCoefficientMap l F L j W) ≅
      pbcDerivedExtend (completedCoefficientMap l E L (j.comp i) W) :=
  PurCompactSupport.tensorComposition _ _ _
    (PurCompactSupport.completedMap_composition l E F i L j W)

/-- Exact tensor commutes with selection of arithmetic levels by the identity square.
Source: Stacks 0940; auxiliary proof Step 5
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionSelection (W : Scheme.{u}) (e : ℕ) :
    subsequence l F W e ⋙ T l F L j W ≅ T l F L j W ⋙ subsequence l L W e :=
  haveI := (tensor_exact l F L j W).1
  haveI := (tensor_exact l F L j W).2
  Functor.mapDerivedCategorySquareIso (Iso.refl _)

/-- Nested selections retain precisely the same objects and composite transitions.
Source: arithmetic level calculation, auxiliary proof Steps 1 and 5
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: the predecessor of h(e(n+1)) is h*e*(n+1)-1. Positivity of e and h
permits cancellation of each predecessor/successor pair. Arrows agree because
natural-number order categories have at most one arrow between two objects. -/
theorem compositionSelectionOrdinary (W : Scheme.{u}) (e h : ℕ)
    (he : 1 ≤ e) (hh : 1 ≤ h) :
    ordinarySubsequence l L W h ⋙ ordinarySubsequence l L W e =
      ordinarySubsequence l L W (h * e) := by
  have _hhpos := hh
  have hi : CategoryTheory.StrictTowerArithmetic.index e ⋙
      CategoryTheory.StrictTowerArithmetic.index h =
        CategoryTheory.StrictTowerArithmetic.index (h * e) := by
    apply CategoryTheory.Functor.ext
    · intro a b f
      apply Subsingleton.elim
    · intro n
      cases n with
      | op n =>
        apply congrArg op
        change h * (e * (n + 1) - 1 + 1) - 1 = (h * e) * (n + 1) - 1
        rw [Nat.sub_add_cancel (Nat.mul_pos he (Nat.succ_pos n)), Nat.mul_assoc]
  change CategoryTheory.StrictTowerArithmetic.restriction _ h ⋙
    CategoryTheory.StrictTowerArithmetic.restriction _ e = _
  simp only [CategoryTheory.StrictTowerArithmetic.restriction]
  change (Functor.whiskeringLeft _ _ _).obj
    (CategoryTheory.StrictTowerArithmetic.index e ⋙
      CategoryTheory.StrictTowerArithmetic.index h) = _
  rw [hi]

/-- Canonical reassociation between the two retained strict derived towers.
Source: Stacks 0940; auxiliary proof Step 5
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionRetained (W : Scheme.{u}) (e h : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) :
    subsequence l L W h ⋙ subsequence l L W e ≅ subsequence l L W (h * e) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (eqToIso (compositionSelectionOrdinary l L W e h he hh))

/-- The ramification ideal equality for the composite inclusion.
Source: auxiliary proof Step 1
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: map the first ideal equality through the second integer inclusion, then
use preservation of ideal powers and the second equality. The exponent is h*e. -/
theorem compositionRamification (e h : ℕ)
    (he : PurCompactSupport.Ramification l E F i e)
    (hh : PurCompactSupport.Ramification l F L j h) :
    PurCompactSupport.Ramification l E L (j.comp i) (h * e) := by
  have hc : integralScalarIntegerInclusion l E L (j.comp i) =
      (integralScalarIntegerInclusion l F L j).comp
        (integralScalarIntegerInclusion l E F i) := by
    ext x
    rfl
  change Ideal.map _ _ = _
  rw [hc, ← Ideal.map_map, he]
  change Ideal.map _ (Ideal.span {Padic.coefficientExtensionUniformizer l F} ^ e) = _
  rw [Ideal.map_pow]
  have hh' := hh
  change Ideal.map _ (Ideal.span {Padic.coefficientExtensionUniformizer l F} ^ 1) =
    Ideal.span {Padic.coefficientExtensionUniformizer l L} ^ h at hh'
  rw [pow_one] at hh'
  rw [hh', ← pow_mul]
  rfl

attribute [local irreducible] scalarAdj properRestriction

private def properScalarMate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {r : B ⥤ A} {G : C ⥤ D} {s : D ⥤ C}
    (a : F ⊣ r) (b : G ⊣ s) {I : A ⥤ C} {J : B ⥤ D}
    (α : r ⋙ I ⟶ J ⋙ s) : I ⋙ G ⟶ F ⋙ J :=
  ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ α)).natTrans

private theorem inverse_restriction_cocycle
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    {r : B ⥤ A} {s : C ⥤ B} {t : C ⥤ A}
    {r' : B' ⥤ A'} {s' : C' ⥤ B'} {t' : C' ⥤ A'}
    {I : A ⥤ A'} {J : B ⥤ B'} {K : C ⥤ C'}
    (c : s ⋙ r ≅ t) (c' : s' ⋙ r' ≅ t')
    (a : J ⋙ r' ≅ r ⋙ I) (b : K ⋙ s' ≅ s ⋙ J) (e : K ⋙ t' ≅ t ⋙ I)
    (he : ∀ M, r'.map (b.hom.app M) ≫ a.hom.app (s.obj M) ≫
      I.map (c.hom.app M) = c'.hom.app (K.obj M) ≫ e.hom.app M) (M : C) :
    I.map (c.hom.app M) ≫ e.inv.app M =
      a.inv.app (s.obj M) ≫ r'.map (b.inv.app M) ≫ c'.hom.app (K.obj M) := by
  have hd := congrArg (fun z ↦
    a.inv.app (s.obj M) ≫ r'.map (b.inv.app M) ≫ z ≫ e.inv.app M) (he M)
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Iso.hom_inv_id_app] at hd
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc, Category.comp_id] at hd
  exact hd

private theorem proper_mate_tower_square
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
        (properScalarMate dH dH' e).app M =
      G'.map ((properScalarMate dF dF' a).app M) ≫ (properScalarMate dG dG' b).app (F.obj M) ≫
        K.map ((Adjunction.leftAdjointCompIso dF dG dH c).hom.app M) := by
  let x : TwoSquare I (F ⋙ G) (F' ⋙ G') K :=
    TwoSquare.vComp (properScalarMate dF dF' a) (properScalarMate dG dG' b)
  let y : TwoSquare I (F ⋙ G) (F' ⋙ G') K :=
    ((TwoSquare.mk _ _ _ _ (properScalarMate dH dH' e)).whiskerLeft
      (Adjunction.leftAdjointCompIso dF dG dH c).inv).whiskerRight
        (Adjunction.leftAdjointCompIso dF' dG' dH' c').hom
  have h : x = y := by
    apply (mateEquiv (dF.comp dG) (dF'.comp dG')).injective
    dsimp only [x, y]
    rw [mateEquiv_hcomp]
    rw [mateEquiv_conjugateEquiv_vcomp (dF.comp dG) dH' (dF'.comp dG')]
    rw [conjugateEquiv_mateEquiv_vcomp (dF.comp dG) dH dH']
    simp only [properScalarMate, Equiv.apply_symm_apply,
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

/-- The strict scalar proper mates compose under ordinary tensor associativity.
Source: Stacks 07A6; auxiliary proof Steps 2--3
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: ordinary coefficient restriction and proper image commute by the identity
on underlying sections. Whole-complex unit normalization carries their cocycle
through right derivation. The localized ordinary tensor associator is the
canonical composite-adjunction comparison. Invert the restriction cocycle and
apply mate pasting with these normalized scalar adjunctions. -/
theorem compositionProper {Z W : Scheme.{u}} (g : Z ⟶ W)
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
    (compositionTower l E F i L j W).hom.app
          ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj K) ≫
        (proper l E L (j.comp i) g).app K =
      (T l F L j W).map ((proper l E F i g).app K) ≫
        (proper l F L j g).app ((T l E F i Z).obj K) ≫
        (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) g).map
          ((compositionTower l E F i L j Z).hom.app K) := by
  have hα (V : Scheme.{u}) :
      compositionTower l E F i L j V =
        Adjunction.leftAdjointCompIso (scalarAdj l E F i V) (scalarAdj l F L j V)
          (scalarAdj l E L (j.comp i) V)
          (towerScalarRestrictionComposition l E F i L j V) :=
    scalarTowerAssociator_normalization l E F i L j V
  rw [hα Z, hα W]
  exact proper_mate_tower_square
    (scalarAdj l E F i Z) (scalarAdj l F L j Z)
    (scalarAdj l E L (j.comp i) Z)
    (scalarAdj l E F i W) (scalarAdj l F L j W)
    (scalarAdj l E L (j.comp i) W)
    (towerScalarRestrictionComposition l E F i L j Z)
    (towerScalarRestrictionComposition l E F i L j W)
    (properRestriction l E F i g).inv (properRestriction l F L j g).inv
    (properRestriction l E L (j.comp i) g).inv
    (inverse_restriction_cocycle
      (towerScalarRestrictionComposition l E F i L j Z)
      (towerScalarRestrictionComposition l E F i L j W)
      (properRestriction l E F i g) (properRestriction l F L j g)
      (properRestriction l E L (j.comp i) g)
      (properRestriction_composition l E F i L j g)) K

attribute [local irreducible] pbcScalarAdjunction pbcDerivedScalarAdjunction
  ordinaryOpenTensor ordinaryBaseOpenTensor PurCompactSupport.openAdjunction
  proEtaleRingRestrictionPullbackInv in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Open scalar balancing uses the same associator as the proper square.
Source: Stacks 0E8I; auxiliary proof Step 4
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: on objects in the open both paths multiply the two scalar factors; off
the open both are zero. This commutes with differentials and quotient transitions.
Sheafification and exact localization preserve the equality. -/
theorem compositionOpen {Z W : Scheme.{u}} (g : Z ⟶ W) [IsOpenImmersion g]
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
    (compositionTower l E F i L j W).hom.app
          ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj K) ≫
        (openTensor l E L (j.comp i) g).app K =
      (T l F L j W).map ((openTensor l E F i g).app K) ≫
        (openTensor l F L j g).app ((T l E F i Z).obj K) ≫
        (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) g).map
          ((compositionTower l E F i L j Z).hom.app K) := by
  have hordinary (N : Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
      (tensor l F L j W).map ((ordinaryOpenTensor l E F i g).app N) ≫
          (ordinaryOpenTensor l F L j g).app ((tensor l E F i Z).obj N) ≫
          (towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) g).map
            ((compositionTowerOrdinary l E F i L j Z).hom.app N) =
        (compositionTowerOrdinary l E F i L j W).hom.app
            ((towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj N) ≫
          (ordinaryOpenTensor l E L (j.comp i) g).app N := by
    simp only [ordinaryOpenTensor_eq]
    apply NatTrans.ext
    funext n
    exact (ordinaryBaseOpenTensor_composition l E F i L j g (N.obj n)).symm
  exact localizedOpenTensor_composition l E F i L j g
    (compositionTowerOrdinary l E F i L j Z)
    (compositionTowerOrdinary l E F i L j W) hordinary K

private theorem scalarLimitRestriction_composition (W : Scheme.{u})
    (e h : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h)
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) W) :
    (scalarLimitRestriction l L W h).app K ≫
        (scalarLimitRestriction l L W e).app ((subsequence l L W h).obj K) ≫
        (scalarLimit l L W).map ((compositionRetained l L W e h he hh).hom.app K) =
      (scalarLimitRestriction l L W (h * e)).app K := by
  exact localizedSelectionRestriction_composition l L W e h he hh
    (compositionSelectionOrdinary l L W e h he hh) K

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))] [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))] [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

/-- Composition of the actual strict proper/open scalar mates on the common L tower.
All maps lie in the derived category of constant integral L-module strict towers.
Source: Stacks 07A6, 0E8I and 0941; returned comparison Step 11
(blueprint: lem-pur-compact-support-strict-scalar-composition).

Proof (DAG Steps 1--6):
1. Use the coefficient-model lemma and ideal-quotient-tower scalar associator on
   A/t^n, B/t^n B, O_L/t^n O_L, at levels n,en,hen, including augmentations.
2. Ordinary coefficient-restriction/proper-image squares paste by identity on
   sections. Their whole-complex unit normalization derives this equality.
3. Apply mate pasting to obtain compositionProper for the specified proper mates.
4. On the open the balancing formula is multiplication, and off it both maps are
   zero. Thus compositionOpen holds, including all quotient transitions.
5. Expand q=Rp(b)a. Naturality of the second proper mate moves it past the first
   open factor; substitute the preceding two equations and tensor naturality.
   Nested selection has exactly levels hen and composite transitions, giving
   compositionRetained. This proves the displayed equation in the diagram category.
6. Identity squares have identity mates; tensor units give identity open balancing.
   All formulas preserve coefficients and quotient augmentations. The equality
   holds before any limit and can be composed with every strict augmentation. -/
theorem compactSupportStrictScalarComposition (c : Compactification f)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L X)
    (e h : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (hh : PurCompactSupport.Ramification l F L j h) (hhpos : 1 ≤ h)
    (M : DerivedCategory (scalarReductionSource l E X))
    (_hM : finiteTorConstructibleIntegral l E X M) :
    (compositionTower l E F i L j Y).hom.app ((support l E c SE).obj M) ≫
        (arrow l E L (j.comp i) c SE SL (h * e)
          (compositionRamification l E F i L j e h he hh) (one_le_mul hhpos hepos)).app M =
      (T l F L j Y).map ((arrow l E F i c SE SF e he hepos).app M) ≫
        (compositionSelection l F L j Y e).hom.app
          ((support l F c SF).obj
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ≫
        (subsequence l L Y e).map
          ((arrow l F L j c SF SL h hh hhpos).app
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ≫
        (compositionRetained l L Y e h hepos hhpos).hom.app
          ((support l L c SL).obj
            ((pbcDerivedExtend (completedCoefficientMap l F L j X)).obj
              ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))) ≫
        (subsequence l L Y (h * e)).map
          ((support l L c SL).map ((compositionCompleted l E F i L j X).hom.app M)) := by
  sorry

/-- Strict mate composition on the common compact-support image tower.
Source: auxiliary proof Steps 3--5 (blueprint: lem-pur-compact-support-strict-scalar-composition).
(blueprint: lem-pur-compact-support-strict-scalar-comparison-stage3-h2).
Proof: paste the proper restriction cocycles, apply mateEquiv horizontal and
vertical pasting, and use the balancing associator for the open factor. Naturality
of the pasted comparison gives the displayed equation before support realization. -/
theorem compactSupportStrictScalarComparison (c : Compactification f)
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (compositionTower l E F i L j Y).hom.app ((image l E c).obj K) ≫
        (comparison l E L (j.comp i) c).app K =
      (T l F L j Y).map ((comparison l E F i c).app K) ≫
        (comparison l F L j c).app ((T l E F i X).obj K) ≫
        (image l L c).map ((compositionTower l E F i L j X).hom.app K) := by
  sorry



/-- The same composition after the specified tensor/product and cofinal Roos maps.
Source: Stacks 0941; auxiliary proof Steps 7--8
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: horizontal Roos coherence composes the canonical tensor/product tau maps.
The selection/block cofinal maps commute with tau and tower maps and their blocks
concatenate. Apply the total limit to the strict equation and postcompose by
r_(he). Naturality cancels the intermediate cofinal inverse, and horizontal tau
coherence identifies the remaining two expressions. Cancel the invertible r_(he).
The recorded Roos normalizations retain the zero shifted-product augmentation. -/
theorem compactSupportScalarLimitComposition (c : Compactification f)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L X)
    (e h : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (hh : PurCompactSupport.Ramification l F L j h) (hhpos : 1 ≤ h)
    (M : DerivedCategory (scalarReductionSource l E X))
    (_hM : finiteTorConstructibleIntegral l E X M) :
    (compositionBase l E F i L j Y).hom.app
          ((support l E c SE ⋙ scalarLimit l E Y).obj M) ≫
        scalarLimitArrow l E L (j.comp i) c SE SL (h * e)
          (compositionRamification l E F i L j e h he hh) (one_le_mul hhpos hepos) M =
      (baseTensor l F L j Y).map (scalarLimitArrow l E F i c SE SF e he hepos M) ≫
        scalarLimitArrow l F L j c SF SL h hh hhpos
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) ≫
        (support l L c SL ⋙ scalarLimit l L Y).map
          ((compositionCompleted l E F i L j X).hom.app M) := by
  let K₀ := (support l E c SE).obj M
  let M₁ := (pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M
  let K₁ := (support l F c SF).obj M₁
  let K₂' := (support l L c SL).obj
    ((pbcDerivedExtend (completedCoefficientMap l F L j X)).obj M₁)
  let K₂ := (support l L c SL).obj
    ((pbcDerivedExtend (completedCoefficientMap l E L (j.comp i) X)).obj M)
  let b : K₂' ⟶ K₂ :=
    (support l L c SL).map ((compositionCompleted l E F i L j X).hom.app M)
  have := scalarLimitRestriction_isIso l F Y e hepos
  have := scalarLimitRestriction_isIso l L Y h hhpos
  have := scalarLimitRestriction_isIso l L Y (h * e) (one_le_mul hhpos hepos)
  have hτ := scalarLimitTensor_composition l E F i L j (j.comp i) Y
    (compositionOrdinary l E F i L j Y) K₀
  change (compositionBase l E F i L j Y).hom.app ((scalarLimit l E Y).obj K₀) ≫
    (scalarLimitTensor l E L (j.comp i) Y).hom.app K₀ =
    (baseTensor l F L j Y).map ((scalarLimitTensor l E F i Y).hom.app K₀) ≫
      (scalarLimitTensor l F L j Y).hom.app ((T l E F i Y).obj K₀) ≫
      (scalarLimit l L Y).map ((compositionTower l E F i L j Y).hom.app K₀) at hτ
  have hσ := scalarLimitTensor_restriction l F L j Y e hepos K₁
  change (baseTensor l F L j Y).map ((scalarLimitRestriction l F Y e).app K₁) ≫
    (scalarLimitTensor l F L j Y).hom.app ((subsequence l F Y e).obj K₁) ≫
    (scalarLimit l L Y).map ((compositionSelection l F L j Y e).hom.app K₁) =
    (scalarLimitTensor l F L j Y).hom.app K₁ ≫
      (scalarLimitRestriction l L Y e).app ((T l F L j Y).obj K₁) at hσ
  have hκ := scalarLimitRestriction_composition l L Y e h hepos hhpos K₂'
  have hq := compactSupportStrictScalarComposition l E F i L j D hl f c SE SF SL
    e h he hepos hh hhpos M _hM
  have nb := (scalarLimitRestriction l L Y (h * e)).naturality b
  have nq := (scalarLimitRestriction l L Y e).naturality
    ((arrow l F L j c SF SL h hh hhpos).app M₁)
  have nt := (scalarLimitTensor l F L j Y).hom.naturality
    ((arrow l E F i c SE SF e he hepos).app M)
  apply (cancel_mono ((scalarLimitRestriction l L Y (h * e)).app K₂)).mp
  simp only [scalarLimitArrow, scalarLimitCofinalInverse, Functor.map_comp,
    Functor.comp_map, Functor.comp_obj, Category.assoc]
  rw [IsIso.inv_hom_id, Category.comp_id]
  change _ = _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ (scalarLimit l L Y).map b ≫
    (scalarLimitRestriction l L Y (h * e)).app K₂
  rw [nb, ← reassoc_of% hκ]
  rw [IsIso.inv_hom_id_assoc]
  rw [reassoc_of% nq, ← reassoc_of% hσ]
  have hire :
      (baseTensor l F L j Y).map (inv ((scalarLimitRestriction l F Y e).app K₁)) ≫
          (baseTensor l F L j Y).map ((scalarLimitRestriction l F Y e).app K₁) = 𝟙 _ := by
    rw [← Functor.map_comp, IsIso.inv_hom_id]
    exact (baseTensor l F L j Y).map_id _
  rw [reassoc_of% hire]
  rw [reassoc_of% nt]
  simp only [Functor.comp_map, ← Functor.map_comp]
  rw [← hq]
  simp only [Functor.map_comp]
  rw [← reassoc_of% hτ]

/-- The completed scalar comparison is uniquely fixed by its constant-coefficient
realization, rather than chosen from its finite evaluations.
Source: Stacks 0941; scalar-limit-reduction normalization and auxiliary proof Step 9
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: the scalar-limit-reduction theorem gives existence. Restriction along the
constant-to-completed coefficient map is faithful on the complete objects in
question: complete objects are the normalized full quotient towers, and the map
respects their coefficient actions and augmentations. Equivalently its maps are
recovered by the derived extension/restriction adjunction and completeness unit.
The specified scalarSupportLimit and scalarCompletion comparisons therefore give
uniqueness for the realized map, without assuming faithfulness of finite evaluation. -/
theorem completedArrow_existsUnique (c : Compactification f)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X))
    (_hM : finiteTorConstructibleIntegral l E X M) :
    ∃! γ : (pbcDerivedExtend (completedCoefficientMap l E F i Y)).obj
          ((scalarSupport l E c SE).obj M) ⟶
        (scalarSupport l F c SF).obj
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M),
      (scalarCompletion l E F i Y).hom.app ((scalarSupport l E c SE).obj M) ≫
          (scalarConstantRestriction l F Y).map γ ≫
          (scalarSupportLimit l F c SF).hom.app
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) =
        (baseTensor l E F i Y).map ((scalarSupportLimit l E c SE).hom.app M) ≫
          scalarLimitArrow l E F i c SE SF e he hepos M := by
  obtain ⟨γ, _, hγ⟩ := compactSupportScalarLimitReduction l E F i D hl f c SE SF e he hepos
  have hreal := (hγ ⟨M, _hM⟩).2.2.2.2.2.2.2.2.1.symm
  refine ⟨γ.app ⟨M, _hM⟩, hreal, ?_⟩
  intro δ hδ
  apply scalarConstantRestriction_complete_map_injective l F Y
    ((hγ ⟨M, _hM⟩).2.2.1)
  apply (cancel_epi ((scalarCompletion l E F i Y).hom.app
    ((scalarSupport l E c SE).obj M))).mp
  apply (cancel_mono ((scalarSupportLimit l F c SF).hom.app
    ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))).mp
  simpa only [scalarConstantRestriction, constantRestriction, Category.assoc] using
    hδ.trans hreal.symm

/-- Gamma is the unique completed-linear realization of r_e inverse R(q) tau.
Source: auxiliary proof Step 9; the augmentation-normalized scalar-limit reduction
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def completedArrow (c : Compactification f)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :=
  (completedArrow_existsUnique l E F i D hl f c SE SF e he hepos M hM).exists.choose

/-- Composition on the ordinary completed-tensor model with its actual associators.
Source: Stacks 07A6 and 0941; auxiliary proof Step 9
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: use the coefficient-model lemma on the input, its successive extensions,
and support outputs. The scalar-completion-associator lemma identifies the strict
balanced associator with ordinary completed associativity through the specified
chi maps. Conjugate compactSupportScalarLimitComposition by scalarCompletion and
scalarSupportLimit at both endpoints. Their augmentation normalizations identify
this with the uniquely specified completedArrow, giving exactly this equation.
The finite-Tor witness for C_(F/E)M is the first clause of the cited
compactSupportScalarLimitReduction, not the downstream coefficient comparison. -/
theorem compactSupportCompletedScalarComposition (c : Compactification f)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L X)
    (e h : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (hh : PurCompactSupport.Ramification l F L j h) (hhpos : 1 ≤ h)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    (compositionCompleted l E F i L j Y).hom.app ((scalarSupport l E c SE).obj M) ≫
        completedArrow l E L (j.comp i) D hl f c SE SL (h * e)
          (compositionRamification l E F i L j e h he hh) (one_le_mul hhpos hepos) M hM =
      (pbcDerivedExtend (completedCoefficientMap l F L j Y)).map
          (completedArrow l E F i D hl f c SE SF e he hepos M hM) ≫
        completedArrow l F L j D hl f c SF SL h hh hhpos
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)
          ((compactSupportScalarLimitReduction l E F i D hl f c SE SF e he hepos).elim
            fun _ h ↦ (h.2 ⟨M, hM⟩).1) ≫
        (scalarSupport l L c SL).map
          ((compositionCompleted l E F i L j X).hom.app M) := by
  let K := (scalarSupport l E c SE).obj M
  let M₁ := (pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M
  let M₂ := (pbcDerivedExtend (completedCoefficientMap l E L (j.comp i) X)).obj M
  have hM₁ : finiteTorConstructibleIntegral l F X M₁ :=
    (compactSupportScalarLimitReduction l E F i D hl f c SE SF e he hepos).elim
      fun _ h ↦ (h.2 ⟨M, hM⟩).1
  have targetComplete : IsSfDerivedComplete l L Y ((scalarSupport l L c SL).obj M₂) :=
    (compactSupportScalarLimitReduction l E L (j.comp i) D hl f c SE SL (h * e)
      (compositionRamification l E F i L j e h he hh) (one_le_mul hhpos hepos)).elim
      fun _ h ↦ (h.2 ⟨M, hM⟩).2.2.1
  have norm₁ := Classical.choose_spec
    (completedArrow_existsUnique l E F i D hl f c SE SF e he hepos M hM).exists
  have norm₂ := Classical.choose_spec
    (completedArrow_existsUnique l F L j D hl f c SF SL h hh hhpos M₁ hM₁).exists
  have norm₃ := Classical.choose_spec
    (completedArrow_existsUnique l E L (j.comp i) D hl f c SE SL (h * e)
      (compositionRamification l E F i L j e h he hh)
      (one_le_mul hhpos hepos) M hM).exists
  change (scalarCompletion l E F i Y).hom.app K ≫
    (scalarConstantRestriction l F Y).map
      (completedArrow l E F i D hl f c SE SF e he hepos M hM) ≫ _ = _ at norm₁
  change (scalarCompletion l F L j Y).hom.app ((scalarSupport l F c SF).obj M₁) ≫
    (scalarConstantRestriction l L Y).map
      (completedArrow l F L j D hl f c SF SL h hh hhpos M₁ hM₁) ≫ _ = _ at norm₂
  change (scalarCompletion l E L (j.comp i) Y).hom.app K ≫
    (scalarConstantRestriction l L Y).map
      (completedArrow l E L (j.comp i) D hl f c SE SL (h * e)
        (compositionRamification l E F i L j e h he hh)
        (one_le_mul hhpos hepos) M hM) ≫ _ = _ at norm₃
  have hχ := scalarCompletion_composition l E F i L j Y K
  change (baseTensor l F L j Y).map ((scalarCompletion l E F i Y).hom.app K) ≫
    (scalarCompletion l F L j Y).hom.app
      ((pbcDerivedExtend (completedCoefficientMap l E F i Y)).obj K) ≫
    (scalarConstantRestriction l L Y).map
      ((compositionCompleted l E F i L j Y).hom.app K) =
    (compositionBase l E F i L j Y).hom.app
      ((scalarConstantRestriction l E Y).obj K) ≫
    (scalarCompletion l E L (j.comp i) Y).hom.app K at hχ
  apply scalarConstantRestriction_complete_map_injective l L Y targetComplete
  exact scalarComposition_diagram
    (scalarCompletion l E F i Y) (scalarCompletion l F L j Y)
    (scalarCompletion l E L (j.comp i) Y)
    (compositionCompleted l E F i L j Y) (compositionBase l E F i L j Y)
    (completedArrow l E F i D hl f c SE SF e he hepos M hM)
    (completedArrow l F L j D hl f c SF SL h hh hhpos M₁ hM₁)
    (completedArrow l E L (j.comp i) D hl f c SE SL (h * e)
      (compositionRamification l E F i L j e h he hh) (one_le_mul hhpos hepos) M hM)
    ((scalarSupport l L c SL).map ((compositionCompleted l E F i L j X).hom.app M))
    ((scalarSupportLimit l E c SE).hom.app M)
    ((scalarSupportLimit l F c SF).hom.app M₁)
    ((scalarSupportLimit l L c SL).hom.app
      ((pbcDerivedExtend (completedCoefficientMap l F L j X)).obj M₁))
    ((scalarSupportLimit l L c SL).hom.app M₂)
    (scalarLimitArrow l E F i c SE SF e he hepos M)
    (scalarLimitArrow l F L j c SF SL h hh hhpos M₁)
    (scalarLimitArrow l E L (j.comp i) c SE SL (h * e)
      (compositionRamification l E F i L j e h he hh) (one_le_mul hhpos hepos) M)
    (((support l L c SL) ⋙ scalarLimit l L Y).map
      ((compositionCompleted l E F i L j X).hom.app M))
    hχ norm₁ norm₂ norm₃
    ((scalarSupportLimit l L c SL).hom.naturality
      ((compositionCompleted l E F i L j X).hom.app M))
    (compactSupportScalarLimitComposition l E F i L j D hl f c SE SF SL
      e h he hepos hh hhpos M hM)

end Geometry

/-- Identity on the constant coefficient ring, including its chosen integral model.
Source: auxiliary proof Step 6
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: the identity field embedding is identity on its valuation ring; constant
sheafification preserves the identity homomorphism and the universe lift. -/
theorem constantMap_identity (W : Scheme.{u}) :
    constantMap l E E (AlgHom.id ℚ_[l] E) W = 𝟙 _ := by
  unfold constantMap
  have hi : CommRingCat.ofHom
      (integralScalarIntegerInclusion l E E (AlgHom.id ℚ_[l] E)).ulift.{u + 1, u + 1} =
        𝟙 (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) := by
    ext x
    rfl
  rw [hi, CategoryTheory.Functor.map_id]

/-- The ordinary tensor multiplication unit, conjugate to identity restriction.
Source: Stacks 07A6; auxiliary proof Step 6
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionUnitOrdinary (W : Scheme.{u}) :
    pbcExtend (constantMap l E E (AlgHom.id ℚ_[l] E) W) ≅ 𝟭 _ :=
  eqToIso (congrArg (fun a ↦ pbcExtend a) (constantMap_identity l E W)) ≪≫
    ((conjugateIsoEquiv (pbcScalarAdjunction (𝟙 ((constants l E).ring W)))
      (Adjunction.id : (𝟭 (pbcModules W ((constants l E).ring W))) ⊣ 𝟭 _)).symm
        (PurCompactSupport.restrictIdentity_existsUnique
          ((constants l E).ring W)).exists.choose).symm

/-- The strict-tower tensor multiplication unit is localized from the ordinary one.
Source: Stacks 0940; auxiliary proof Step 6
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionUnitTower (W : Scheme.{u}) :
    T l E E (AlgHom.id ℚ_[l] E) W ≅ 𝟭 _ :=
  haveI := (tensor_exact l E E (AlgHom.id ℚ_[l] E) W).1
  haveI := (tensor_exact l E E (AlgHom.id ℚ_[l] E) W).2
  Functor.mapDerivedCategoryNatIso
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (compositionUnitOrdinary l E W)) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The completed tensor multiplication unit with the recorded adjunction normalization.
Source: Stacks 07A6; auxiliary proof Steps 6 and 9
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionUnitCompleted (W : Scheme.{u}) :
    pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) W) ≅ 𝟭 _ :=
  eqToIso (congrArg (fun a ↦ pbcDerivedExtend a)
      (PurCompactSupport.completedMap_identity l E W)) ≪≫
    PurCompactSupport.tensorIdentity ((PurCompactSupport.completed l E).ring W)

/-- Arithmetic selection by one is the identity on the ordinary strict tower category.
Source: auxiliary proof Step 6
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: n+1-1=n on objects; the order-category arrow and composite transitions agree. -/
theorem compositionSelectionOneOrdinary (W : Scheme.{u}) :
    ordinarySubsequence l E W 1 = 𝟭 _ := by
  have hi : CategoryTheory.StrictTowerArithmetic.index 1 = 𝟭 ℕᵒᵖ := by
    apply CategoryTheory.Functor.ext
    · intro a b f
      apply Subsingleton.elim
    · intro n
      cases n
      simp [CategoryTheory.StrictTowerArithmetic.index]
  change CategoryTheory.StrictTowerArithmetic.restriction _ 1 = _
  simp only [CategoryTheory.StrictTowerArithmetic.restriction, hi]
  rfl

/-- The canonical identity selection comparison on derived strict towers.
Source: Stacks 0940; auxiliary proof Step 6
(blueprint: lem-pur-compact-support-strict-scalar-composition). -/
def compositionSelectionOne (W : Scheme.{u}) : subsequence l E W 1 ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (eqToIso (compositionSelectionOneOrdinary l E W)) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Identity inclusion has ramification one, without an extra hypothesis.
Source: auxiliary proof Step 6
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: the integral inclusion is the identity, so mapping its uniformizer ideal fixes it. -/
theorem compositionRamificationOne :
    PurCompactSupport.Ramification l E E (AlgHom.id ℚ_[l] E) 1 := by
  have hi : integralScalarIntegerInclusion l E E (AlgHom.id ℚ_[l] E) =
      RingHom.id _ := by
    ext x
    rfl
  change Ideal.map _ _ = _
  rw [hi, Ideal.map_id]

/-- The actual identity-inclusion strict scalar mate is identity under the unit maps.
Source: Stacks 07A6, 0E8I; auxiliary proof Step 6
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: the proper square is identity and its mate is identity by mate pasting.
The open balancing map is tensor multiplication on the open and zero off it.
The unit-normalized reduction counits identify the retained tower at e=1 with
the original tower. Thus the three displayed unit comparisons give identity. -/
theorem compactSupportStrictScalarIdentity {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (arrow l E E (AlgHom.id ℚ_[l] E) c SE SE 1
        (compositionRamificationOne l E) (by decide)).app M ≫
        (compositionSelectionOne l E Y).hom.app
          ((support l E c SE).obj
            ((pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) X)).obj M)) ≫
        (support l E c SE).map ((compositionUnitCompleted l E X).hom.app M) =
      (compositionUnitTower l E Y).hom.app ((support l E c SE).obj M) := by
  sorry

private theorem quotientCast_apply (a b : ℕ) (hab : a = b)
    (x : Padic.coefficientExtensionIntegers l L) :
    (eqToHom (congrArg
      (fun m ↦ CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l L m)))
      hab)).hom (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L a) x)) =
        ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L b) x) := by
  cases hab
  rfl

/-- Finite quotient coefficient squares preserve the composite inclusion.
The final cast is exactly reassociation of h*(e*n) with (h*e)*n.
Source: auxiliary proof Steps 1 and 6
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: quotient induction reduces both maps to the same composite integral
inclusion. Associativity of multiplication identifies the target exponent;
constant sheafification preserves the resulting equation, including n=1. -/
theorem compositionFiniteCoefficients (W : Scheme.{u}) (e h : ℕ)
    (he : PurCompactSupport.Ramification l E F i e)
    (hh : PurCompactSupport.Ramification l F L j h) (n : ℕ) (_hn : 1 ≤ n) :
    PurCompactSupport.ramifiedSheafMap l E F i e he n W ≫
        PurCompactSupport.ramifiedSheafMap l F L j h hh (e * n) W ≫
        eqToHom (congrArg
          (fun m ↦ ((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).obj
            (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l L m)))))
          (Nat.mul_assoc h e n).symm) =
      PurCompactSupport.ramifiedSheafMap l E L (j.comp i) (h * e)
        (compositionRamification l E F i L j e h he hh) n W := by
  unfold PurCompactSupport.ramifiedSheafMap
  rw [← eqToHom_map (constantSheaf (ProEt.topology W) CommRingCat.{u + 1})
    (congrArg (fun m ↦ CommRingCat.of
      (ULift.{u + 1} (Padic.coefficientExtensionRing l L m))) (Nat.mul_assoc h e n).symm)]
  rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  rintro ⟨x⟩
  refine Quotient.inductionOn' x ?_
  intro x
  change (eqToHom (congrArg
    (fun m ↦ CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l L m)))
      (Nat.mul_assoc h e n).symm)).hom (ULift.up
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (h * (e * n)))
      (integralScalarIntegerInclusion l F L j (integralScalarIntegerInclusion l E F i x)))) = _
  rw [quotientCast_apply l L _ _ (Nat.mul_assoc h e n).symm]
  rfl

/-- Identity inclusions preserve every positive quotient coefficient map.
Source: auxiliary proof Step 6
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: quotient induction makes the map the identity on quotient representatives;
constant sheafification preserves identity maps. -/
theorem identityFiniteCoefficients (W : Scheme.{u}) (n : ℕ) (_hn : 1 ≤ n) :
    PurCompactSupport.ramifiedSheafMap l E E (AlgHom.id ℚ_[l] E) 1
        (compositionRamificationOne l E) n W ≫
        eqToHom (congrArg
          (fun m ↦ ((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).obj
            (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)))))
          (Nat.one_mul n)) = 𝟙 _ := by
  unfold PurCompactSupport.ramifiedSheafMap
  rw [← eqToHom_map (constantSheaf (ProEt.topology W) CommRingCat.{u + 1})
    (congrArg (fun m ↦ CommRingCat.of
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))) (Nat.one_mul n))]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  rintro ⟨x⟩
  refine Quotient.inductionOn' x ?_
  intro x
  change (eqToHom (congrArg
    (fun m ↦ CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)))
      (Nat.one_mul n))).hom (ULift.up
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (1 * n))
      (integralScalarIntegerInclusion l E E (AlgHom.id ℚ_[l] E) x))) = _
  rw [quotientCast_apply l E _ _ (Nat.one_mul n)]
  rfl

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] reductionChange reductionDerivedChange
  pbcScalarAdjunction pbcDerivedScalarAdjunction
  PurCompactSupport.tensorComposition
  PurCompactSupport.tensorIdentity

attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] completedCoefficientMap
  compositionCompleted compositionUnitCompleted
  completedIntegralCommRingSheafUnrestricted

private theorem compositionCompleted_identity_iso (W : Scheme.{u}) :
    compositionCompleted l E E (AlgHom.id ℚ_[l] E) E (AlgHom.id ℚ_[l] E) W =
      Functor.isoWhiskerRight (compositionUnitCompleted l E W)
          (pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) W)) ≪≫
        Functor.leftUnitor
          (pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) W)) := by
  delta compositionCompleted compositionUnitCompleted
  exact tensorComposition_identity_iso_of_eq (W := W)
    ((PurCompactSupport.completed l E).ring W)
    (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) W)
    (PurCompactSupport.completedMap_identity l E W)
    (PurCompactSupport.completedMap_composition l E E (AlgHom.id ℚ_[l] E)
      E (AlgHom.id ℚ_[l] E) W)

private theorem compositionCompleted_identity_left (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E W)) :
    (compositionCompleted l E E (AlgHom.id ℚ_[l] E) E (AlgHom.id ℚ_[l] E) W).hom.app K =
      (pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) W)).map
        ((compositionUnitCompleted l E W).hom.app K) := by
  rw [compositionCompleted_identity_iso]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  erw [Category.comp_id]

attribute [local irreducible] completedArrow scalarSupport
  completedAdicDerivedChange completedIntegralCoefficientSheafUnrestricted
  coefficientSequenceLimit scalarSupportNative


section IdentityGeometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))] [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))] [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc


/-- The completed comparisons form transformations on the full finite-Tor domain.
Source: auxiliary proof Steps 8--9
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: every factor of scalarLimitArrow is natural, and scalarCompletion and
scalarSupportLimit are natural isomorphisms. Their normalization equation and
uniqueness of completedArrow transport that naturality to completed coefficients. -/
theorem completedArrow_naturality (c : Compactification f)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M N : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M)
    (hN : finiteTorConstructibleIntegral l E X N) (a : M ⟶ N) :
    (pbcDerivedExtend (completedCoefficientMap l E F i Y)).map
          ((scalarSupport l E c SE).map a) ≫
        completedArrow l E F i D hl f c SE SF e he hepos N hN =
      completedArrow l E F i D hl f c SE SF e he hepos M hM ≫
        (scalarSupport l F c SF).map
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).map a) := by
  obtain ⟨γ, _, hγ⟩ := compactSupportScalarLimitReduction l E F i D hl f c SE SF e he hepos
  have hchosen (P : DerivedCategory (scalarReductionSource l E X))
      (hP : finiteTorConstructibleIntegral l E X P) :
      completedArrow l E F i D hl f c SE SF e he hepos P hP = γ.app ⟨P, hP⟩ := by
    unfold completedArrow
    apply (completedArrow_existsUnique l E F i D hl f c SE SF e he hepos P hP).unique
      (Classical.choose_spec
        (completedArrow_existsUnique l E F i D hl f c SE SF e he hepos P hP).exists)
    exact (hγ ⟨P, hP⟩).2.2.2.2.2.2.2.2.1.symm
  rw [hchosen M hM, hchosen N hN]
  exact γ.naturality (show (⟨M, hM⟩ : finiteTorConstructibleIntegralCategory l E X) ⟶
    ⟨N, hN⟩ from ObjectProperty.homMk a)

/-- The small interface of the uniquely normalized completed comparison.
Source: scalar-limit reduction, auxiliary proof Step 9
(blueprint: lem-pur-compact-support-strict-scalar-composition).
The existing reduction preserves the finite-Tor domain and supplies an invertible
transformation. Uniqueness of the normalization identifies its components with
completedArrow. Extract these properties before specializing coefficient maps. -/
private theorem completedArrow_properties (c : Compactification f)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    finiteTorConstructibleIntegral l F X
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) ∧
      IsIso (completedArrow l E F i D hl f c SE SF e he hepos M hM) := by
  obtain ⟨γ, hγ, hnorm⟩ := compactSupportScalarLimitReduction l E F i D hl f c SE SF
    e he hepos
  refine ⟨(hnorm ⟨M, hM⟩).1, ?_⟩
  have heq : completedArrow l E F i D hl f c SE SF e he hepos M hM =
      γ.app ⟨M, hM⟩ := by
    unfold completedArrow
    apply (completedArrow_existsUnique l E F i D hl f c SE SF e he hepos M hM).unique
      (Classical.choose_spec
        (completedArrow_existsUnique l E F i D hl f c SE SF e he hepos M hM).exists)
    exact (hnorm ⟨M, hM⟩).2.2.2.2.2.2.2.2.1.symm
  rw [heq]
  have := hγ
  exact NatIso.isIso_app_of_isIso γ ⟨M, hM⟩

/-- Gamma for the identity coefficient inclusion is tensor multiplication.
Source: auxiliary proof Steps 6--9
(blueprint: lem-pur-compact-support-strict-scalar-composition).
Proof: normalized adjunction composition identifies the identity associator with
scalar extension of the tensor unit. Apply completed composition to two identity
embeddings and naturality to the source unit. Scalar-limit reduction makes the
comparison invertible; cancellation and faithfulness of identity scalar extension
then give this equation. -/
theorem compactSupportCompletedScalarIdentity (c : Compactification f)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    completedArrow l E E (AlgHom.id ℚ_[l] E) D hl f c SE SE 1
        (compositionRamificationOne l E) (by decide) M hM ≫
        (scalarSupport l E c SE).map ((compositionUnitCompleted l E X).hom.app M) =
      (compositionUnitCompleted l E Y).hom.app ((scalarSupport l E c SE).obj M) := by
  have hprops := completedArrow_properties l E E (AlgHom.id ℚ_[l] E) D hl f c SE SE 1
    (compositionRamificationOne l E) (Nat.le_refl 1) M hM
  have hCM := hprops.1
  have := hprops.2
  refine target_unit_of_composition
    (pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) Y))
    (compositionUnitCompleted l E Y)
    (completedArrow l E E (AlgHom.id ℚ_[l] E) D hl f c SE SE 1
      (compositionRamificationOne l E) (Nat.le_refl 1) M hM)
    (completedArrow l E E (AlgHom.id ℚ_[l] E) D hl f c SE SE 1
      (compositionRamificationOne l E) (Nat.le_refl 1)
      ((pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) X)).obj M) hCM)
    ((scalarSupport l E c SE).map ((compositionUnitCompleted l E X).hom.app M))
    ((scalarSupport l E c SE).map
      ((compositionCompleted l E E (AlgHom.id ℚ_[l] E) E (AlgHom.id ℚ_[l] E) X).hom.app M))
    ((scalarSupport l E c SE).map
      ((pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) X)).map
        ((compositionUnitCompleted l E X).hom.app M)))
    ((compositionCompleted l E E (AlgHom.id ℚ_[l] E) E (AlgHom.id ℚ_[l] E) Y).hom.app
      ((scalarSupport l E c SE).obj M))
    (compositionCompleted_identity_left l E Y ((scalarSupport l E c SE).obj M)) ?_ ?_ ?_
  · exact congrArg (fun h ↦ (scalarSupport l E c SE).map h)
      (compositionCompleted_identity_left l E X M)
  · simpa only [AlgHom.comp_id] using
      compactSupportCompletedScalarComposition l E E (AlgHom.id ℚ_[l] E)
        E (AlgHom.id ℚ_[l] E) D hl f c SE SE SE
        1 1 (compositionRamificationOne l E) (Nat.le_refl 1)
        (compositionRamificationOne l E) (Nat.le_refl 1) M hM
  · exact completedArrow_naturality l E E (AlgHom.id ℚ_[l] E) D hl f c SE SE 1
      (compositionRamificationOne l E) (Nat.le_refl 1)
      ((pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id ℚ_[l] E) X)).obj M)
      M hCM hM ((compositionUnitCompleted l E X).hom.app M)

end IdentityGeometry
end WeilConjectures.PurStrictScalar
