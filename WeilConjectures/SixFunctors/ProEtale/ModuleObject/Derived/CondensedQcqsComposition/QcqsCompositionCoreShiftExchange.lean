/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.CondensedQcqsCompositionDefs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.CondensedQcqsCompositionDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.QcqsCompositionCoreShiftAlphaComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.KFlatDerivedAdjunctionTransportShifts
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.Shift.RestrictFullyFaithful
@[expose] public noncomputable section
set_option autoImplicit false
-- As in native compactification reindexing, check derived-category proofs sequentially.
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

private theorem commShift_of_whisker_eq
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (I : D ⥤ E) [I.CommShift ℤ] [I.Faithful]
    (e : F ⟶ G) (τ : F ⋙ I ⟶ G ⋙ I)
    (h : Functor.whiskerRight e I = τ) (hτ : NatTrans.CommShift τ ℤ) :
    NatTrans.CommShift e ℤ := by
  have : NatTrans.CommShift (Functor.whiskerRight e I) ℤ := by
    rw [h]
    exact hτ
  exact NatTrans.CommShift.of_whiskerRight e I

private theorem inverseMate_commShift
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    [G.CommShift ℤ] [H.CommShift ℤ] [L₁.CommShift ℤ] [R₁.CommShift ℤ]
    [L₂.CommShift ℤ] [R₂.CommShift ℤ]
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.CommShift ℤ] [adj₂.CommShift ℤ]
    (β : TwoSquare R₁ H G R₂) [β.natTrans.CommShift ℤ] :
    ((mateEquiv adj₁ adj₂).symm β).natTrans.CommShift ℤ := by
  change ((Functor.leftUnitor (G ⋙ L₂)).inv ≫
    Functor.whiskerRight adj₁.unit (G ⋙ L₂) ≫
    (Functor.associator (L₁ ⋙ R₁) G L₂).inv ≫
    Functor.whiskerRight (Functor.associator L₁ R₁ G).hom L₂ ≫
    Functor.whiskerRight (Functor.whiskerLeft L₁ β.natTrans) L₂ ≫
    Functor.whiskerRight (Functor.associator L₁ H R₂).inv L₂ ≫
    (Functor.associator (L₁ ⋙ H) R₂ L₂).hom ≫
    Functor.whiskerLeft (L₁ ⋙ H) adj₂.counit ≫
    (Functor.rightUnitor (L₁ ⋙ H)).hom).CommShift ℤ
  infer_instance

section Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem exactComparison_commShift {X Y : Scheme.{u}} (f : X ⟶ Y) :
    NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom ℤ :=
  (module_derived_functors_exact_and_comparison_shifts Λ f).2.2.1

private theorem squareComparison_commShift {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {w : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : CommSq w f' f v) :
    NatTrans.CommShift (pullbackSquareComparison Λ sq).hom ℤ := by
  change NatTrans.CommShift (modulePullbackSquareComparison Λ f v w f' sq.w.symm).hom ℤ
  constructor
  intro n
  ext K
  exact (module_pullback_square_shift Λ f v w f' sq.w.symm K n).symm

private theorem openAdjunction_commShift {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] :
    (CompactificationReindexing.oa Λ j).CommShift ℤ := by
  have := exactComparison_commShift Λ j
  have : NatTrans.CommShift
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm.hom ℤ := by
    change NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm.hom ℤ
    exact NatTrans.CommShift.of_iso_inv _ ℤ
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).commShift_mapDerivedCategoryAdjunction
  exact Adjunction.commShift_ofNatIsoRight _ _

private theorem openExchange_commShift {X Y X' Y' : Scheme.{u}}
    {j : X ⟶ Y} {j' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback w j' j v) :
    NatTrans.CommShift (CompactificationReindexing.beta Λ sq).hom ℤ := by
  have := squareComparison_commShift Λ sq.toCommSq
  have := openAdjunction_commShift Λ j
  have := openAdjunction_commShift Λ j'
  have : NatTrans.CommShift
      (CompactificationReindexing.openMate Λ sq.toCommSq) ℤ := by
    unfold CompactificationReindexing.openMate
    exact inverseMate_commShift _ _ _
  unfold CompactificationReindexing.beta
  infer_instance

set_option maxHeartbeats 2000000 in
-- Elaborating the native derived adjunction endpoints needs a larger heartbeat budget.
private theorem squareExchange_commShift {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {c : Compactification f} {c' : Compactification f'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : CompactificationReindexing.Square c c' w v) :
    NatTrans.CommShift (CompactificationReindexing.squareExchange Λ sq) ℤ := by
  have := (kflat_derived_adjunction_transport_shifts (Mon.mk Λ) c.g).2.2
  have := (kflat_derived_adjunction_transport_shifts (Mon.mk Λ) c'.g).2.2
  have := squareComparison_commShift Λ sq.properSquare
  have := openExchange_commShift Λ sq.openSquare
  have := NatTrans.CommShift.mateEquiv (A := ℤ)
    (derivedUpperStarLowerStarAdjunction Λ c.g)
    (derivedUpperStarLowerStarAdjunction Λ c'.g)
    (TwoSquare.mk _ _ _ _ (pullbackSquareComparison Λ sq.properSquare).hom)
  unfold CompactificationReindexing.squareExchange
    CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
  infer_instance

end Ambient

private abbrev nativeCoeff (ℓ : ℕ) [Fact ℓ.Prime] :=
  Profinite.padicAlgClRingObj ℓ

private def nativeExchangeSquare {X Y : Scheme.{u}} {f : X ⟶ Y}
    (a : X ≅ X) (b : Y ≅ Y) (sq : IsPullback a.hom f f b.hom)
    (c : Compactification f) :
    CompactificationReindexing.Square c (c.ofIsPullback sq) a.hom b.hom where
  middle := pullback.fst c.g b.hom
  openSquare := c.isPullback_i_ofIsPullback sq
  properSquare := (c.isPullback_g_ofIsPullback sq).flip.toCommSq

private theorem nativeExchangeWord_eq (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (S : System ℓ f)
    (a : X ≅ X) (b : Y ≅ Y) (sq : IsPullback a.hom f f b.hom)
    (E : Exchange ℓ S a b sq) (c : Compactification f) :
    Functor.whiskerRight (E.iso c).hom (bc ℓ Y).ι =
      exchangeTransformation ℓ S a b sq c := by
  ext K
  change ((E.iso c).hom.app K).hom = _
  simpa only [exchangeComponent.eq_def] using E.normalized c K

set_option maxHeartbeats 2000000 in
-- The native shift specialization has a larger elaboration budget.
private theorem exchange_commShift (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [(bc ℓ X).IsTriangulated] [(bc ℓ Y).IsTriangulated]
    (S : System ℓ f) (a : X ≅ X) (b : Y ≅ Y)
    (sq : IsPullback a.hom f f b.hom) (E : Exchange ℓ S a b sq)
    (hcomp : ∀ c d, NatTrans.CommShift (S.comparison c d).hom ℤ)
    (c : Compactification f) : NatTrans.CommShift (E.iso c).hom ℤ := by
  have ha := exactComparison_commShift (nativeCoeff ℓ) a.hom
  have hb := exactComparison_commShift (nativeCoeff ℓ) b.hom
  have hs := squareExchange_commShift (nativeCoeff ℓ)
    (nativeExchangeSquare a b sq c)
  have hc := hcomp (c.ofIsPullback sq) c
  have ht : NatTrans.CommShift (exchangeTransformation ℓ S a b sq c) ℤ := by
    as_aux_lemma =>
      unfold exchangeTransformation
      exact ObjectProperty.exchangeWord_commShift
        (catC₀ :=
          inferInstanceAs (Category (CompactificationReindexing.D (nativeCoeff ℓ) X)))
        (catD₀ :=
          inferInstanceAs (Category (CompactificationReindexing.D (nativeCoeff ℓ) Y)))
        (shiftC₀ :=
          inferInstanceAs (HasShift (CompactificationReindexing.D (nativeCoeff ℓ) X) ℤ))
        (shiftD₀ :=
          inferInstanceAs (HasShift (CompactificationReindexing.D (nativeCoeff ℓ) Y) ℤ))
        (_iF :=
          inferInstanceAs ((CompactificationReindexing.F (nativeCoeff ℓ)
            c).CommShift ℤ))
        (_iG :=
          inferInstanceAs ((CompactificationReindexing.F (nativeCoeff ℓ)
            (c.ofIsPullback sq)).CommShift ℤ))
        (_iA := inferInstanceAs ((StrictWeilCondensed.action (nativeCoeff ℓ) a).CommShift ℤ))
        (_iPa :=
          inferInstanceAs ((CompactificationReindexing.P (nativeCoeff ℓ) a.hom).CommShift ℤ))
        (_iB := inferInstanceAs ((StrictWeilCondensed.action (nativeCoeff ℓ) b).CommShift ℤ))
        (_iPb :=
          inferInstanceAs ((CompactificationReindexing.P (nativeCoeff ℓ) b.hom).CommShift ℤ))
        (_ixa := ha) (_ixb := hb) (_iσ := hs) (_iρ := hc)
        (hP := inferInstanceAs (HasShift (C ℓ X) ℤ))
        (hQ := inferInstanceAs (HasShift (C ℓ Y) ℤ))
        (iP := inferInstanceAs ((bc ℓ X).ι.CommShift ℤ))
        (iQ := inferInstanceAs ((bc ℓ Y).ι.CommShift ℤ))
        (_iT := inferInstanceAs ((S.support ℓ c).CommShift ℤ))
        (_ia := inferInstanceAs ((pull ℓ a).CommShift ℤ))
        (_ib := inferInstanceAs ((pull ℓ b).CommShift ℤ))
        (bc ℓ X) (bc ℓ Y)
        (CompactificationReindexing.F (nativeCoeff ℓ) c)
        (CompactificationReindexing.F
            (nativeCoeff ℓ) (c.ofIsPullback sq))
        (StrictWeilCondensed.action (nativeCoeff ℓ) a)
        (CompactificationReindexing.P (nativeCoeff ℓ) a.hom)
        (StrictWeilCondensed.action (nativeCoeff ℓ) b)
        (CompactificationReindexing.P (nativeCoeff ℓ) b.hom)
        (leftDerivedUpperStarIsoMapDerivedCategory (nativeCoeff ℓ) a.hom)
        (leftDerivedUpperStarIsoMapDerivedCategory (nativeCoeff ℓ) b.hom)
        (S.preserves c)
        (fun K ↦ ((StrictWeilCondensed.action_preserves (nativeCoeff ℓ) a K.obj).1).2 K.property)
        (fun K ↦ ((StrictWeilCondensed.action_preserves (nativeCoeff ℓ) b K.obj).1).2 K.property)
        (CompactificationReindexing.squareExchange (nativeCoeff ℓ) (nativeExchangeSquare a b sq
          c)) (S.comparison (c.ofIsPullback sq) c)
  have he := nativeExchangeWord_eq ℓ S a b sq E c
  exact commShift_of_whisker_eq (bc ℓ Y).ι (E.iso c).hom
    (exchangeTransformation ℓ S a b sq c) he ht

set_option maxHeartbeats 2000000 in
-- The normalized derived-functor composites elaborate beyond the default heartbeat budget.
/-- Shift compatibility of all normalized exchange isomorphisms, for the qcqs
compactification comparison data of the geometric fibres of separated morphisms of finite
type over a finite field.
Source: Stacks Tag 0F7J and the shift-calculus compatibility lemmas (Tag 05SU).
(blueprint: new-r2-qcqs-composition-core-shift-exchange).
Proof: by `Exchange.normalized` the underlying map of each component is
`exchangeComponent`: the exact-to-total pullback identification for `b`, the canonical
proper/open square exchange, the image of the identification for `a`, and a refinement
comparison. Each factor commutes with the canonical shifts by the qcqs proper/open calculus
(the comparison as in the compositor case), hence so does the composite, and the full
subcategory inclusion is faithful and shift-compatible, so the equation transports to the
components of `(A.exchange …).iso`. -/
theorem qcqsCompositionCoreShiftExchange (ℓ : ℕ) [Fact ℓ.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p)
    {X₀ Z₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [QuasiSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj X₀).left)).IsTriangulated]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj Z₀).left)).IsTriangulated]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj Y₀).left)).IsTriangulated]
    (A : Comparisons ℓ (modelMap D h₀) (modelMap D g₀)) :
    ∀ (a : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj X₀).left ≅
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj X₀).left)
      (b : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj Z₀).left ≅
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj Z₀).left)
      (v : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj Y₀).left ≅
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj Y₀).left)
      (shsq : IsPullback a.hom (modelMap D h₀) (modelMap D h₀) b.hom)
      (sgsq : IsPullback b.hom (modelMap D g₀) (modelMap D g₀) v.hom),
      (∀ c : Compactification (modelMap D h₀),
        NatTrans.CommShift ((A.exchange a b v shsq sgsq).1.iso c).hom ℤ) ∧
      (∀ d : Compactification (modelMap D g₀),
        NatTrans.CommShift ((A.exchange a b v shsq sgsq).2.1.iso d).hom ℤ) ∧
      (∀ e : Compactification (modelMap D h₀ ≫ modelMap D g₀),
        NatTrans.CommShift ((A.exchange a b v shsq sgsq).2.2.iso e).hom ℤ) := by
  obtain ⟨hh, hg, hhg⟩ := qcqsCompositionCoreShiftAlphaComparison ℓ D hℓ h₀ g₀ A
  intro a b v shsq sgsq
  exact ⟨exchange_commShift ℓ A.sh a b shsq (A.exchange a b v shsq sgsq).1 hh,
    exchange_commShift ℓ A.sg b v sgsq (A.exchange a b v shsq sgsq).2.1 hg,
    exchange_commShift ℓ A.sgh a v (shsq.paste_vert sgsq)
      (A.exchange a b v shsq sgsq).2.2 hhg⟩
end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
