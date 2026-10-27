/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.SixFunctors.CoefWeilLeftExchangeCompatibility
import Sheaf.Paper.SemilinearFieldOperationLifts
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction

/-! # Weil lifts of the specified exceptional coefficient adjunctions

Source: blueprint `cor-coef-verdier-weil-equivariance`, proof paragraph 3
(blueprint: lem-coef-weil-exceptional-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v a b a' b' u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures
open CoefVerdierWeil
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)
open CategoryTheory.Endofunctor (IsoAlgebra)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem mate_scalar_square
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (adj : F ⊣ G) (adj' : F' ⊣ G')
    (P : C ⥤ C) (Q : D ⥤ D) (P' : C' ⥤ C') (Q' : D' ⥤ D')
    (L : C ⥤ C') (M : D ⥤ D')
    (a : F ⋙ Q ≅ P ⋙ F) (a' : F' ⋙ Q' ≅ P' ⋙ F')
    (alpha : F ⋙ M ≅ L ⋙ F') (beta : G ⋙ L ≅ M ⋙ G')
    (s : L ⋙ P' ≅ P ⋙ L) (t : M ⋙ Q' ≅ Q ⋙ M)
    (hc : ∀ N, alpha.hom.app (G.obj N) ≫ F'.map (beta.hom.app N) ≫
      adj'.counit.app (M.obj N) = M.map (adj.counit.app N))
    (hsq : ∀ K, t.hom.app (F.obj K) ≫ M.map (a.hom.app K) ≫
      alpha.hom.app (P.obj K) = Q'.map (alpha.hom.app K) ≫
        a'.hom.app (L.obj K) ≫ F'.map (s.hom.app K)) (N : D) :
    s.hom.app (G.obj N) ≫
      L.map ((mateEquiv adj adj (TwoSquare.mk _ _ _ _ a.inv)).natTrans.app N) ≫
        beta.hom.app (Q.obj N) =
      P'.map (beta.hom.app N) ≫
        (mateEquiv adj' adj' (TwoSquare.mk _ _ _ _ a'.inv)).natTrans.app (M.obj N) ≫
        G'.map (t.hom.app N) := by
  let b := (mateEquiv adj adj (TwoSquare.mk _ _ _ _ a.inv)).natTrans
  let b' := (mateEquiv adj' adj' (TwoSquare.mk _ _ _ _ a'.inv)).natTrans
  have hb : a.hom.app (G.obj N) ≫ F.map (b.app N) ≫
      adj.counit.app (Q.obj N) = Q.map (adj.counit.app N) := by
    dsimp only [b]
    rw [mateEquiv_counit]
    simp
  have hb' : a'.hom.app (G'.obj (M.obj N)) ≫ F'.map (b'.app (M.obj N)) ≫
      adj'.counit.app (Q'.obj (M.obj N)) = Q'.map (adj'.counit.app (M.obj N)) := by
    dsimp only [b']
    rw [mateEquiv_counit]
    simp
  have hα := alpha.hom.naturality (b.app N)
  have ha := a'.hom.naturality (beta.hom.app N)
  have ht := t.hom.naturality (adj.counit.app N)
  have hε := adj'.counit.naturality (t.hom.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hα ha ht hε
  apply (adj'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, F'.map_comp, Category.assoc]
  apply (cancel_epi (Q'.map (alpha.hom.app (G.obj N)) ≫
    a'.hom.app (L.obj (G.obj N)))).1
  simp only [Category.assoc]
  calc
    _ = t.hom.app (F.obj (G.obj N)) ≫ M.map (a.hom.app (G.obj N)) ≫
        alpha.hom.app (P.obj (G.obj N)) ≫ F'.map (L.map (b.app N)) ≫
        F'.map (beta.hom.app (Q.obj N)) ≫ adj'.counit.app (M.obj (Q.obj N)) := by
      rw [← reassoc_of% (hsq (G.obj N))]
    _ = t.hom.app (F.obj (G.obj N)) ≫ M.map (Q.map (adj.counit.app N)) := by
      rw [← reassoc_of% hα, hc (Q.obj N), ← M.map_comp_assoc, ← M.map_comp, Category.assoc, hb]
    _ = Q'.map (M.map (adj.counit.app N)) ≫ t.hom.app N := ht.symm
    _ = Q'.map (alpha.hom.app (G.obj N)) ≫
        a'.hom.app (L.obj (G.obj N)) ≫ F'.map (P'.map (beta.hom.app N)) ≫
        F'.map (b'.app (M.obj N)) ≫ F'.map (G'.map (t.hom.app N)) ≫
        adj'.counit.app (M.obj (Q.obj N)) := by
      rw [← hc N, Q'.map_comp, Q'.map_comp]
      simp only [Category.assoc]
      rw [← reassoc_of% hb', ← reassoc_of% ha]
      rw [hε]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

@[irreducible] private def exceptionalOfLeft
    {C : Type a} {B : Type b} [Category C] [Category B]
    {F : C ⥤ B} {G : B ⥤ C} (adj : F ⊣ G)
    (P : C ⥤ C) (Q : B ⥤ B) [P.IsEquivalence] [Q.IsEquivalence]
    (left : F ⋙ Q ≅ P ⋙ F) : Exceptional P Q adj where
  left := left
  right := IsoAlgebra.mateIso adj left
  mate := rfl
  unit K := by
    simpa only [IsoAlgebra.mapOfNatIso_obj_str, ← IsoAlgebra.str_hom,
      Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      IsoAlgebra.mapOfNatIso_obj_carrier, Functor.map_comp, Category.assoc] using
      (IsoAlgebra.map_unit_app_comp_str adj left (IsoAlgebra.mateIso adj left) rfl K).symm
  counit K := by
    simpa only [IsoAlgebra.mapOfNatIso_obj_str, ← IsoAlgebra.str_hom,
      Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      IsoAlgebra.mapOfNatIso_obj_carrier, Functor.map_comp, Category.assoc] using
      (IsoAlgebra.map_counit_app_comp_str adj left (IsoAlgebra.mateIso adj left) rfl K).symm

private theorem exceptionalOfLeft_left
    {C : Type a} {B : Type b} [Category C] [Category B]
    {F : C ⥤ B} {G : B ⥤ C} (adj : F ⊣ G)
    (P : C ⥤ C) (Q : B ⥤ B)
    (hP : P.IsEquivalence) (hQ : Q.IsEquivalence)
    (left : F ⋙ Q ≅ P ⋙ F) :
    (@exceptionalOfLeft C B _ _ F G adj P Q hP hQ left).left = left := by
  unfold exceptionalOfLeft
  rfl

private theorem exceptionalComparison_of_left_square
    {C : Type a} {C' : Type a'} {B : Type b} {B' : Type b'}
    [Category C] [Category C'] [Category B] [Category B']
    {P : C ⥤ C} {P' : C' ⥤ C'} {Q : B ⥤ B} {Q' : B' ⥤ B'}
    {F : C ⥤ B} {G : B ⥤ C} {F' : C' ⥤ B'} {G' : B' ⥤ C'}
    {adj : F ⊣ G} {adj' : F' ⊣ G'}
    (W : Exceptional P Q adj) (W' : Exceptional P' Q' adj')
    (L : C ⥤ C') (M : B ⥤ B') (s : L ⋙ P' ≅ P ⋙ L) (t : M ⋙ Q' ≅ Q ⋙ M)
    (alpha : F ⋙ M ≅ L ⋙ F') (beta : G ⋙ L ≅ M ⋙ G')
    (hc : ∀ N, alpha.hom.app (G.obj N) ≫ F'.map (beta.hom.app N) ≫
      adj'.counit.app (M.obj N) = M.map (adj.counit.app N))
    (hsq : ∀ K, t.hom.app (F.obj K) ≫ M.map (W.left.hom.app K) ≫
      alpha.hom.app (P.obj K) = Q'.map (alpha.hom.app K) ≫
        W'.left.hom.app (L.obj K) ≫ F'.map (s.hom.app K)) :
    ExceptionalComparison W W' L M s t alpha beta := by
  have hr := mate_scalar_square adj adj' P Q P' Q' L M W.left W'.left alpha beta s t hc hsq
  rw [← W.mate, ← W'.mate] at hr
  constructor
  · intro K
    have hn := alpha.hom.naturality K.str.hom
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    dsimp only [IsEquivariant, transportedStructure, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, IsoAlgebra.mk_carrier, IsoAlgebra.mk_str]
    simp only [M.map_comp, Category.assoc]
    rw [hn]
    have h := congrArg (fun x ↦ x ≫ F'.map (L.map K.str.hom)) (hsq K.carrier)
    simpa only [IsoAlgebra.mk_str, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, F'.map_comp, Category.assoc] using h
  · intro K
    have hn := beta.hom.naturality K.str.hom
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    dsimp only [IsEquivariant, transportedStructure, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, IsoAlgebra.mk_carrier, IsoAlgebra.mk_str]
    simp only [L.map_comp, Category.assoc]
    rw [hn]
    have h := congrArg (fun x ↦ x ≫ G'.map (M.map K.str.hom)) (hr K.carrier)
    simpa only [IsoAlgebra.mk_str, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, G'.map_comp, Category.assoc] using h


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Cache just the rational equivalence conclusion of the field-transport theorem. -/
private theorem rationalFrobeniusEquivalence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom]
    [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (sfWeilFrobeniusPullback D l hl T₀ E).IsEquivalence :=
  ((semilinearFieldOperationLifts D l hl T₀ T₀ (𝟙 T₀) E Ω).2.2.1).1.2.2.2.2.2.2.2.1

/-- Cache just the common-stage equivalence conclusion. -/
private theorem commonFrobeniusEquivalence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom]
    [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
    (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).IsEquivalence :=
  ((semilinearFieldOperationLifts D l hl T₀ T₀ (𝟙 T₀)
    (Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω)) Ω).2.2.1).2.1

private theorem finiteCounitSquare
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (c₀ : Compactification f₀.left)
    (A : FiberExceptional D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀))
    (E F : Index l Ω) (h : E ≤ F)
    (N : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
      (D.geometricFiber Y₀).left) :
    (fiberLeftScalar D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀) A E F h).hom.app
        ((fiberRight D l hl Ω X₀ f₀ (FrobeniusExchange.geometricCompactification D f₀ c₀)
          A E).obj N) ≫
      (fiberLeft D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A F).map
        ((fiberRightScalar D l hl Ω X₀ f₀
          (FrobeniusExchange.geometricCompactification D f₀ c₀) A E F h).hom.app N) ≫
      (fiberAdjunction D l hl Ω X₀ f₀ (FrobeniusExchange.geometricCompactification D f₀ c₀)
          A F).counit.app
        ((transition l Ω (D.geometricFiber Y₀).left E F h).obj N) =
      (transition l Ω (D.geometricFiber Y₀).left E F h).map
        ((fiberAdjunction D l hl Ω X₀ f₀ (FrobeniusExchange.geometricCompactification D f₀ c₀)
          A E).counit.app N) := by
  have := fiberStructureLocallyFiniteType D X₀
  have := fiberStructureQuasiCompact D X₀
  have := fiberStructureSeparated D X₀
  have := fiberStructureLocallyFiniteType D Y₀
  have := fiberStructureQuasiCompact D Y₀
  have := fiberStructureSeparated D Y₀
  have := fiberMapSeparated D f₀
  have := fiberMapLocallyFiniteType D f₀
  have := fiberMapQuasiCompact D f₀
  have : (FrobeniusExchange.fiberMap D f₀).IsOver (Spec (.of D.k)) := by
    with_unfolding_all
      exact ⟨((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap D.k₀ D.k)))).map f₀).w⟩
  let d := A.system.fields.rationalComparison
    (FrobeniusExchange.geometricCompactification D f₀ c₀)
    (CoefQbarVerdier.fieldStage l Ω E) (CoefQbarVerdier.fieldStage l Ω F)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E F h)
  let := d.shiftX
  let := d.shiftY
  exact d.comparison.counit N

private theorem stageCounitSquare
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (c₀ : Compactification f₀.left)
    (A : FiberExceptional D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀))
    (E : Index l Ω)
    (N : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
      (D.geometricFiber Y₀).left) :
    (fiberLeftComparison D l hl Ω X₀ f₀ (FrobeniusExchange.geometricCompactification D f₀ c₀)
          A E).hom.app
      ((fiberRight D l hl Ω X₀ f₀ (FrobeniusExchange.geometricCompactification D f₀ c₀)
          A E).obj N) ≫
    (fiberCommonLeft D l hl Ω X₀ f₀ (FrobeniusExchange.geometricCompactification D f₀ c₀) A).map
      ((fiberRightComparison D l hl Ω X₀ f₀ (FrobeniusExchange.geometricCompactification D f₀ c₀)
          A E).hom.app N) ≫
    (fiberCommonAdjunction D l hl Ω X₀ f₀ (FrobeniusExchange.geometricCompactification D f₀ c₀)
          A).counit.app
      ((fiberInclusion D l Ω Y₀ E).obj N) =
    (fiberInclusion D l Ω Y₀ E).map
      ((fiberAdjunction D l hl Ω X₀ f₀ (FrobeniusExchange.geometricCompactification D f₀ c₀)
          A E).counit.app N) := by
  have := fiberStructureLocallyFiniteType D X₀
  have := fiberStructureQuasiCompact D X₀
  have := fiberStructureSeparated D X₀
  have := fiberStructureLocallyFiniteType D Y₀
  have := fiberStructureQuasiCompact D Y₀
  have := fiberStructureSeparated D Y₀
  have := fiberMapSeparated D f₀
  have := fiberMapLocallyFiniteType D f₀
  have := fiberMapQuasiCompact D f₀
  exact A.properties.2.2.2.2.2.1 E N

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Transport normalization along specified equations of the left components. -/
private def pinByLeft {I : Type u₁}
    (F : I → Type a) (G : Type b) (LF : I → Type a') (LG : Type b')
    (leftF : ∀ i, F i → LF i) (leftG : G → LG)
    (finiteNorm : (∀ i, LF i) → Prop) (commonNorm : LG → Prop)
    (finite : ∀ i, F i) (common : G) (lfinite : ∀ i, LF i) (lcommon : LG)
    (hf : ∀ i, leftF i (finite i) = lfinite i) (hg : leftG common = lcommon)
    (hnf : finiteNorm lfinite) (hng : commonNorm lcommon) :
    PinnedFrobeniusAdjunctions F G
      (fun x ↦ finiteNorm (fun i ↦ leftF i (x i)))
      (fun y ↦ commonNorm (leftG y)) where
  finite := finite
  common := common
  finiteNormalized := by
    rw [funext hf]
    exact hnf
  commonNormalized := by
    rw [hg]
    exact hng

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The mate construction on the specified finite and common adjunctions. -/
@[irreducible] private def pinnedOfLeft
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (c₀ : Compactification f₀.left)
    (A : CoefVerdierWeil.FiberExceptional D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀))
    {BX : CoefVerdierWeil.FiberDuality D l hl Ω X₀}
    {BY : CoefVerdierWeil.FiberDuality D l hl Ω Y₀}
    (WX : CoefVerdierWeil.Coefficients D l hl Ω X₀ BX)
    (WY : CoefVerdierWeil.Coefficients D l hl Ω Y₀ BY)
    (L : CoefVerdierWeil.LeftExchanges D l hl Ω X₀ f₀ c₀ A WX WY) :
    CoefVerdierWeil.FrobeniusAdjunctions D l hl Ω X₀ f₀ c₀ A := by
  have hCX : (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).IsEquivalence :=
    commonFrobeniusEquivalence D l hl Ω X₀
  have hCY : (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).IsEquivalence :=
    commonFrobeniusEquivalence D l hl Ω Y₀
  exact pinByLeft
    (finiteExceptionalType D l hl Ω X₀ f₀ c₀ A)
    (commonExceptionalType D l hl Ω X₀ f₀ c₀ A)
    (finiteLeftExchangeType D l hl Ω X₀ f₀ c₀ A)
    (commonLeftExchangeType D l hl Ω X₀ f₀ c₀ A)
    (fun _ x ↦ x.left) (fun x ↦ x.left)
    (finiteLeftExchangeLaw D l hl Ω X₀ f₀ c₀ A)
    (commonLeftExchangeLaw D l hl Ω X₀ f₀ c₀ A)
    (fun E ↦ by
      have hX : (sfWeilFrobeniusPullback D l hl X₀
          (Coefficient.{u} l Ω E)).IsEquivalence :=
        rationalFrobeniusEquivalence D l hl Ω X₀ (Coefficient.{u} l Ω E)
      have hY : (sfWeilFrobeniusPullback D l hl Y₀
          (Coefficient.{u} l Ω E)).IsEquivalence :=
        rationalFrobeniusEquivalence D l hl Ω Y₀ (Coefficient.{u} l Ω E)
      exact @exceptionalOfLeft (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
          (D.geometricFiber X₀).left)
        (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
          (D.geometricFiber Y₀).left)
        _ _
        (fiberLeft D l hl Ω X₀ f₀
          (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
        (fiberRight D l hl Ω X₀ f₀
          (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
        (CoefVerdierWeil.fiberAdjunction D l hl Ω X₀ f₀
          (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
        (sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E))
        (sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E)) hX hY (L.finite E))
    (@exceptionalOfLeft
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left)
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
      _ _
      (fiberCommonLeft D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A)
      (fiberCommonRight D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A)
      (fiberCommonAdjunction D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A) _ _ hCX hCY L.common)
    L.finite L.common
    (fun E ↦ @exceptionalOfLeft_left
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
        (D.geometricFiber X₀).left)
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
        (D.geometricFiber Y₀).left)
      _ _
      (fiberLeft D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
      (fiberRight D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
      (fiberAdjunction D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
      (sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E))
      (sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E))
      (rationalFrobeniusEquivalence D l hl Ω X₀ (Coefficient.{u} l Ω E))
      (rationalFrobeniusEquivalence D l hl Ω Y₀ (Coefficient.{u} l Ω E))
      (L.finite E))
    (@exceptionalOfLeft_left
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left)
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
      _ _
      (fiberCommonLeft D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A)
      (fiberCommonRight D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A)
      (fiberCommonAdjunction D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A)
      (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
      (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω)
      (commonFrobeniusEquivalence D l hl Ω X₀)
      (commonFrobeniusEquivalence D l hl Ω Y₀) L.common)
    L.finiteNormalized L.commonNormalized

private theorem pinnedOfLeft_finite_left
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (c₀ : Compactification f₀.left)
    (A : CoefVerdierWeil.FiberExceptional D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀))
    {BX : CoefVerdierWeil.FiberDuality D l hl Ω X₀}
    {BY : CoefVerdierWeil.FiberDuality D l hl Ω Y₀}
    (WX : CoefVerdierWeil.Coefficients D l hl Ω X₀ BX)
    (WY : CoefVerdierWeil.Coefficients D l hl Ω Y₀ BY)
    (L : CoefVerdierWeil.LeftExchanges D l hl Ω X₀ f₀ c₀ A WX WY) (E : Index l Ω) :
    ((pinnedOfLeft D l hl Ω X₀ f₀ c₀ A WX WY L).finite E).left = L.finite E := by
  simp only [pinnedOfLeft, pinByLeft]
  exact @exceptionalOfLeft_left
    (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
      (D.geometricFiber X₀).left)
    (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
      (D.geometricFiber Y₀).left)
    _ _
    (fiberLeft D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
    (fiberRight D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
    (fiberAdjunction D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
    (sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E))
    (sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E))
    (rationalFrobeniusEquivalence D l hl Ω X₀ (Coefficient.{u} l Ω E))
    (rationalFrobeniusEquivalence D l hl Ω Y₀ (Coefficient.{u} l Ω E))
    (L.finite E)

private theorem pinnedOfLeft_common_left
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (c₀ : Compactification f₀.left)
    (A : CoefVerdierWeil.FiberExceptional D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀))
    {BX : CoefVerdierWeil.FiberDuality D l hl Ω X₀}
    {BY : CoefVerdierWeil.FiberDuality D l hl Ω Y₀}
    (WX : CoefVerdierWeil.Coefficients D l hl Ω X₀ BX)
    (WY : CoefVerdierWeil.Coefficients D l hl Ω Y₀ BY)
    (L : CoefVerdierWeil.LeftExchanges D l hl Ω X₀ f₀ c₀ A WX WY) :
    (pinnedOfLeft D l hl Ω X₀ f₀ c₀ A WX WY L).common.left = L.common := by
  simp only [pinnedOfLeft, pinByLeft]
  exact @exceptionalOfLeft_left
    (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left)
    (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
    _ _
    (fiberCommonLeft D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀) A)
    (fiberCommonRight D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀) A)
    (fiberCommonAdjunction D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀) A)
    (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
    (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω)
    (commonFrobeniusEquivalence D l hl Ω X₀)
    (commonFrobeniusEquivalence D l hl Ω Y₀) L.common

/-- The given exceptional coefficient adjunction lifts to Weil pairs, with its
original unit and counit and the normalized finite and common-stage exchanges.
It constructs no duality and assumes no exceptional-duality formula.

Source: blueprint `cor-coef-verdier-weil-equivariance`, proof paragraphs 1 and 3
(blueprint: lem-coef-weil-exceptional-compatibility).

Proof: use the supplied normalized left exchanges. At both coefficient stages,
take the mate of inverse left exchange under the actual adjunction; the Frobenius
pullback equivalences make the mate invertible. The proved unit and counit formulas
for IsoAlgebra.mateIso give the two equations on arbitrary Weil objects.

For the right scalar square, transpose both routes under the target adjunction.
Precompose with the invertible composite of the left coefficient comparison and
target left exchange. The left scalar square and the specified coefficient counit
identity identify the two transposes. Cancel that composite and use adjunction
injectivity. Naturality of the original left and right coefficient comparisons
then gives equivariance after composing with arbitrary input structure maps.
Apply this calculation first to finite field transitions and then to the actual
finite-to-common inclusion comparisons. The left-exchange normalizations are
retained verbatim, as are the underlying functors, units, counits and adjunctions. -/
theorem coef_weil_exceptional_compatibility
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    {Y₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType Y₀.hom]
    [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (c₀ : Compactification f₀.left)
    (A : CoefVerdierWeil.FiberExceptional D l hl Ω X₀ f₀
      (FrobeniusExchange.geometricCompactification D f₀ c₀))
    {BX : CoefVerdierWeil.FiberDuality D l hl Ω X₀}
    {BY : CoefVerdierWeil.FiberDuality D l hl Ω Y₀}
    (WX : CoefVerdierWeil.Coefficients D l hl Ω X₀ BX)
    (WY : CoefVerdierWeil.Coefficients D l hl Ω Y₀ BY)
    (L : CoefVerdierWeil.LeftExchanges D l hl Ω X₀ f₀ c₀ A WX WY) :
    Nonempty (CoefVerdierWeil.Adjunctions D l hl Ω X₀ f₀ c₀ A WX WY) := by
  let Z := pinnedOfLeft D l hl Ω X₀ f₀ c₀ A WX WY L
  refine ⟨{ toFrobeniusAdjunctions := Z, scalar := ?_, stage := ?_ }⟩
  · intro E F h
    apply exceptionalComparison_of_left_square
    · exact finiteCounitSquare D l hl Ω X₀ f₀ c₀ A E F h
    · simpa only [Z, pinnedOfLeft_finite_left, scalarLeftExchangeLaw] using L.scalar E F h
  · intro E
    have hstage := @exceptionalComparison_of_left_square
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
        (D.geometricFiber X₀).left)
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left)
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
        (D.geometricFiber Y₀).left)
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
      _ _ _ _
      (sfWeilFrobeniusPullback D l hl X₀ (Coefficient.{u} l Ω E))
      (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
      (sfWeilFrobeniusPullback D l hl Y₀ (Coefficient.{u} l Ω E))
      (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω)
      (fiberLeft D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
      (fiberRight D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
      (fiberCommonLeft D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A)
      (fiberCommonRight D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A)
      (fiberAdjunction D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
      (fiberCommonAdjunction D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A)
      (Z.finite E) Z.common
      (fiberInclusion D l Ω X₀ E)
      (fiberInclusion D l Ω Y₀ E)
      (WX.stageFrobenius E) (WY.stageFrobenius E)
      (fiberLeftComparison D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
      (fiberRightComparison D l hl Ω X₀ f₀
        (FrobeniusExchange.geometricCompactification D f₀ c₀) A E)
      (stageCounitSquare D l hl Ω X₀ f₀ c₀ A E) (by
        simpa only [Z, pinnedOfLeft_finite_left, pinnedOfLeft_common_left,
          stageLeftExchangeLaw] using L.stage E)
    exact hstage

end WeilConjectures
