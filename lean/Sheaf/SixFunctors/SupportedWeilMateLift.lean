module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.FieldWeilShriekShiftData
public import Sheaf.Paper.WeilIndSheafCategory
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction

import Sheaf.Paper.AutomorphismConstructibleStageEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-! # The supported right adjoint and its normalized Weil lift

Source: main-20261015, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-localization-all-stages.proof.md, final Weil-structures paragraph
(blueprint: lem-sf-supported-weil-mate-lift).

The input and conclusion records spell out this conditional statement. In the final
statement their categories, Frobenius pullbacks and pullback squares are the published
rational and common-stage ones. Triangles always belong to the underlying categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v uX vX uZ vZ uU vU uX' vX' uZ' vZ' uU' vU'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

section Input
variable {X : Type uX} [Category.{vX} X] [Preadditive X] [HasZeroObject X]
  [HasShift X ℤ] [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]
  {Z : Type uZ} [Category.{vZ} Z] [Preadditive Z] [HasZeroObject Z]
  [HasShift Z ℤ] [∀ n : ℤ, (shiftFunctor Z n).Additive] [Pretriangulated Z]
  {U : Type uU} [Category.{vU} U] [Preadditive U] [HasZeroObject U]
  [HasShift U ℤ] [∀ n : ℤ, (shiftFunctor U n).Additive] [Pretriangulated U]
  (ip : X ⥤ Z) (jp : X ⥤ U) (P : X ⥤ X) (Q : Z ⥤ Z) (H : U ⥤ U)
  (d : ip ⋙ Q ≅ P ⋙ ip) (dj : jp ⋙ H ≅ P ⋙ jp)

/-- Exactly the specified supported adjunctions and triangles, including exactness
of their adjunction maps. The closed comparison is the prescribed mate of d inverse.
Source: localization proof, Weil-structures paragraph and returned step 20
(blueprint: lem-sf-supported-weil-mate-lift). -/
structure SfSupportedWeilInput where
  iPush : Z ⥤ X
  exceptional : X ⥤ Z
  jPush : U ⥤ X
  closedAdj : ip ⊣ iPush
  exceptionalAdj : iPush ⊣ exceptional
  openAdj : jp ⊣ jPush
  closedCounit : IsIso closedAdj.counit
  openCounit : IsIso openAdj.counit
  closed_open_zero (M : Z) : IsZero (jp.obj (iPush.obj M))
  pShift : P.CommShift ℤ
  qShift : Q.CommShift ℤ
  hShift : H.CommShift ℤ
  ipShift : ip.CommShift ℤ
  jpShift : jp.CommShift ℤ
  iShift : iPush.CommShift ℤ
  exceptionalShift : exceptional.CommShift ℤ
  jShift : jPush.CommShift ℤ
  pExact : letI := pShift; P.IsTriangulated
  qExact : letI := qShift; Q.IsTriangulated
  hExact : letI := hShift; H.IsTriangulated
  closedExact : letI := ipShift; letI := iShift; closedAdj.IsTriangulated
  exceptionalExact :
    letI := iShift; letI := exceptionalShift; exceptionalAdj.IsTriangulated
  openExact : letI := jpShift; letI := jShift; openAdj.IsTriangulated
  dShift : letI := ipShift; letI := pShift; letI := qShift;
    NatTrans.CommShift d.hom ℤ
  djShift : letI := jpShift; letI := pShift; letI := hShift;
    NatTrans.CommShift dj.hom ℤ
  a : iPush ⋙ P ≅ Q ⋙ iPush
  a_mate : a.hom = (mateEquiv closedAdj closedAdj (TwoSquare.mk _ _ _ _ d.inv)).natTrans
  r : jPush ⋙ P ≅ H ⋙ jPush
  rShift : letI := jShift; letI := pShift; letI := hShift;
    NatTrans.CommShift r.hom ℤ
  openUnit (K : X) : P.map (openAdj.unit.app K) ≫ r.hom.app (jp.obj K) ≫
    jPush.map (dj.hom.app K) = openAdj.unit.app (P.obj K)
  boundary (K : X) : jPush.obj (jp.obj K) ⟶ (iPush.obj (exceptional.obj K))⟦(1 : ℤ)⟧
  distinguished (K : X) :
    Triangle.mk (exceptionalAdj.counit.app K) (openAdj.unit.app K) (boundary K) ∈
      distTriang X
  unique_middle (K L : X) (f : K ⟶ L) :
    ∃! t : Triangle.mk (exceptionalAdj.counit.app K) (openAdj.unit.app K) (boundary K) ⟶
        Triangle.mk (exceptionalAdj.counit.app L) (openAdj.unit.app L) (boundary L),
      t.hom₂ = f

variable {ip jp P Q H d dj}

/-- The right mate itself, with its actual three factors fixed before invertibility.
Source: localization proof, mate formula in returned step 20
(blueprint: lem-sf-supported-weil-mate-lift). -/
def sfSupportedWeilMate (S : SfSupportedWeilInput ip jp P Q H d dj) :
    S.exceptional ⋙ Q ⟶ P ⋙ S.exceptional :=
  (mateEquiv S.exceptionalAdj S.exceptionalAdj (TwoSquare.mk _ _ _ _ S.a.inv)).natTrans

/-- The given underlying supported triangle; no triangle of fixed pairs is introduced.
Source: localization proof, returned step 20
(blueprint: lem-sf-supported-weil-mate-lift). -/
def sfSupportedWeilTriangle (S : SfSupportedWeilInput ip jp P Q H d dj) (K : X) :
    Triangle X :=
  Triangle.mk (S.exceptionalAdj.counit.app K) (S.openAdj.unit.app K) (S.boundary K)

/-- The required lift, including its uniqueness, mate normalization, Hom actions,
shift square, triangle comparison, recovery by i*, and functoriality on Weil arrows.
Source: localization proof, returned step 20
(blueprint: lem-sf-supported-weil-mate-lift). -/
def SfSupportedWeilConclusion (S : SfSupportedWeilInput ip jp P Q H d dj) : Prop :=
  letI := S.pShift
  letI := S.qShift
  letI := S.exceptionalShift
  (∃! b : S.exceptional ⋙ Q ≅ P ⋙ S.exceptional,
    ∀ K : X, S.iPush.map (b.hom.app K) ≫ S.exceptionalAdj.counit.app (P.obj K) =
      S.a.inv.app (S.exceptional.obj K) ≫ P.map (S.exceptionalAdj.counit.app K)) ∧
  ∃ b : S.exceptional ⋙ Q ≅ P ⋙ S.exceptional,
    b.hom = sfSupportedWeilMate S ∧
    (∀ K : X, b.hom.app K = S.exceptionalAdj.unit.app (Q.obj (S.exceptional.obj K)) ≫
      S.exceptional.map (S.a.inv.app (S.exceptional.obj K)) ≫
      S.exceptional.map (P.map (S.exceptionalAdj.counit.app K))) ∧
    NatTrans.CommShift b.hom ℤ ∧
    (∃ A : IsoAlgebra.mapOfNatIso S.a ⊣ IsoAlgebra.mapOfNatIso b,
      (∀ M : IsoAlgebra Q, (A.unit.app M).hom.f =
        S.exceptionalAdj.unit.app M.carrier) ∧
      (∀ K : IsoAlgebra P, (A.counit.app K).hom.f =
        S.exceptionalAdj.counit.app K.carrier)) ∧
    (∀ (M : IsoAlgebra Q) (K : IsoAlgebra P) (f : S.iPush.obj M.carrier ⟶ K.carrier),
      S.exceptionalAdj.homEquiv M.carrier K.carrier
        ((S.iPush.mapIso M.str).inv ≫ S.a.inv.app M.carrier ≫ P.map f ≫ K.str.hom) =
      M.str.inv ≫ Q.map (S.exceptionalAdj.homEquiv M.carrier K.carrier f) ≫
        b.hom.app K.carrier ≫ S.exceptional.map K.str.hom) ∧
    (∀ K : IsoAlgebra P,
      (∃! t : P.mapTriangle.obj (sfSupportedWeilTriangle S K.carrier) ≅
          sfSupportedWeilTriangle S K.carrier, t.hom.hom₂ = K.str.hom) ∧
      ∀ t : P.mapTriangle.obj (sfSupportedWeilTriangle S K.carrier) ≅
          sfSupportedWeilTriangle S K.carrier, t.hom.hom₂ = K.str.hom →
        t.hom.hom₁ = S.a.hom.app (S.exceptional.obj K.carrier) ≫
          S.iPush.map (b.hom.app K.carrier ≫ S.exceptional.map K.str.hom) ∧
        t.hom.hom₃ = S.r.hom.app (jp.obj K.carrier) ≫
          S.jPush.map (dj.hom.app K.carrier ≫ jp.map K.str.hom) ∧
        (∀ c : ip.obj (S.iPush.obj (S.exceptional.obj K.carrier)) ≅
            S.exceptional.obj K.carrier, c.hom = S.closedAdj.counit.app _ →
          Q.map c.inv ≫ d.hom.app (S.iPush.obj (S.exceptional.obj K.carrier)) ≫
            ip.map t.hom.hom₁ ≫ c.hom =
              b.hom.app K.carrier ≫ S.exceptional.map K.str.hom)) ∧
    (∀ (K L : IsoAlgebra P) (f : K ⟶ L),
      ((IsoAlgebra.mapOfNatIso b).map f).hom.f = S.exceptional.map f.hom.f ∧
      Q.map (S.exceptional.map f.hom.f) ≫
          (b.hom.app L.carrier ≫ S.exceptional.map L.str.hom) =
        (b.hom.app K.carrier ≫ S.exceptional.map K.str.hom) ≫
          S.exceptional.map f.hom.f) ∧
    (∀ (K L : IsoAlgebra P) (f : K ⟶ L)
      (tK : P.mapTriangle.obj (sfSupportedWeilTriangle S K.carrier) ≅
        sfSupportedWeilTriangle S K.carrier)
      (tL : P.mapTriangle.obj (sfSupportedWeilTriangle S L.carrier) ≅
        sfSupportedWeilTriangle S L.carrier),
      tK.hom.hom₂ = K.str.hom → tL.hom.hom₂ = L.str.hom →
      ∀ s : sfSupportedWeilTriangle S K.carrier ⟶ sfSupportedWeilTriangle S L.carrier,
        s.hom₂ = f.hom.f → P.mapTriangle.map s ≫ tL.hom = tK.hom ≫ s)

private theorem supported_mate_counit
    (S : SfSupportedWeilInput ip jp P Q H d dj) (K : X) :
    S.iPush.map ((sfSupportedWeilMate S).app K) ≫
      S.exceptionalAdj.counit.app (P.obj K) =
        S.a.inv.app (S.exceptional.obj K) ≫ P.map (S.exceptionalAdj.counit.app K) :=
  mateEquiv_counit S.exceptionalAdj S.exceptionalAdj
    (TwoSquare.mk _ _ _ _ S.a.inv) K

private theorem supported_first_square
    (S : SfSupportedWeilInput ip jp P Q H d dj)
    {K L : X} (f : P.obj K ⟶ L) :
    P.map (S.exceptionalAdj.counit.app K) ≫ f =
      S.a.hom.app (S.exceptional.obj K) ≫
        S.iPush.map ((sfSupportedWeilMate S).app K ≫ S.exceptional.map f) ≫
          S.exceptionalAdj.counit.app L := by
  simp only [S.iPush.map_comp, Category.assoc]
  have hn := S.exceptionalAdj.counit_naturality f
  rw [hn, reassoc_of% supported_mate_counit S K, Iso.hom_inv_id_app_assoc]

private theorem supported_open_square
    (S : SfSupportedWeilInput ip jp P Q H d dj)
    {K L : X} (f : P.obj K ⟶ L) :
    P.map (S.openAdj.unit.app K) ≫ S.r.hom.app (jp.obj K) ≫
      S.jPush.map (dj.hom.app K ≫ jp.map f) = f ≫ S.openAdj.unit.app L := by
  simp only [S.jPush.map_comp]
  rw [reassoc_of% S.openUnit K]
  exact S.openAdj.unit_naturality f

private theorem supported_open_ext
    (S : SfSupportedWeilInput ip jp P Q H d dj)
    (K : X) (V : U) (f g : P.obj (S.jPush.obj (jp.obj K)) ⟶ S.jPush.obj V)
    (h : P.map (S.openAdj.unit.app K) ≫ f = P.map (S.openAdj.unit.app K) ≫ g) :
    f = g := by
  let := S.openCounit
  have hi : IsIso (jp.map (S.openAdj.unit.app K)) := by
    have he : jp.map (S.openAdj.unit.app K) = inv (S.openAdj.counit.app (jp.obj K)) := by
      apply (cancel_mono (S.openAdj.counit.app (jp.obj K))).1
      simp only [IsIso.inv_hom_id]
      exact S.openAdj.left_triangle_components K
    rw [he]
    infer_instance
  have he : jp.map (P.map (S.openAdj.unit.app K)) =
      dj.inv.app K ≫ H.map (jp.map (S.openAdj.unit.app K)) ≫
        dj.hom.app (S.jPush.obj (jp.obj K)) := by
    have hn := dj.hom.naturality (S.openAdj.unit.app K)
    dsimp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hn
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using
      congrArg (fun f ↦ dj.inv.app K ≫ f) hn.symm
  have : IsIso (jp.map (P.map (S.openAdj.unit.app K))) := by
    rw [he]
    infer_instance
  apply (S.openAdj.homEquiv _ _).symm.injective
  apply (cancel_epi (jp.map (P.map (S.openAdj.unit.app K)))).1
  simpa only [S.openAdj.homEquiv_naturality_left_symm, Functor.id_obj,
    Functor.comp_obj] using
    congrArg (S.openAdj.homEquiv (P.obj K) V).symm h

private theorem supported_hom_action
    (S : SfSupportedWeilInput ip jp P Q H d dj)
    (M : IsoAlgebra Q) (K : IsoAlgebra P) (f : S.iPush.obj M.carrier ⟶ K.carrier) :
    S.exceptionalAdj.homEquiv M.carrier K.carrier
      ((S.iPush.mapIso M.str).inv ≫ S.a.inv.app M.carrier ≫ P.map f ≫ K.str.hom) =
    M.str.inv ≫ Q.map (S.exceptionalAdj.homEquiv M.carrier K.carrier f) ≫
      (sfSupportedWeilMate S).app K.carrier ≫ S.exceptional.map K.str.hom := by
  apply (S.exceptionalAdj.homEquiv _ _).symm.injective
  simp only [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply,
    Functor.map_comp, Category.assoc]
  rw [S.exceptionalAdj.counit_naturality,
    reassoc_of% supported_mate_counit S K.carrier]
  have hn := S.a.inv.naturality (S.exceptionalAdj.homEquiv M.carrier K.carrier f)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← P.map_comp_assoc]
  have hf : S.iPush.map (S.exceptionalAdj.homEquiv M.carrier K.carrier f) ≫
      S.exceptionalAdj.counit.app K.carrier = f :=
    (S.exceptionalAdj.homEquiv _ _).symm_apply_apply f
  rw [hf]
  rfl

private theorem supported_triangle_ext
    (S : SfSupportedWeilInput ip jp P Q H d dj) [P.CommShift ℤ] (K L : X)
    (e : P.mapTriangle.obj (sfSupportedWeilTriangle S K) ≅ sfSupportedWeilTriangle S K)
    (f g : P.mapTriangle.obj (sfSupportedWeilTriangle S K) ⟶ sfSupportedWeilTriangle S L)
    (h : f.hom₂ = g.hom₂) : f = g := by
  have hh : e.inv ≫ f = e.inv ≫ g :=
    (S.unique_middle K L (e.inv.hom₂ ≫ f.hom₂)).unique
      (show (e.inv ≫ f).hom₂ = _ from rfl)
      (show (e.inv ≫ g).hom₂ = _ by change _ ≫ _ = _ ≫ _; rw [h])
  exact (cancel_epi e.inv).1 hh

private theorem supported_conclusion
    (S : SfSupportedWeilInput ip jp P Q H d dj) [P.IsEquivalence] [Q.IsEquivalence] :
    SfSupportedWeilConclusion S := by
  let := S.pShift
  let := S.qShift
  let := S.hShift
  let := S.ipShift
  let := S.jpShift
  let := S.iShift
  let := S.exceptionalShift
  let := S.jShift
  let := S.closedExact
  let := S.exceptionalExact
  let := S.openExact
  let := S.pExact
  let := S.dShift
  let := S.djShift
  let := S.rShift
  let := S.closedCounit
  let := S.openCounit
  have ha : NatTrans.CommShift S.a.hom ℤ := by
    rw [S.a_mate]
    exact NatTrans.CommShift.mateEquiv _ _ _
  let := ha
  let b : S.exceptional ⋙ Q ≅ P ⋙ S.exceptional :=
    IsoAlgebra.mateIso S.exceptionalAdj S.a
  have hb : b.hom = sfSupportedWeilMate S := rfl
  have hbn (K : X) : S.iPush.map (b.hom.app K) ≫
      S.exceptionalAdj.counit.app (P.obj K) =
        S.a.inv.app (S.exceptional.obj K) ≫ P.map (S.exceptionalAdj.counit.app K) :=
    supported_mate_counit S K
  have hbu (c : S.exceptional ⋙ Q ≅ P ⋙ S.exceptional)
      (hc : ∀ K : X, S.iPush.map (c.hom.app K) ≫
        S.exceptionalAdj.counit.app (P.obj K) =
          S.a.inv.app (S.exceptional.obj K) ≫ P.map (S.exceptionalAdj.counit.app K)) : c = b := by
    apply Iso.ext
    ext K
    apply (S.exceptionalAdj.homEquiv _ _).symm.injective
    exact (hc K).trans (hbn K).symm
  change (∃! c, _) ∧ _
  refine ⟨⟨b, hbn, hbu⟩, b, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K
    simp [b, IsoAlgebra.mateIso, mateEquiv]
  · exact NatTrans.CommShift.mateEquiv _ _ _
  · exact ⟨IsoAlgebra.mapOfNatIsoAdjunction S.exceptionalAdj S.a b rfl,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  · exact supported_hom_action S
  · intro K
    let θ := b.hom.app K.carrier ≫ S.exceptional.map K.str.hom
    let e₁ : P.obj (S.iPush.obj (S.exceptional.obj K.carrier)) ≅
        S.iPush.obj (S.exceptional.obj K.carrier) :=
      S.a.app _ ≪≫ S.iPush.mapIso (b.app _ ≪≫ S.exceptional.mapIso K.str)
    have hw : P.map (S.exceptionalAdj.counit.app K.carrier) ≫ K.str.hom =
        e₁.hom ≫ S.exceptionalAdj.counit.app K.carrier := by
      change P.map (S.exceptionalAdj.counit.app K.carrier) ≫ K.str.hom =
        (S.a.hom.app _ ≫ S.iPush.map (b.hom.app _ ≫ S.exceptional.map K.str.hom)) ≫ _
      simpa only [Category.assoc, hb] using supported_first_square S K.str.hom
    let t₀ := isoTriangleOfIso₁₂ _ _
      (P.map_distinguished _ (S.distinguished K.carrier)) (S.distinguished K.carrier)
      e₁ K.str hw
    have ht₂ : t₀.hom.hom₂ = K.str.hom := by simp [t₀]
    refine ⟨⟨t₀, ht₂, ?_⟩, ?_⟩
    · intro t ht
      apply Iso.ext
      exact supported_triangle_ext S _ _ t₀ _ _ (ht.trans ht₂.symm)
    · intro t ht
      have ht₀ : t = t₀ := by
        apply Iso.ext
        exact supported_triangle_ext S _ _ t₀ _ _ (ht.trans ht₂.symm)
      have ht₁ : t.hom.hom₁ = S.a.hom.app (S.exceptional.obj K.carrier) ≫
          S.iPush.map θ := by simp [ht₀, t₀, e₁, θ]
      refine ⟨ht₁, ?_, ?_⟩
      · apply supported_open_ext S K.carrier (jp.obj K.carrier) t.hom.hom₃ _
        have ht' : P.map (S.openAdj.unit.app K.carrier) ≫ t.hom.hom₃ =
            K.str.hom ≫ S.openAdj.unit.app K.carrier := by
          have hh := t.hom.comm₂
          change P.map (S.openAdj.unit.app K.carrier) ≫ t.hom.hom₃ =
            t.hom.hom₂ ≫ S.openAdj.unit.app K.carrier at hh
          simpa only [ht] using hh
        exact ht'.trans (supported_open_square S K.str.hom).symm
      · intro c hc
        let M := (IsoAlgebra.mapOfNatIso b).obj K
        have he := IsoAlgebra.map_counit_app_comp_str S.closedAdj d S.a S.a_mate.symm M
        have he' : Q.map c.hom ≫ θ =
            d.hom.app (S.iPush.obj (S.exceptional.obj K.carrier)) ≫
              ip.map (S.a.hom.app (S.exceptional.obj K.carrier) ≫ S.iPush.map θ) ≫
                c.hom := by
          change Q.map (S.closedAdj.counit.app _) ≫ θ =
            (d.hom.app _ ≫ ip.map (S.a.hom.app _ ≫ S.iPush.map θ)) ≫
              S.closedAdj.counit.app _ at he
          simpa only [Category.assoc, hc] using he
        change Q.map c.inv ≫ d.hom.app _ ≫ ip.map t.hom.hom₁ ≫ c.hom = θ
        rw [ht₁, ← he']
        simp only [← Q.map_comp_assoc, c.inv_hom_id, Q.map_id, Category.id_comp]
  · intro K L f
    refine ⟨rfl, ?_⟩
    exact ((IsoAlgebra.mapOfNatIso b).map f).hom.h
  · intro K L f tK tL htK htL s hs
    apply supported_triangle_ext S _ _ tK
    change P.map s.hom₂ ≫ tL.hom.hom₂ = tK.hom.hom₂ ≫ s.hom₂
    rw [htL, htK, hs]
    exact f.hom.h

end Input


section Coefficients
variable {X : Type uX} [Category.{vX} X] [Preadditive X] [HasZeroObject X]
  [HasShift X ℤ] [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]
  {Z : Type uZ} [Category.{vZ} Z] [Preadditive Z] [HasZeroObject Z]
  [HasShift Z ℤ] [∀ n : ℤ, (shiftFunctor Z n).Additive] [Pretriangulated Z]
  {U : Type uU} [Category.{vU} U] [Preadditive U] [HasZeroObject U]
  [HasShift U ℤ] [∀ n : ℤ, (shiftFunctor U n).Additive] [Pretriangulated U]
  {X' : Type uX'} [Category.{vX'} X'] [Preadditive X'] [HasZeroObject X']
  [HasShift X' ℤ] [∀ n : ℤ, (shiftFunctor X' n).Additive] [Pretriangulated X']
  {Z' : Type uZ'} [Category.{vZ'} Z'] [Preadditive Z'] [HasZeroObject Z']
  [HasShift Z' ℤ] [∀ n : ℤ, (shiftFunctor Z' n).Additive] [Pretriangulated Z']
  {U' : Type uU'} [Category.{vU'} U'] [Preadditive U'] [HasZeroObject U']
  [HasShift U' ℤ] [∀ n : ℤ, (shiftFunctor U' n).Additive] [Pretriangulated U']
  {ip : X ⥤ Z} {jp : X ⥤ U} {P : X ⥤ X} {Q : Z ⥤ Z} {H : U ⥤ U}
  {d : ip ⋙ Q ≅ P ⋙ ip} {dj : jp ⋙ H ≅ P ⋙ jp}
  {ip' : X' ⥤ Z'} {jp' : X' ⥤ U'} {P' : X' ⥤ X'} {Q' : Z' ⥤ Z'} {H' : U' ⥤ U'}
  {d' : ip' ⋙ Q' ≅ P' ⋙ ip'} {dj' : jp' ⋙ H' ≅ P' ⋙ jp'}

/-- The coefficient square for the normalized mate. This applies to every given
coefficient comparison, including rational scalar changes, finite-stage inclusions,
identities and composites. Thus any given tower coherence is retained, rather than
choosing a new exceptional comparison separately at each stage.
Source: localization proof, returned step 20, coefficient paragraph
(blueprint: lem-sf-supported-weil-mate-lift).

Proof: expand the three factors of sfSupportedWeilMate. Preservation of the
exceptional counit identifies the adjunction transpose after coefficient change.
The Frobenius square for the closed image identifies its other side. The two
resulting arrows have equal transposes under the target exceptional adjunction,
hence agree. This is clause 1 of lem-weil-pbc-mate-pasting. The same calculation
for identities and successive comparisons, using its identity clause, gives the
identity and tower equations. All comparisons in a given tower are fixed inputs. -/
theorem sf_supportedWeilMate_coefficient
    (S : SfSupportedWeilInput ip jp P Q H d dj)
    (S' : SfSupportedWeilInput ip' jp' P' Q' H' d' dj')
    (TX : X ⥤ X') (TZ : Z ⥤ Z')
    (sI : S.iPush ⋙ TX ≅ TZ ⋙ S'.iPush)
    (sJ : S.exceptional ⋙ TZ ≅ TX ⋙ S'.exceptional)
    (sP : P ⋙ TX ≅ TX ⋙ P') (sQ : Q ⋙ TZ ≅ TZ ⋙ Q')
    (_counit : ∀ K : X, sI.hom.app (S.exceptional.obj K) ≫
      S'.iPush.map (sJ.hom.app K) ≫ S'.exceptionalAdj.counit.app (TX.obj K) =
        TX.map (S.exceptionalAdj.counit.app K))
    (_closed : ∀ M : Z, TX.map (S.a.hom.app M) ≫ sI.hom.app (Q.obj M) ≫
      S'.iPush.map (sQ.hom.app M) = sP.hom.app (S.iPush.obj M) ≫
        P'.map (sI.hom.app M) ≫ S'.a.hom.app (TZ.obj M)) :
    ∀ K : X, TZ.map ((sfSupportedWeilMate S).app K) ≫ sJ.hom.app (P.obj K) ≫
      S'.exceptional.map (sP.hom.app K) = sQ.hom.app (S.exceptional.obj K) ≫
        Q'.map (sJ.hom.app K) ≫ (sfSupportedWeilMate S').app (TX.obj K) := by
  intro K
  have hb (V : X) : S.iPush.map ((sfSupportedWeilMate S).app V) ≫
      S.exceptionalAdj.counit.app (P.obj V) =
        S.a.inv.app (S.exceptional.obj V) ≫ P.map (S.exceptionalAdj.counit.app V) :=
    mateEquiv_counit S.exceptionalAdj S.exceptionalAdj
      (TwoSquare.mk _ _ _ _ S.a.inv) V
  have hb' (V : X') : S'.iPush.map ((sfSupportedWeilMate S').app V) ≫
      S'.exceptionalAdj.counit.app (P'.obj V) =
        S'.a.inv.app (S'.exceptional.obj V) ≫ P'.map (S'.exceptionalAdj.counit.app V) :=
    mateEquiv_counit S'.exceptionalAdj S'.exceptionalAdj
      (TwoSquare.mk _ _ _ _ S'.a.inv) V
  have hc (M : Z) : sI.hom.app (Q.obj M) ≫ S'.iPush.map (sQ.hom.app M) ≫
      S'.a.inv.app (TZ.obj M) = TX.map (S.a.inv.app M) ≫
        sP.hom.app (S.iPush.obj M) ≫ P'.map (sI.hom.app M) := by
    apply (cancel_epi (TX.map (S.a.hom.app M))).1
    simpa only [Category.assoc, ← TX.map_comp_assoc, Iso.hom_inv_id_app,
      TX.map_id, Category.id_comp, Category.comp_id, Iso.hom_inv_id_app_assoc,
      Functor.comp_obj] using
      congrArg (fun f ↦ f ≫ S'.a.inv.app (TZ.obj M)) (_closed M)
  apply (S'.exceptionalAdj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  apply (cancel_epi (sI.hom.app (Q.obj (S.exceptional.obj K)))).1
  calc
    _ = TX.map (S.iPush.map ((sfSupportedWeilMate S).app K)) ≫
        TX.map (S.exceptionalAdj.counit.app (P.obj K)) ≫ sP.hom.app K := by
      rw [S'.exceptionalAdj.counit_naturality]
      have hn := sI.hom.naturality ((sfSupportedWeilMate S).app K)
      dsimp only [Functor.comp_map] at hn
      rw [← reassoc_of% hn]
      rw [reassoc_of% _counit (P.obj K)]
    _ = TX.map (S.a.inv.app (S.exceptional.obj K)) ≫
        sP.hom.app (S.iPush.obj (S.exceptional.obj K)) ≫
          P'.map (TX.map (S.exceptionalAdj.counit.app K)) := by
      rw [← TX.map_comp_assoc, hb, TX.map_comp, Category.assoc]
      rw [dsimp% sP.hom.naturality (S.exceptionalAdj.counit.app K)]
    _ = _ := by
      rw [← _counit K, P'.map_comp, P'.map_comp]
      rw [← reassoc_of% hc (S.exceptional.obj K)]
      have hn := S'.a.inv.naturality (sJ.hom.app K)
      dsimp only [Functor.comp_map] at hn
      rw [← reassoc_of% hn]
      rw [← hb' (TX.obj K)]
      rfl

end Coefficients

/-- The unique normalized supported right-adjoint comparison, on both literal
coefficient categories of the node. All supported functors and adjunctions are
specified inputs; the two pullbacks and both pullback-composition comparisons are
fixed to their canonical published definitions.
Source: main-20261015, localization proof, final Weil-structures paragraph;
returned step 20 (blueprint: lem-sf-supported-weil-mate-lift).

Proof plan:
1. Use lem-sf-automorphism-constructible-stage-equivalence for the semilinear
   geometric Frobenius pullbacks P,Q,H, including their coherent inverse and shifts.
   The closed comparison a is the mate of d inverse by the input normalization,
   as in lem-sf-open-closed-weil-mate-structures.
2. Apply def-weil-pbc-adjunction-mate to a inverse for iPush ⊣ exceptional. The
   displayed three-factor word is sfSupportedWeilMate. It is invertible by
   lem-weil-mate-iso-along-equivalences. The transpose equation is the stated
   counit normalization; injectivity of the Hom bijection gives uniqueness.
3. lem-sf-fixed-pair-adjunction-lift constructs the lifted adjunction, with the
   same underlying unit and counit. Apply it also to ip ⊣ iPush, using a_mate.
4. The exceptional counit and given open unit give the first two Weil squares.
   TR3 completes the first square. The third component is the prescribed open
   structure: by jp ⊣ jPush, precomposition with P(openUnit) is injective, since
   jp(openUnit) is inverse to the invertible open counit. All components are
   invertible. Uniqueness with fixed middle component gives the unique triangle iso.
5. Apply ip to its first component and conjugate by the invertible closed
   counit. Equivariance of that counit identifies the result with the mate lift.
   Naturality of the mate gives the stated action on Weil morphisms.
6. Expand the inverse adjunction bijection e composed with iPush(v). Naturality
   of e and a and the normalized counit equation identify its Frobenius transform
   with that of v. Bijectivity then gives the displayed forward Hom-action equation.
7. Exactness of the adjunctions makes the shift comparisons mates. Apply clause 1
   of lem-weil-pbc-mate-pasting first to d inverse and then to a inverse; equality
   of the two pasted squares gives NatTrans.CommShift for b. The coefficient
   clause sf_supportedWeilMate_coefficient repeats this calculation for the given
   coefficient comparisons, with the identity and tower equations inherited from
   those inputs. No triangulated structure on fixed pairs is asserted. -/
theorem sf_supportedWeilMateLift
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X₀ Z₀ U₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    (i₀ : Z₀ ⟶ X₀) (j₀ : U₀ ⟶ X₀)
    [IsClosedImmersion i₀.left] [IsOpenImmersion j₀.left]
    (_complement : Set.range j₀.left = (Set.range i₀.left)ᶜ) :
    (∀ S : SfSupportedWeilInput
        (fieldWeilPull D l hl E i₀) (fieldWeilPull D l hl E j₀)
        (sfWeilFrobeniusPullback D l hl X₀ E)
        (sfWeilFrobeniusPullback D l hl Z₀ E)
        (sfWeilFrobeniusPullback D l hl U₀ E)
        (fieldWeilPullSquare D l hl E i₀) (fieldWeilPullSquare D l hl E j₀),
      SfSupportedWeilConclusion S) ∧
    (∀ S : SfSupportedWeilInput
        (zlPull D l hl Ω i₀) (zlPull D l hl Ω j₀)
        (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
        (sfCommonStageWeilFrobeniusPullback D l hl Z₀ Ω)
        (sfCommonStageWeilFrobeniusPullback D l hl U₀ Ω)
        (zlFrobeniusSquare D l hl Ω i₀) (zlFrobeniusSquare D l hl Ω j₀),
      SfSupportedWeilConclusion S) := by
  let : Fact (l ≠ D.p) := ⟨hl⟩
  let := sfWeilPrimeInvertible D l hl X₀
  let := sfWeilPrimeInvertible D l hl Z₀
  let : IsSeparated Z₀.hom := by
    rw [← i₀.w]
    infer_instance
  let : IsSeparated (D.geometricFiber X₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : IsSeparated (D.geometricFiber Z₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Z₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : LocallyOfFiniteType (D.geometricFiber X₀).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : LocallyOfFiniteType (D.geometricFiber Z₀).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Z₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact (D.geometricFiber X₀).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact (D.geometricFiber Z₀).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd Z₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have hX := automorphismConstructibleStage_integral_rational D l E
    (D.geometricFiber X₀) (D.geometricFrobenius X₀)
  have hZ := automorphismConstructibleStage_integral_rational D l E
    (D.geometricFiber Z₀) (D.geometricFrobenius Z₀)
  have hX' := automorphismConstructibleStage_qbar D l Ω
    (D.geometricFiber X₀) (D.geometricFrobenius X₀)
  have hZ' := automorphismConstructibleStage_qbar D l Ω
    (D.geometricFiber Z₀) (D.geometricFrobenius Z₀)
  let : (sfWeilFrobeniusPullback D l hl X₀ E).IsEquivalence := hX.2.2.2.2.2.1
  let : (sfWeilFrobeniusPullback D l hl Z₀ E).IsEquivalence := hZ.2.2.2.2.2.1
  let : (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).IsEquivalence := hX'.1
  let : (sfCommonStageWeilFrobeniusPullback D l hl Z₀ Ω).IsEquivalence := hZ'.1
  exact ⟨fun S ↦ supported_conclusion S, fun S ↦ supported_conclusion S⟩

end WeilConjectures
