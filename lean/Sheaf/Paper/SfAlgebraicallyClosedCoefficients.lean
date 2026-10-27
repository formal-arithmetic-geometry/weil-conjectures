/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.Paper.AlgebraicallyClosedCoefficients
public import Sheaf.Paper.ScalarExtensionExactIntrinsic
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.CategoryTheory.StageSystemVerdier
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Colimit.Module

import Sheaf.Paper.SfRationalScalarExactOfIntegral
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import WeilConjectures.CategoryTheory.IntegerShiftFromOne

/-! # Intrinsic algebraically closed coefficients without idempotent completion

Source: blueprint `sec-smooth-purity/sk-def-sf-operations`, order 1462;
current main snapshot `sec-proetale-coefficients/sk-def-sf-operations`, order 1821
(blueprint: def-weil-algebraically-closed-coefficients).
Objects are actual pairs and Hom is the directed colimit of the stated abelian groups.
Finite stages use the repaired intrinsic integral constructibility predicate.

The similarly named legacy theorems quantify over `AlgebraicallyClosedCoefficients.Stage`,
which uses `rationalConstructibleCategory` and the withdrawn integral predicate.
Here the eleven formerly ambiguous signatures bind every source parameter explicitly
and qualify their intrinsic stage, pair, transition and Hom data. They concern
`sfRationalConstructibleCategory` on `sfIntegralConstructibleCategory`; no identification
with the legacy stages is assumed. Existing generic pair/cone/Verdier constructions
and the shared coefficient transport are reused.
The legacy coefficient-size transports are reused without identifying the old and new stages.
The existing upstream pair category supplies its quotient, identities and composition;
its Hom groups are canonically the displayed abelian-group colimits.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe d u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace WeilConjectures
namespace SfAlgebraicallyClosedCoefficients

section
attribute [local irreducible] sfRationalTriangulationDatum sfRationalScalarExtension

open TensorProduct

private theorem normalized_compatibility
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (I : D ⥤ E) (H : C ⥤ E)
    [F.CommShift ℤ] [I.CommShift ℤ] [H.CommShift ℤ] (e : F ⋙ I ≅ H)
    (hc : ∀ (n : ℤ) (X : C), HEq (I.map ((F.commShiftIso n).hom.app X) ≫
        (I.commShiftIso n).hom.app (F.obj X))
      (e.hom.app ((shiftFunctor C n).obj X) ≫ (H.commShiftIso n).hom.app X ≫
        (shiftFunctor E n).map (e.inv.app X))) :
    NatTrans.CommShift e.hom ℤ := by
  apply NatTrans.CommShift.of_core
  intro n
  constructor
  ext X
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [Functor.commShiftIso_comp_hom_app, eq_of_heq (hc n X)]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id]
  simp only [Functor.comp_obj, CategoryTheory.Category.comp_id]

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases h
  rfl

private theorem localizedIso
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    {C : Type*} [Category C] [Preadditive C] [Linear R C]
    {D : Type*} [Category D] [Preadditive D] [Linear S D]
    (t : R) (v : S) (ψ : Localization.Away t → Localization.Away v)
    (F₀ G₀ : C ⥤ D) (e : F₀ ≅ G₀)
    (F G : ScalarLocalization R C t ⥤ ScalarLocalization S D v)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨F₀.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨G₀.obj K.obj⟩)
    (mF : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] F₀.map f : ScalarLocalization.mk (R := S) (p := v) (F₀.obj K) ⟶
          ⟨F₀.obj K'⟩))
    (mG : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (G.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] G₀.map f : ScalarLocalization.mk (R := S) (p := v) (G₀.obj K) ⟶
          ⟨G₀.obj K'⟩)) :
    ∃! a : F ≅ G, ∀ K, HEq (a.hom.app K)
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
  let c (K : ScalarLocalization R C t) : F.obj K ≅ G.obj K :=
    eqToIso (hF K) ≪≫ (ScalarLocalization.localization S D v).mapIso (e.app K.obj) ≪≫
      (eqToIso (hG K)).symm
  have c_hom (K) : (c K).hom =
      eqToHom (hF K) ≫ (ScalarLocalization.localization S D v).map (e.hom.app K.obj) ≫
        eqToHom (hG K).symm := rfl
  have hc (K) : HEq (c K).hom
      ((ScalarLocalization.localization S D v).map (e.hom.app K.obj)) := by
    rw [c_hom]
    exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)
  have hn {K K' : ScalarLocalization R C t} (f : K ⟶ K') :
      F.map f ≫ (c K').hom = (c K).hom ≫ G.map f := by
    obtain ⟨K⟩ := K
    obtain ⟨K'⟩ := K'
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f g hf hg =>
      rw [F.map_add, G.map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
    | tmul a f =>
      have he : ScalarLocalization.composition S D v _ _ _
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') (ψ a ⊗ₜ[S] F₀.map f) =
          ScalarLocalization.composition S D v _ _ _
            (ψ a ⊗ₜ[S] G₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) := by
        simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
        rw [e.hom.naturality f]
      have he' :
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨F₀.obj K'⟩ ⟨G₀.obj K'⟩
            (ψ a ⊗ₜ[S] F₀.map f) ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K') =
          @CategoryStruct.comp (ScalarLocalization S D v) _
            ⟨F₀.obj K⟩ ⟨G₀.obj K⟩ ⟨G₀.obj K'⟩
            ((1 : Localization.Away v) ⊗ₜ[S] e.hom.app K) (ψ a ⊗ₜ[S] G₀.map f) := he
      apply eq_of_heq
      exact (heq_comp (hF ⟨K⟩) (hF ⟨K'⟩) (hG ⟨K'⟩)
        (mF K K' f a) (hc ⟨K'⟩)).trans
          ((heq_of_eq he').trans
            (heq_comp (hF ⟨K⟩) (hG ⟨K⟩) (hG ⟨K'⟩)
              (hc ⟨K⟩) (mG K K' f a)).symm)
  let a : F ≅ G := NatIso.ofComponents c (fun f ↦ hn f)
  refine ⟨a, hc, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((ha' K).trans (hc K).symm)

private theorem commShiftCore_neg
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) (n : ℤ) (h : NatTrans.CommShiftCore τ n) :
    NatTrans.CommShiftCore τ (-n) := by
  constructor
  ext X
  apply (shiftFunctor D n).map_injective
  have hz : NatTrans.CommShiftCore τ (-n + n) := by
    simpa only [neg_add_cancel] using NatTrans.CommShiftCore.zero (τ := τ) ℤ
  have hs := hz.shift_app_comm τ X
  simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
    Category.assoc] at hs
  rw [← NatTrans.naturality_assoc] at hs
  have hD := (shiftFunctorAdd D (-n) n).inv.naturality (τ.app X)
  dsimp only [Functor.comp_map] at hD
  rw [← hD] at hs
  apply (cancel_epi (F.map ((shiftFunctorAdd C (-n) n).hom.app X) ≫
    (F.commShiftIso n).hom.app (X⟦-n⟧))).mp
  apply (cancel_mono ((shiftFunctorAdd D (-n) n).inv.app (G.obj X))).mp
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Functor.comp_obj, Category.assoc, h.shift_app_comm_assoc τ] using hs

/-- Coherence extends the degree-one square to every integral shift. -/
private theorem commShift_of_one
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) (h : NatTrans.CommShiftCore τ (1 : ℤ)) :
    NatTrans.CommShift τ ℤ := by
  apply NatTrans.CommShift.of_core
  have hn := commShiftCore_neg τ 1 h
  intro n
  induction n using Int.induction_on with
  | zero => exact NatTrans.CommShiftCore.zero (τ := τ) ℤ
  | @succ n ih => exact ih.add h
  | @pred n ih => simpa only [sub_eq_add_neg] using ih.add hn

private theorem integer_commShift_ext
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ] {F : C ⥤ D}
    (s t : F.CommShift ℤ)
    (h : ∀ n : ℤ, Functor.commShiftIso F (self := s) n =
      Functor.commShiftIso F (self := t) n) : s = t := by
  cases s
  cases t
  congr
  funext n
  exact h n

private theorem commShift_one_ext
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) (s t : F.CommShift ℤ)
    (h : Functor.commShiftIso F (self := s) (1 : ℤ) =
      Functor.commShiftIso F (self := t) (1 : ℤ)) : s = t := by
  have hcore : @NatTrans.CommShiftCore C D _ _ F F (𝟙 F) ℤ _ _ _ s t 1 := by
    refine @NatTrans.CommShiftCore.mk C D _ _ F F (𝟙 F) ℤ _ _ _ s t 1 ?_
    apply NatTrans.ext
    funext X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.id_app, Functor.comp_obj]
    rw [(shiftFunctor D (1 : ℤ)).map_id, Category.comp_id, Category.id_comp]
    exact congrArg (fun a ↦ a.hom.app X) h
  have hc := @commShift_of_one C D _ _ _ _ F F s t (𝟙 F) hcore
  apply integer_commShift_ext
  intro n
  apply Iso.ext
  apply NatTrans.ext
  funext X
  have hn := congrArg (fun a ↦ a.app X) (hc.shift_comm n)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.id_app, Functor.comp_obj] at hn
  rw [(shiftFunctor D n).map_id, Category.comp_id, Category.id_comp] at hn
  exact hn


private theorem scalarShift_exists
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    {C : Type*} [Category C] [Preadditive C] [Linear R C] [HasShift C ℤ]
    {D : Type*} [Category D] [Preadditive D] [Linear S D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [(shiftFunctor C (1 : ℤ)).Linear R]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [(shiftFunctor D (1 : ℤ)).Linear S]
    (t : R) (v : S) (ψ : Localization.Away t → Localization.Away v)
    [HasShift (ScalarLocalization R C t) ℤ] [HasShift (ScalarLocalization S D v) ℤ]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization R C t) n).Additive]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization S D v) n).Additive]
    (hC : shiftFunctor (ScalarLocalization R C t) (1 : ℤ) =
      ScalarLocalization.map R C t (shiftFunctor C (1 : ℤ)))
    (hD : shiftFunctor (ScalarLocalization S D v) (1 : ℤ) =
      ScalarLocalization.map S D v (shiftFunctor D (1 : ℤ)))
    (T : C ⥤ D) [T.CommShift ℤ]
    (F : ScalarLocalization R C t ⥤ ScalarLocalization S D v) [F.Additive]
    (hF : ∀ K, F.obj K = ⟨T.obj K.obj⟩)
    (mF : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] T.map f : ScalarLocalization.mk (R := S) (p := v) (T.obj K) ⟶
          ⟨T.obj K'⟩)) :
    ∃ s : F.CommShift ℤ, ∀ K,
      HEq ((Functor.commShiftIso F (self := s) (1 : ℤ)).hom.app K)
        ((ScalarLocalization.localization S D v).map ((T.commShiftIso (1 : ℤ)).hom.app K.obj)) := by
  let A := shiftFunctor (ScalarLocalization R C t) (1 : ℤ) ⋙ F
  let B := F ⋙ shiftFunctor (ScalarLocalization S D v) (1 : ℤ)
  have hA (K) : A.obj K = ⟨T.obj ((shiftFunctor C (1 : ℤ)).obj K.obj)⟩ := by
    dsimp only [A, Functor.comp_obj]
    rw [hC]
    exact hF _
  have hB (K) : B.obj K = ⟨(shiftFunctor D (1 : ℤ)).obj (T.obj K.obj)⟩ := by
    dsimp only [B, Functor.comp_obj]
    rw [hD, hF]
    rfl
  have mA (K K' : C) (f : K ⟶ K') (a : Localization.Away t) :
      HEq (A.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] T.map ((shiftFunctor C (1 : ℤ)).map f) :
          ScalarLocalization.mk (R := S) (p := v)
            (T.obj ((shiftFunctor C (1 : ℤ)).obj K)) ⟶
              ⟨T.obj ((shiftFunctor C (1 : ℤ)).obj K')⟩) := by
    dsimp only [A, Functor.comp_map]
    rw [hC]
    simpa only [ScalarLocalization.map, ScalarLocalization.mapHom,
      LinearMap.baseChange_tmul, Functor.comp_obj,
      Functor.coe_mapLinearMap] using mF _ _ ((shiftFunctor C (1 : ℤ)).map f) a
  have mB (K K' : C) (f : K ⟶ K') (a : Localization.Away t) :
      HEq (B.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] (shiftFunctor D (1 : ℤ)).map (T.map f) :
          ScalarLocalization.mk (R := S) (p := v)
            ((shiftFunctor D (1 : ℤ)).obj (T.obj K)) ⟶
              ⟨(shiftFunctor D (1 : ℤ)).obj (T.obj K')⟩) := by
    have hm := map_heq (shiftFunctor (ScalarLocalization S D v) (1 : ℤ))
      (hF ⟨K⟩) (hF ⟨K'⟩) (mF K K' f a)
    rw [hD] at hm
    dsimp only [B, Functor.comp_map]
    rw [hD]
    simpa only [B, Functor.comp_map, ScalarLocalization.map, ScalarLocalization.mapHom,
      LinearMap.baseChange_tmul, Functor.comp_obj,
      Functor.coe_mapLinearMap] using hm
  obtain ⟨a, ha, _⟩ := localizedIso t v ψ
    (shiftFunctor C (1 : ℤ) ⋙ T) (T ⋙ shiftFunctor D (1 : ℤ))
    (T.commShiftIso (1 : ℤ)) A B hA hB mA mB
  obtain ⟨s, hs⟩ := Functor.exists_commShift_of_one F a
  refine ⟨s, ?_⟩
  intro K
  rw [hs]
  exact ha K

private theorem scalarShift_existsUnique
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    {C : Type*} [Category C] [Preadditive C] [Linear R C] [HasShift C ℤ]
    {D : Type*} [Category D] [Preadditive D] [Linear S D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [(shiftFunctor C (1 : ℤ)).Linear R]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [(shiftFunctor D (1 : ℤ)).Linear S]
    (t : R) (v : S) (ψ : Localization.Away t → Localization.Away v)
    [HasShift (ScalarLocalization R C t) ℤ] [HasShift (ScalarLocalization S D v) ℤ]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization R C t) n).Additive]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization S D v) n).Additive]
    (hC : shiftFunctor (ScalarLocalization R C t) (1 : ℤ) =
      ScalarLocalization.map R C t (shiftFunctor C (1 : ℤ)))
    (hD : shiftFunctor (ScalarLocalization S D v) (1 : ℤ) =
      ScalarLocalization.map S D v (shiftFunctor D (1 : ℤ)))
    (T : C ⥤ D) [T.CommShift ℤ]
    (F : ScalarLocalization R C t ⥤ ScalarLocalization S D v) [F.Additive]
    (hF : ∀ K, F.obj K = ⟨T.obj K.obj⟩)
    (mF : ∀ (K K' : C) (f : K ⟶ K') (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R] f : ScalarLocalization.mk (R := R) (p := t) K ⟶ ⟨K'⟩))
        (ψ a ⊗ₜ[S] T.map f : ScalarLocalization.mk (R := S) (p := v) (T.obj K) ⟶
          ⟨T.obj K'⟩)) :
    ∃! s : F.CommShift ℤ, ∀ K,
      HEq ((Functor.commShiftIso F (self := s) (1 : ℤ)).hom.app K)
        ((ScalarLocalization.localization S D v).map ((T.commShiftIso (1 : ℤ)).hom.app K.obj)) := by
  obtain ⟨s, hs⟩ := scalarShift_exists t v ψ hC hD T F hF mF
  refine ⟨s, hs, ?_⟩
  intro s' hs'
  apply commShift_one_ext
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((hs' K).trans (hs K).symm)


private theorem finite_scalar_shift
    (p l : ℕ) [Fact l.Prime] (hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})
    [(sfConstructibleIntegralScalarExtension p l hl E L i Y).CommShift ℤ] :
    ∃! c : (sfRationalScalarExtension l E Y p hl L i).CommShift ℤ,
      ∀ K : sfRationalConstructibleCategory l E Y,
        HEq ((Functor.commShiftIso (sfRationalScalarExtension l E Y p hl L i)
            (self := c) (1 : ℤ)).hom.app K)
          ((sfRationalConstructibleLocalization l L Y).map
            (((sfConstructibleIntegralScalarExtension p l hl E L i Y).commShiftIso
              (1 : ℤ)).hom.app K.obj)) := by
  let : ∀ n : ℤ, (shiftFunctor (sfIntegralConstructibleCategory l E Y) n).Additive :=
    fun n ↦ inferInstance
  let : ∀ n : ℤ, (shiftFunctor (sfIntegralConstructibleCategory l L Y) n).Additive :=
    fun n ↦ inferInstance
  let : ∀ n : ℤ, (shiftFunctor (sfRationalConstructibleCategory l E Y) n).Additive :=
    fun n ↦ sfRationalConstructibleShiftAdditive l E Y n
  let : ∀ n : ℤ, (shiftFunctor (sfRationalConstructibleCategory l L Y) n).Additive :=
    fun n ↦ sfRationalConstructibleShiftAdditive l L Y n
  have hsE := (sfRationalTriangulationDatum l E Y).choose_spec.choose_spec.1
  have hsL := (sfRationalTriangulationDatum l L Y).choose_spec.choose_spec.1
  exact scalarShift_existsUnique
    (R := Padic.coefficientExtensionIntegers l E)
    (S := Padic.coefficientExtensionIntegers l L)
    (C := sfIntegralConstructibleCategory l E Y)
    (D := sfIntegralConstructibleCategory l L Y)
    (Padic.coefficientExtensionUniformizer l E) (Padic.coefficientExtensionUniformizer l L)
    (fun a ↦ (sfRationalCoefficientEquiv l L).symm (i (sfRationalCoefficientEquiv l E a)))
    hsE hsL (sfConstructibleIntegralScalarExtension p l hl E L i Y)
    (sfRationalScalarExtension l E Y p hl L i)
    (sfRationalScalarExtension_obj l E Y p hl L i)
    (sfRationalScalarExtension_map_tmul l E Y p hl L i)


end



attribute [local irreducible] ScalarLocalization.category sfRationalTriangulationDatum
  sfRationalScalarExtension sfRationalScalarComp sfRationalScalarUnit
  sfIntegralScalarComp sfIntegralScalarUnit sfIntegralOrdinaryComparison

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)

private abbrev PairCommon
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    {S : StageSystem C} (A B : S.PairCategory) :=
  {L : I // A.stage ≤ L ∧ B.stage ≤ L}
private abbrev PairStageHom
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    {S : StageSystem C} (A B : S.PairCategory) (L : PairCommon A B) :=
  (S.T L.property.1).obj A.obj ⟶ (S.T L.property.2).obj B.obj
private theorem generic_coordinates
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    (S : StageSystem C) (A B : S.PairCategory)
    [∀ L : PairCommon A B, AddCommGroup (PairStageHom A B L)]
    [Nonempty (PairCommon A B)] [IsDirectedOrder (PairCommon A B)]
    [DecidableEq (PairCommon A B)]
    (t : ∀ L M : PairCommon A B, L ≤ M → PairStageHom A B L →+ PairStageHom A B M)
    (ht : ∀ L M h f, t L M h f = S.tr h f)
    (dt : DirectedSystem (PairStageHom A B) (fun {L M} h ↦ t L M h)) :
    ∃! e : (A ⟶ B) ≃ AddCommGroup.DirectLimit (PairStageHom A B) t,
      ∀ L hA hB f, e (StageSystem.PairCategory.mkHom L hA hB f) =
        AddCommGroup.DirectLimit.of (PairStageHom A B) t ⟨L, hA, hB⟩ f := by
  classical
  let q : (A ⟶ B) ≃ _root_.DirectLimit ((PairStageHom A B))
      (fun L M h ↦ t L M h) :=
    { toFun := Quotient.lift
        (fun r : StageSystem.PairCategory.Rep A B ↦
          ⟦⟨⟨r.k, r.hX, r.hY⟩, r.u⟩⟧)
        (by
          rintro r s ⟨N, hr, hs, he⟩
          apply Quotient.sound
          refine ⟨⟨N, r.hX.trans hr, r.hY.trans hr⟩, hr, hs, ?_⟩
          simpa only [ht] using he)
      invFun := Quotient.lift
        (fun r : Σ L : (PairCommon A B), (PairStageHom A B) L ↦
          StageSystem.PairCategory.mkHom r.1.val r.1.property.1 r.1.property.2 r.2)
        (by
          rintro ⟨L, f⟩ ⟨M, g⟩ ⟨N, hL, hM, he⟩
          exact (StageSystem.PairCategory.mkHom_eq_mkHom_iff' f g).2
            ⟨N.val, hL, hM, by simpa only [ht] using he⟩)
      left_inv := by intro f; induction f using Quotient.inductionOn; rfl
      right_inv := by intro f; induction f using Quotient.inductionOn; rfl }
  have : DirectedSystem ((PairStageHom A B))
      (fun L M h ↦ (t L M h).toNatLinearMap) := by
    constructor
    · intro L f
      exact @DirectedSystem.map_self _ _ ((PairStageHom A B))
        (fun {L M} h ↦ t L M h) dt L f
    · intro N M L h k f
      exact @DirectedSystem.map_map _ _ ((PairStageHom A B))
        (fun {L M} h ↦ t L M h) dt N M L h k f
  let e : (A ⟶ B) ≃ AddCommGroup.DirectLimit (PairStageHom A B) t := q.trans
    (Module.DirectLimit.linearEquiv ((PairStageHom A B))
      (fun L M h ↦ (t L M h).toNatLinearMap)).symm.toEquiv
  have he (L : I) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (f : (PairStageHom A B) ⟨L, hA, hB⟩) :
      e (StageSystem.PairCategory.mkHom L hA hB f) =
        AddCommGroup.DirectLimit.of (PairStageHom A B) t ⟨L, hA, hB⟩ f := by
    rfl
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Equiv.ext
  intro f
  induction f using StageSystem.PairCategory.hom_induction with
  | h L hA hB f => exact (he' L hA hB f).trans (he L hA hB f).symm

private theorem coordinates_add
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    (S : StageSystem C) (A B : S.PairCategory)
    [∀ L : PairCommon A B, AddCommGroup (PairStageHom A B L)]
    [Nonempty (PairCommon A B)] [IsDirectedOrder (PairCommon A B)]
    [DecidableEq (PairCommon A B)]
    (t : ∀ L M : PairCommon A B, L ≤ M → PairStageHom A B L →+ PairStageHom A B M)
    (e : (A ⟶ B) ≃ AddCommGroup.DirectLimit (PairStageHom A B) t)
    (he : ∀ L hA hB f, e (StageSystem.PairCategory.mkHom L hA hB f) =
      AddCommGroup.DirectLimit.of (PairStageHom A B) t ⟨L, hA, hB⟩ f)
    (L : I) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f g : PairStageHom A B ⟨L, hA, hB⟩) :
    letI := e.addCommGroup
    StageSystem.PairCategory.mkHom L hA hB f +
      StageSystem.PairCategory.mkHom L hA hB g =
        StageSystem.PairCategory.mkHom L hA hB (f + g) := by
  let := e.addCommGroup
  apply e.injective
  rw [show e (_ + _) = e _ + e _ from e.addEquiv.map_add _ _,
    he L hA hB f, he L hA hB g, he L hA hB (f + g)]
  exact (map_add (AddCommGroup.DirectLimit.of (PairStageHom A B) t
    ⟨L, hA, hB⟩) f g).symm

private theorem coordinates_zero
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    (S : StageSystem C) (A B : S.PairCategory)
    [∀ L : PairCommon A B, AddCommGroup (PairStageHom A B L)]
    [Nonempty (PairCommon A B)] [IsDirectedOrder (PairCommon A B)]
    [DecidableEq (PairCommon A B)]
    (t : ∀ L M : PairCommon A B, L ≤ M → PairStageHom A B L →+ PairStageHom A B M)
    (e : (A ⟶ B) ≃ AddCommGroup.DirectLimit (PairStageHom A B) t)
    (he : ∀ L hA hB f, e (StageSystem.PairCategory.mkHom L hA hB f) =
      AddCommGroup.DirectLimit.of (PairStageHom A B) t ⟨L, hA, hB⟩ f)
    (L : I) (hA : A.stage ≤ L) (hB : B.stage ≤ L) :
    letI := e.addCommGroup
    StageSystem.PairCategory.mkHom L hA hB
      (0 : PairStageHom A B ⟨L, hA, hB⟩) = 0 := by
  let := e.addCommGroup
  apply e.injective
  rw [he L hA hB (0 : PairStageHom A B ⟨L, hA, hB⟩),
    show e (0 : A ⟶ B) = 0 from e.addEquiv.map_zero]
  exact map_zero (AddCommGroup.DirectLimit.of (PairStageHom A B) t ⟨L, hA, hB⟩)

private theorem pair_composition_bilinear
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)]
    (S : StageSystem C) [∀ A B : S.PairCategory, AddCommGroup (A ⟶ B)]
    (hadd : ∀ {A B : S.PairCategory} {L : I} (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (f g : A.toStage hA ⟶ B.toStage hB),
      StageSystem.PairCategory.mkHom L hA hB f +
        StageSystem.PairCategory.mkHom L hA hB g =
          StageSystem.PairCategory.mkHom L hA hB (f + g)) :
    (∀ (A B C : S.PairCategory) (f f' : A ⟶ B) (g : B ⟶ C),
      (f + f') ≫ g = f ≫ g + f' ≫ g) ∧
    (∀ (A B C : S.PairCategory) (f : A ⟶ B) (g g' : B ⟶ C),
      f ≫ (g + g') = f ≫ g + f ≫ g') := by
  constructor
  · intro A B C f f' g
    obtain ⟨L, -, hA, hB, _, _, u, v, rfl, rfl⟩ :=
      StageSystem.PairCategory.exists_common_stage f f' A.stage
    obtain ⟨M, hLM, hB', hC, _, _, w, _, rfl, -⟩ :=
      StageSystem.PairCategory.exists_common_stage g g L
    rw [← StageSystem.PairCategory.mkHom_tr hLM u,
      ← StageSystem.PairCategory.mkHom_tr hLM v, hadd,
      StageSystem.PairCategory.mkHom_comp_mkHom,
      StageSystem.PairCategory.mkHom_comp_mkHom,
      StageSystem.PairCategory.mkHom_comp_mkHom, hadd, Preadditive.add_comp]
  · intro A B C f g g'
    obtain ⟨L, -, hB, hC, _, _, v, w, rfl, rfl⟩ :=
      StageSystem.PairCategory.exists_common_stage g g' B.stage
    obtain ⟨M, hLM, hA, hB', _, _, u, _, rfl, -⟩ :=
      StageSystem.PairCategory.exists_common_stage f f L
    rw [← StageSystem.PairCategory.mkHom_tr hLM v,
      ← StageSystem.PairCategory.mkHom_tr hLM w, hadd,
      StageSystem.PairCategory.mkHom_comp_mkHom,
      StageSystem.PairCategory.mkHom_comp_mkHom,
      StageSystem.PairCategory.mkHom_comp_mkHom, hadd, Preadditive.comp_add]

private theorem stage_transport_additive
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    [∀ i, Preadditive (C i)] (S : StageSystem C)
    {i j n p : I} (hi : i ≤ n) (hj : j ≤ n) (h : n ≤ p)
    [(S.T h).Additive] (x : C i) (y : C j) :
    S.tr (hi := hi) (hj := hj) h (0 : (S.T hi).obj x ⟶ (S.T hj).obj y) = 0 ∧
      ∀ f g : (S.T hi).obj x ⟶ (S.T hj).obj y,
        S.tr h (f + g) = S.tr h f + S.tr h g := by
  constructor
  · simp only [StageSystem.tr, Functor.map_zero, Limits.comp_zero, Limits.zero_comp]
  · intro f g
    simp only [StageSystem.tr, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

private theorem stage_transport_self
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    (S : StageSystem C) {i j n : I} (hi : i ≤ n) (hj : j ≤ n)
    [(S.T (le_refl n)).Faithful] (x : C i) (y : C j)
    (f : (S.T hi).obj x ⟶ (S.T hj).obj y) : S.tr (le_refl n) f = f := by
  apply (S.T (le_refl n)).map_injective
  apply (StageSystem.tr_injective (S := S) (le_refl n)).mp
  exact StageSystem.tr_tr (S := S) (le_refl n) (le_refl n) f


private theorem stage_spec_existsUnique
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    (T : ∀ {i j : I}, i ≤ j → C i ⥤ C j)
    (a : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k), T h ⋙ T h' ≅ T (h.trans h'))
    (c : ∀ {i j k m : I} (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ m),
      Functor.whiskerRight (a h h').hom (T h'') ≫ (a (h.trans h') h'').hom =
        (Functor.associator (T h) (T h') (T h'')).hom ≫
          Functor.whiskerLeft (T h) (a h' h'').hom ≫ (a h (h'.trans h'')).hom) :
    ∃! R : StageSystem C,
      (∀ (i j : I) (h : i ≤ j), R.T h = T h) ∧
      (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k), HEq (R.assoc h h') (a h h')) := by
  let S : StageSystem C :=
    { T := T
      assoc := a
      cocycle := fun h h' h'' X ↦ by
        simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.associator_hom_app, Category.id_comp] using
          NatTrans.congr_app (c h h' h'') X }
  refine ⟨S, ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ HEq.rfl⟩, ?_⟩
  rintro ⟨T', a', c'⟩ ⟨hT, ha⟩
  have ht : @T' = @T := by funext i j h; exact hT i j h
  cases ht
  have he : @a' = @a := by funext i j k h h'; exact eq_of_heq (ha i j k h h')
  cases he
  rfl

private theorem commShift_ext
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ] {F : C ⥤ D}
    (s t : F.CommShift ℤ)
    (h : ∀ n : ℤ, Functor.commShiftIso F (self := s) n =
      Functor.commShiftIso F (self := t) n) : s = t := by
  cases s
  cases t
  congr
  funext n
  exact h n

private theorem exact_cast
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F G : C ⥤ D) (e : F = G) (c : G.CommShift ℤ)
    (hc : @Functor.IsTriangulated _ _ _ _ _ _ G c _ _ _ _ _ _ _ _) :
    @Functor.IsTriangulated _ _ _ _ _ _ F
      (cast (congrArg (fun H : C ⥤ D ↦ H.CommShift ℤ) e.symm) c)
      _ _ _ _ _ _ _ _ := by
  subst G
  exact hc

private theorem normalized_shift_existsUnique
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (I : D ⥤ E) [I.Full] [I.Faithful] [I.CommShift ℤ]
    (H : C ⥤ E) [H.CommShift ℤ] (e : F ⋙ I ≅ H) :
    ∃! c : F.CommShift ℤ, ∀ n X,
      HEq (I.map ((Functor.commShiftIso F (self := c) n).hom.app X) ≫
        (I.commShiftIso n).hom.app (F.obj X))
        (e.hom.app ((shiftFunctor C n).obj X) ≫ (H.commShiftIso n).hom.app X ≫
          (shiftFunctor E n).map (e.inv.app X)) := by
  let c : F.CommShift ℤ := Functor.CommShift.ofComp e ℤ
  have hc (n : ℤ) (X : C) :
      HEq (I.map ((Functor.commShiftIso F (self := c) n).hom.app X) ≫
        (I.commShiftIso n).hom.app (F.obj X))
        (e.hom.app ((shiftFunctor C n).obj X) ≫ (H.commShiftIso n).hom.app X ≫
          (shiftFunctor E n).map (e.inv.app X)) := by
    change HEq (I.map ((Functor.CommShift.OfComp.iso e n).hom.app X) ≫
      (I.commShiftIso n).hom.app (F.obj X)) _
    simp [Category.assoc]
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  apply commShift_ext
  intro n
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply I.map_injective
  apply (cancel_mono ((I.commShiftIso n).hom.app (F.obj X))).mp
  exact eq_of_heq ((hc' n X).trans (hc n X).symm)


private noncomputable def correctedAssociator
    (p l : ℕ) [Fact l.Prime] (hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (ι : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M) (k : E →ₐ[Padic l] M)
    (h : j.comp ι = k) (Y : AlgebraicGeometry.Scheme.{u}) :
    sfRationalScalarExtension l E Y p hl L ι ⋙
        sfRationalScalarExtension l L Y p hl M j ≅
      sfRationalScalarExtension l E Y p hl M k :=
  sfRationalScalarComp l E L ι Y p hl M j ≪≫
    eqToIso (congrArg
      (sfRationalScalarExtension l E Y p hl M) h)

attribute [local irreducible] correctedAssociator

private theorem correctedAssociator_pentagon
    (p l : ℕ) [Fact l.Prime] (hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
    (Y : AlgebraicGeometry.Scheme.{u})
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M) (k : M →ₐ[Padic l] N)
    (ij : E →ₐ[Padic l] M) (jk : L →ₐ[Padic l] N) (ijk : E →ₐ[Padic l] N)
    (hij : j.comp i = ij) (hjk : k.comp j = jk)
    (hijk : k.comp ij = ijk) (hijk' : jk.comp i = ijk)
    (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarExtension l M Y p hl N k).map
        ((correctedAssociator p l hl E L M i j ij hij Y).hom.app K) ≫
        (correctedAssociator p l hl E M N ij k ijk hijk Y).hom.app K =
      (correctedAssociator p l hl L M N j k jk hjk Y).hom.app
          ((sfRationalScalarExtension l E Y p hl L i).obj K) ≫
        (correctedAssociator p l hl E L N i jk ijk hijk' Y).hom.app K := by
  subst ij
  subst jk
  subst ijk
  have hcast : (eqToIso (congrArg
      (sfRationalScalarExtension l E Y p hl N)
      hijk')).hom.app K = 𝟙 _ := by
    rfl
  unfold correctedAssociator
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [hcast]
  simp only [eqToIso.hom, eqToHom_refl, NatTrans.id_app,
    Category.comp_id]
  have hp := (sfRationalScalar_coherence l E L i Y p hl M j).2.2 N k K
  exact hp.trans (congrArg
    (fun f ↦ (sfRationalScalarComp l L M j Y p hl N k).hom.app
        ((sfRationalScalarExtension l E Y p hl L i).obj K) ≫ f)
    (Category.comp_id ((sfRationalScalarComp l E L i Y p hl N (k.comp j)).hom.app K))).symm


private theorem correctedAssociator_pentagon_nat
    (p l : ℕ) [Fact l.Prime] (hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
    (Y : AlgebraicGeometry.Scheme.{u})
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M) (k : M →ₐ[Padic l] N)
    (ij : E →ₐ[Padic l] M) (jk : L →ₐ[Padic l] N) (ijk : E →ₐ[Padic l] N)
    (hij : j.comp i = ij) (hjk : k.comp j = jk)
    (hijk : k.comp ij = ijk) (hijk' : jk.comp i = ijk)
    :
    Functor.whiskerRight (correctedAssociator p l hl E L M i j ij hij Y).hom
        (sfRationalScalarExtension l M Y p hl N k) ≫
        (correctedAssociator p l hl E M N ij k ijk hijk Y).hom =
      (Functor.associator
        (sfRationalScalarExtension l E Y p hl L i)
        (sfRationalScalarExtension l L Y p hl M j)
        (sfRationalScalarExtension l M Y p hl N k)).hom ≫
      Functor.whiskerLeft
        (sfRationalScalarExtension l E Y p hl L i)
        (correctedAssociator p l hl L M N j k jk hjk Y).hom ≫
      (correctedAssociator p l hl E L N i jk ijk hijk' Y).hom := by
  ext K
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] using
    correctedAssociator_pentagon p l hl E L M N Y i j k ij jk ijk hij hjk hijk hijk' K

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The specified raw rational stage, using its equivalent small coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def Stage (E : Index l Ω) :=
  D.sfRationalCategory l hl (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageCategory (E : Index l Ω) :
    Category (Stage D l hl Ω Y E) :=
  ScalarLocalization.category (Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω E))
    (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l Ω E))

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stagePreadditive (E : Index l Ω) :
    Preadditive (Stage D l hl Ω Y E) :=
  inferInstanceAs (Preadditive
    (D.sfRationalCategory l hl (Coefficient.{u} l Ω E) Y))

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageZero (E : Index l Ω) :
    HasZeroObject (Stage D l hl Ω Y E) :=
  sfRationalConstructibleZero l (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageShift (E : Index l Ω) :
    HasShift (Stage D l hl Ω Y E) ℤ :=
  sfRationalConstructibleShift l (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageShiftAdditive (E : Index l Ω) (n : ℤ) :
    (shiftFunctor (Stage D l hl Ω Y E) n).Additive :=
  sfRationalConstructibleShiftAdditive l (Coefficient.{u} l Ω E) Y n

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stagePretriangulated (E : Index l Ω) :
    Pretriangulated (Stage D l hl Ω Y E) :=
  sfRationalConstructiblePretriangulated l (Coefficient.{u} l Ω E) Y

/-- Cache the existing rational stage structure on the named coefficient model.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageTriangulated (E : Index l Ω) :
    IsTriangulated (Stage D l hl Ω Y E) :=
  sfRationalConstructibleTriangulated l (Coefficient.{u} l Ω E) Y

/-- The actual finite-field scalar transition, with both coefficient identifications.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transition (E L : Index l Ω) (h : E ≤ L) :
    Stage D l hl Ω Y E ⥤ Stage D l hl Ω Y L :=
  sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y D.p hl
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- The integral transition inherits the ordinary tensor shift through its canonical
quotient-completion comparison, not through an arbitrary exact-functor witness.
Source: blueprint order 1462, exact transition clause
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: conjugate the ordinary derived tensor shift by sfIntegralOrdinaryComparison.
The full intrinsic subcategory inherits the ambient shift. The inclusion's shift
comparisons identify its shifted objects with ambient shifts on both sides. Full
faithfulness lifts each component and its inverse. Naturality, the zero equation and
the addition equation follow from the ordinary ones by cancellation of the comparisons.
The formula fixes all components,
so extensionality of natural isomorphisms and proof irrelevance prove uniqueness. -/
theorem integralTransitionCommShift_existsUnique (E L : Index l Ω) (h : E ≤ L) :
    ∃! c : (sfConstructibleIntegralScalarExtension D.p l hl
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) Y).CommShift ℤ,
      (fun [commInst : (sfConstructibleIntegralScalarExtension D.p l hl
          (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) Y).CommShift ℤ] ↦
        ∀ (n : ℤ) (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y),
          HEq ((((sfConstructibleIntegralScalarExtension D.p l hl
            (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L h) Y).commShiftIso n).hom.app K).hom ≫
              ((sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι.commShiftIso n).hom.app
                ((sfConstructibleIntegralScalarExtension D.p l hl
                  (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
                  (coefficientInclusion l Ω E L h) Y).obj K))
            ((sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E)
                (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y).inv.app
                  ((shiftFunctor (sfIntegralConstructibleCategory l
                    (Coefficient.{u} l Ω E) Y) n).obj K) ≫
              (Functor.commShiftIso
                ((sfIntegralConstructible l (Coefficient.{u} l Ω E) Y).ι ⋙
                  integralOrdinaryDerivedScalar l (Coefficient.{u} l Ω E)
                    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y) n).hom.app K ≫
              (shiftFunctor (DerivedCategory (scalarReductionSource.{u, u} l
                (Coefficient.{u} l Ω L) Y)) n).map
                  ((sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E)
                    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y).hom.app K)))
        (commInst := c) := by
  exact normalized_shift_existsUnique
    (sfConstructibleIntegralScalarExtension D.p l hl
      (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y)
    (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι
    ((sfIntegralConstructible l (Coefficient.{u} l Ω E) Y).ι ⋙
      integralOrdinaryDerivedScalar l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y)
    (sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y).symm

/-- The fixed ordinary-to-completed normalization of the integral transition shift.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance integralTransitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (sfConstructibleIntegralScalarExtension D.p l hl
      (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) Y).CommShift ℤ :=
  (integralTransitionCommShift_existsUnique D l hl Ω Y E L h).exists.choose

set_option linter.unusedVariables false in
/-- The rational transition shift is uniquely fixed by localizing the normalized integral
shift. Source: blueprint order 1462, exact transition clause
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: tensor the integral components and inverses with one. On pure tensors, integral
naturality gives rational naturality; generation gives it on every Hom. The recorded
rational shift and localization comparison are normalized to the integral shift and
identity at one. Thus the displayed HEq gives the shift-by-one comparison. Iteration and
inverse shifts give all integer comparisons and their coherence. A coherent integer-shift
comparison is determined at one, which also proves uniqueness. -/
theorem transitionCommShift_existsUnique (E L : Index l Ω) (h : E ≤ L) :
    ∃! c : (transition D l hl Ω Y E L h).CommShift ℤ,
      (fun [commInst : (transition D l hl Ω Y E L h).CommShift ℤ] ↦
        ∀ K : Stage D l hl Ω Y E,
          HEq (((transition D l hl Ω Y E L h).commShiftIso (1 : ℤ)).hom.app K)
            ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).map
              (((sfConstructibleIntegralScalarExtension D.p l hl
                (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
                (coefficientInclusion l Ω E L h) Y).commShiftIso (1 : ℤ)).hom.app K.obj)))
        (commInst := c) := by
  dsimp only [transition]
  exact finite_scalar_shift D.p l hl
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) Y

/-- The canonical, integral-image-normalized shift comparison of the rational transition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance transitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (transition D l hl Ω Y E L h).CommShift ℤ :=
  (transitionCommShift_existsUnique D l hl Ω Y E L h).exists.choose

section

/-- Exactness for the normalized shift comparison on the recorded intrinsic rational stages.
Source: blueprint order 1462, exact transition clause
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: use the exactness argument of sfScalarExtension_exact_triangulated: the Roos cone
shift is conjugate through the quotient-completion comparison to the ordinary tensor
shift. Full intrinsic subcategories inherit distinguished triangles, and rationalization
has precisely the isomorphic integral image triangles. The preceding normalization is
that same comparison, so the finite scalar transition preserves distinguished triangles
including their connecting arrows. -/
@[instance]
theorem transitionExact (E L : Index l Ω) (h : E ≤ L) :
    (transition D l hl Ω Y E L h).IsTriangulated := by
  let : ∀ n : ℤ, (shiftFunctor
      (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y) n).Additive :=
    fun n ↦ inferInstance
  let : ∀ n : ℤ, (shiftFunctor
      (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω L) Y) n).Additive :=
    fun n ↦ inferInstance
  let : ∀ n : ℤ, (shiftFunctor
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y) n).Additive :=
    fun n ↦ sfRationalConstructibleShiftAdditive l (Coefficient.{u} l Ω E) Y n
  let : ∀ n : ℤ, (shiftFunctor
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω L) Y) n).Additive :=
    fun n ↦ sfRationalConstructibleShiftAdditive l (Coefficient.{u} l Ω L) Y n
  let T := sfConstructibleIntegralScalarExtension D.p l hl
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y
  let : T.CommShift ℤ := integralTransitionCommShift D l hl Ω Y E L h
  let I := (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι
  let H := (sfIntegralConstructible l (Coefficient.{u} l Ω E) Y).ι ⋙
    integralOrdinaryDerivedScalar l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y
  let e : T ⋙ I ≅ H := (sfIntegralOrdinaryComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) Y).symm
  have : NatTrans.CommShift e.hom ℤ := normalized_compatibility T I H e
    (integralTransitionCommShift_existsUnique D l hl Ω Y E L h).exists.choose_spec
  have hI : I.IsTriangulated := by
    change (sfIntegralConstructible l (Coefficient.{u} l Ω L) Y).ι.IsTriangulated
    infer_instance
  have hH : H.IsTriangulated := by
    dsimp only [H]
    infer_instance
  have hT : T.IsTriangulated :=
    (Functor.isTriangulated_iff_comp_right (F := T) (G := I) (H := H) e).2
      hH
  let : (sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y D.p hl
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)).CommShift ℤ :=
    transitionCommShift D l hl Ω Y E L h
  exact sfRationalScalarExactOfIntegral D.p l hl
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) Y
    (t := integralTransitionCommShift D l hl Ω Y E L h)
    (ht := hT) (s := transitionCommShift D l hl Ω Y E L h)
    (transitionCommShift_existsUnique D l hl Ω Y E L h).exists.choose_spec

end


/-- Additivity of the published intrinsic rational scalar-extension functor.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance transitionAdditive (E L : Index l Ω) (h : E ≤ L) :
    (transition D l hl Ω Y E L h).Additive :=
  sfRationalScalarExtension_additive l (Coefficient.{u} l Ω E) Y D.p hl
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h)

/-- The canonical scalar associator, with its tensor-generator normalization.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def associator (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    transition D l hl Ω Y E L h ⋙ transition D l hl Ω Y L M k ≅
      transition D l hl Ω Y E M (h.trans k) :=
  sfRationalScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) Y D.p hl (Coefficient.{u} l Ω M)
    (coefficientInclusion l Ω L M k) ≪≫
    eqToIso (congrArg (sfRationalScalarExtension l
      (Coefficient.{u} l Ω E) Y D.p hl (Coefficient.{u} l Ω M))
      ((coefficientInclusion_laws l Ω).2 E L M h k))

/-- The normalized scalar unit, transported through the coefficient identifications.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def unitor (E : Index l Ω) : transition D l hl Ω Y E E le_rfl ≅
    𝟭 (Stage D l hl Ω Y E) :=
  eqToIso (congrArg (sfRationalScalarExtension l
    (Coefficient.{u} l Ω E) Y D.p hl (Coefficient.{u} l Ω E))
    ((coefficientInclusion_laws l Ω).1 E)) ≪≫
    sfRationalScalarUnit l (Coefficient.{u} l Ω E) Y D.p hl

attribute [local irreducible] transition associator unitor
  stagePreadditive stageShift stagePretriangulated

section

-- Compare whole natural transformations before taking components. This keeps the
-- proof-irrelevant inclusion witnesses out of large functor-object conversions.
private theorem associator_pentagon
    (E L M N : Padic.FiniteCoefficientFields l Ω)
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N) :
    Functor.whiskerRight (associator D l hl Ω Y E L M h k).hom (transition D l hl Ω Y M N m) ≫
        (associator D l hl Ω Y E M N (h.trans k) m).hom =
      (Functor.associator (transition D l hl Ω Y E L h) (transition D l hl Ω Y L M k)
        (transition D l hl Ω Y M N m)).hom ≫
      Functor.whiskerLeft (transition D l hl Ω Y E L h) (associator D l hl Ω Y L M N k m).hom ≫
        (associator D l hl Ω Y E L N h (k.trans m)).hom := by
  have hp := correctedAssociator_pentagon_nat D.p l hl
      (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (Coefficient.{u} l Ω M) (Coefficient.{u} l Ω N) Y
      (coefficientInclusion l Ω E L h) (coefficientInclusion l Ω L M k)
      (coefficientInclusion l Ω M N m) (coefficientInclusion l Ω E M (h.trans k))
      (coefficientInclusion l Ω L N (k.trans m))
      (coefficientInclusion l Ω E N ((h.trans k).trans m))
      ((coefficientInclusion_laws l Ω).2 E L M h k)
      ((coefficientInclusion_laws l Ω).2 L M N k m)
      ((coefficientInclusion_laws l Ω).2 E M N (h.trans k) m)
      ((coefficientInclusion_laws l Ω).2 E L N h (k.trans m))
  unfold associator
  delta transition
  with_unfolding_all exact hp

/-- The normalized tensor associators satisfy the stage-system cocycle.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: sfRationalScalar_coherence proves the tensor pentagon. The small
coefficient inclusions compose by coefficientInclusion_laws. Substitution gives the
displayed cocycle, including repeated fields and identity inclusions. -/
theorem associator_cocycle
    (D : WeilConjectures.FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    (E L M N : Padic.FiniteCoefficientFields l Ω)
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N) (K : SfAlgebraicallyClosedCoefficients.Stage D l hl Ω Y E) :
    (SfAlgebraicallyClosedCoefficients.transition D l hl Ω Y M N m).map
        ((SfAlgebraicallyClosedCoefficients.associator D l hl Ω Y E L M h k).hom.app K) ≫
        (SfAlgebraicallyClosedCoefficients.associator D l hl Ω Y E M N (h.trans k) m).hom.app K =
      (SfAlgebraicallyClosedCoefficients.associator D l hl Ω Y L M N k m).hom.app
          ((SfAlgebraicallyClosedCoefficients.transition D l hl Ω Y E L h).obj K) ≫
        (SfAlgebraicallyClosedCoefficients.associator D l hl Ω Y E L N h (k.trans m)).hom.app K :=
            by
  have hc := NatTrans.congr_app (associator_pentagon D l hl Ω Y E L M N h k m) K
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] using hc

/-- The tensor transitions and associators uniquely determine the stage system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: take T to be transition and assoc to be associator; associator_cocycle is
precisely the required coherence equation. Conversely the displayed equalities fix
all data fields of StageSystem; the remaining cocycle proof is proof irrelevant. -/
theorem stageSystem_existsUnique
    (D : WeilConjectures.FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    :
    ∃! S : StageSystem (SfAlgebraicallyClosedCoefficients.Stage D l hl Ω Y),
      (∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L), S.T h =
          SfAlgebraicallyClosedCoefficients.transition D l hl Ω Y E L h) ∧
      (∀ (E L M : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) (k : L ≤ M),
        HEq (S.assoc h k) (SfAlgebraicallyClosedCoefficients.associator D l hl Ω Y E L M h k)) := by
  exact stage_spec_existsUnique
    (fun {E L} h ↦ transition D l hl Ω Y E L h)
    (fun {E L M} h k ↦ associator D l hl Ω Y E L M h k)
    (fun {E L M N} h k m ↦ associator_pentagon D l hl Ω Y E L M N h k m)


end

attribute [local irreducible] Stage stageCategory

/-- The stage system with exactly the specified tensor functors and associators.
The uniqueness specification fixes every data field, retaining a small opaque interface
for later elaboration of dependent representative types.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev stageSystem : StageSystem (Stage D l hl Ω Y) :=
  (stageSystem_existsUnique D l hl Ω Y).exists.choose

/-- The existing tensor functor as a transition of the uniquely fixed stage system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev stageTransition (E L : Index l Ω) (h : E ≤ L) :=
  (stageSystem D l hl Ω Y).T h

/-- The specified shift comparison transported by equality of the transition functors.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageTransitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (stageTransition D l hl Ω Y E L h).CommShift ℤ :=
  cast (congrArg (fun F : Stage D l hl Ω Y E ⥤ Stage D l hl Ω Y L ↦ F.CommShift ℤ)
    ((stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.1 E L h).symm)
    (transitionCommShift D l hl Ω Y E L h)

/-- Exactness of the prescribed stage transition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: stageSystem_existsUnique identifies this functor and its shift comparison
with the specified tensor extension. Apply transitionExact. -/
@[instance]
theorem stageTransition_exact
    (D : WeilConjectures.FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) :
    (SfAlgebraicallyClosedCoefficients.stageTransition D l hl Ω Y E L h).IsTriangulated := by
  exact exact_cast _ _
    ((stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.1 E L h)
    (transitionCommShift D l hl Ω Y E L h) (transitionExact D l hl Ω Y E L h)

/-- Additivity of the prescribed stage transition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: equality of functors with transition reduces the claim to transitionAdditive. -/
@[instance]
theorem stageTransition_additive
    (D : WeilConjectures.FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) :
    (SfAlgebraicallyClosedCoefficients.stageTransition D l hl Ω Y E L h).Additive := by
  unfold stageTransition
  rw [(stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.1 E L h]
  exact transitionAdditive D l hl Ω Y E L h

/-- The upstream common-stage pair category, specialized to the specified rational stages.
Its objects are literal pairs, and no idempotents are adjoined.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev Pair := (stageSystem D l hl Ω Y).PairCategory

/-- Cache the existing upstream category on the named concrete pair type.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance pairCategory : Category (Pair D l hl Ω Y) :=
  inferInstanceAs (Category (stageSystem D l hl Ω Y).PairCategory)

variable {D l hl Ω Y}

/-- The directed index of common finite coefficient overfields of two pairs.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
abbrev Common (A B : Pair D l hl Ω Y) :=
  {L : Index l Ω // A.stage ≤ L ∧ B.stage ≤ L}

/-- The compositum of the source and target fields supplies a common coefficient stage.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance commonNonempty (A B : Pair D l hl Ω Y) : Nonempty (Common A B) :=
  ⟨⟨Padic.finiteCoefficientCompositum l Ω A.stage B.stage,
    (Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage⟩⟩

/-- Composita make the common-overfield poset directed while retaining both lower bounds.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance commonDirected (A B : Pair D l hl Ω Y) :
    IsDirectedOrder (Common A B) where
  directed L M :=
    ⟨⟨Padic.finiteCoefficientCompositum l Ω L.val M.val,
        L.property.1.trans ((Padic.finiteCoefficientFields_properties l Ω).1 L.val M.val).1,
        L.property.2.trans ((Padic.finiteCoefficientFields_properties l Ω).1 L.val M.val).1⟩,
      (Padic.finiteCoefficientFields_properties l Ω).1 L.val M.val⟩

/-- Hom at one common coefficient field.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def StageHom (A B : Pair D l hl Ω Y) (L : Common A B) :=
  ((stageTransition D l hl Ω Y A.stage L.val L.property.1).obj A.obj ⟶
    (stageTransition D l hl Ω Y B.stage L.val L.property.2).obj B.obj)

/-- Cache the abelian group of a stage Hom before forming the dependent colimit family.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageHomAddCommGroup (A B : Pair D l hl Ω Y) (L : Common A B) :
    AddCommGroup (StageHom A B L) :=
  inferInstanceAs (AddCommGroup
    ((stageTransition D l hl Ω Y A.stage L.val L.property.1).obj A.obj ⟶
      (stageTransition D l hl Ω Y B.stage L.val L.property.2).obj B.obj))

/-- Extend the representative and conjugate by the specified associators.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transport (A B : Pair D l hl Ω Y) (L M : Common A B) (h : L ≤ M)
    (f : StageHom A B L) : StageHom A B M :=
  ((stageSystem D l hl Ω Y).assoc L.property.1 h).inv.app A.obj ≫
    (stageTransition D l hl Ω Y L.val M.val h).map f ≫
    ((stageSystem D l hl Ω Y).assoc L.property.2 h).hom.app B.obj

/-- Transport is additive and preserves zero.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: scalar extension is additive. Left and right composition by each fixed
associator component are additive by preadditivity of the rational target stage. -/
theorem transport_additive
    {D : WeilConjectures.FiniteFieldDatum.{d}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (A B : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) (L M :
        SfAlgebraicallyClosedCoefficients.Common A B) (h : L ≤ M) :
    SfAlgebraicallyClosedCoefficients.transport A B L M h 0 = 0 ∧
      ∀ f g, SfAlgebraicallyClosedCoefficients.transport A B L M h (f + g) =
        SfAlgebraicallyClosedCoefficients.transport A B L M h f +
            SfAlgebraicallyClosedCoefficients.transport A B L M h g := by
  exact stage_transport_additive (stageSystem D l hl Ω Y)
    L.property.1 L.property.2 h A.obj B.obj

/-- The transition homomorphism of the directed Hom system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transportHom (A B : Pair D l hl Ω Y) (L M : Common A B) (h : L ≤ M) :
    StageHom A B L →+ StageHom A B M where
  toFun := transport A B L M h
  map_zero' := (transport_additive A B L M h).1
  map_add' := (transport_additive A B L M h).2

/-- The actual representative transports form a directed system of abelian groups.
Source: blueprint order 1462, displayed Hom colimit
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: for a reflexive extension, the normalized tensor unit and the two unit coherence
laws identify the conjugated map with the original map. For two successive extensions,
expand transport and use the associator cocycle and naturality; the inner inverse
associators cancel. This gives identity and composition on each representative. -/
@[instance]
theorem transportSystem (A B : Pair D l hl Ω Y) :
    DirectedSystem (StageHom A B) (fun {L M} h ↦ transportHom A B L M h) := by
  -- Faithfulness turns the cocycle's idempotent reflexive transport into the identity.
  constructor
  · intro L f
    have hf : (stageTransition D l hl Ω Y L.val L.val le_rfl).Faithful := by
      unfold stageTransition
      rw [(stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.1 L.val L.val le_rfl]
      exact Functor.Faithful.of_iso (unitor D l hl Ω Y L.val).symm
    exact stage_transport_self (stageSystem D l hl Ω Y)
      L.property.1 L.property.2 A.obj B.obj f
  · intro N M L h k f
    exact StageSystem.tr_tr (S := stageSystem D l hl Ω Y) h k f

/-- Decidable equality is used only to realize Mathlib's algebraic direct limit.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance commonDecidableEq (A B : Pair D l hl Ω Y) :
    DecidableEq (Common A B) := Classical.decEq _

/-- The actual abelian-group colimit, with no completion of its objects.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def ColimitHom (A B : Pair D l hl Ω Y) :=
  AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)

/-- The direct limit's abelian group structure, on the fixed Hom type.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance colimitHomGroup (A B : Pair D l hl Ω Y) : AddCommGroup (ColimitHom A B) :=
  inferInstanceAs (AddCommGroup
    (AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)))

/-- The class of a map over a common finite coefficient field.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def colimitOf (A B : Pair D l hl Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) : ColimitHom A B :=
  AddCommGroup.DirectLimit.of (StageHom A B) (transportHom A B) ⟨L, hA, hB⟩ f

/-- The upstream quotient Hom has exactly the stated abelian-colimit coordinates.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: send each common-stage representative to its direct-limit class. The tensor
cocycle and unit law make transport a directed system; the quotient relation is exactly
equality after extension. The direct-limit representative criterion therefore makes
this map well-defined and bijective. Every Hom is represented, proving uniqueness. -/
theorem homCoordinates_existsUnique
    {D : WeilConjectures.FiniteFieldDatum.{d}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (A B : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) :
    ∃! e : (A ⟶ B) ≃ SfAlgebraicallyClosedCoefficients.ColimitHom A B,
      ∀ (L : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
        (f : SfAlgebraicallyClosedCoefficients.StageHom A B ⟨L, hA, hB⟩),
        e (StageSystem.PairCategory.mkHom L hA hB f) = SfAlgebraicallyClosedCoefficients.colimitOf A
            B L hA hB f := by
  exact @generic_coordinates (Index l Ω) inferInstance inferInstance (Stage D l hl Ω Y)
    (fun E ↦ stageCategory D l hl Ω Y E)
    (stageSystem D l hl Ω Y) A B (stageHomAddCommGroup A B)
    inferInstance inferInstance (commonDecidableEq A B)
    (transportHom A B) (fun _ _ _ _ ↦ rfl) (transportSystem A B)

/-- The canonical Hom coordinates, fixed on every common-stage representative.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def homCoordinates (A B : Pair D l hl Ω Y) :=
  (homCoordinates_existsUnique A B).exists.choose

/-- The abelian group transported from the specified directed colimit.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance homAddCommGroup (A B : Pair D l hl Ω Y) : AddCommGroup (A ⟶ B) :=
  (homCoordinates A B).addCommGroup

/-- The map represented at L, using the existing upstream quotient constructor.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev ofHom (A B : Pair D l hl Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) : A ⟶ B :=
  StageSystem.PairCategory.mkHom L hA hB f

private theorem mkHom_add {A B : Pair D l hl Ω Y} {L : Index l Ω}
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f g : A.toStage hA ⟶ B.toStage hB) :
    StageSystem.PairCategory.mkHom L hA hB f +
      StageSystem.PairCategory.mkHom L hA hB g =
        StageSystem.PairCategory.mkHom L hA hB (f + g) := by
  exact @coordinates_add (Index l Ω) inferInstance inferInstance (Stage D l hl Ω Y)
    (fun E ↦ stageCategory D l hl Ω Y E)
    (stageSystem D l hl Ω Y) A B (stageHomAddCommGroup A B)
    inferInstance inferInstance (commonDecidableEq A B)
    (transportHom A B) (homCoordinates A B)
    (homCoordinates_existsUnique A B).exists.choose_spec L hA hB f g

private theorem mkHom_zero {A B : Pair D l hl Ω Y} {L : Index l Ω}
    (hA : A.stage ≤ L) (hB : B.stage ≤ L) :
    StageSystem.PairCategory.mkHom L hA hB (0 : A.toStage hA ⟶ B.toStage hB) = 0 := by
  exact @coordinates_zero (Index l Ω) inferInstance inferInstance (Stage D l hl Ω Y)
    (fun E ↦ stageCategory D l hl Ω Y E)
    (stageSystem D l hl Ω Y) A B (stageHomAddCommGroup A B)
    inferInstance inferInstance (commonDecidableEq A B)
    (transportHom A B) (homCoordinates A B)
    (homCoordinates_existsUnique A B).exists.choose_spec L hA hB

/-- The fixed composition is additive in each variable.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: represent the three maps at a common compositum. Colimit structure maps are
additive and stage composition is bilinear, giving both asserted equations. -/
theorem composition_bilinear
    {D : WeilConjectures.FiniteFieldDatum.{d}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    :
    (∀ (A B C : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) (f f' : A ⟶ B) (g : B ⟶ C),
      (f + f') ≫ g = f ≫ g + f' ≫ g) ∧
    (∀ (A B C : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) (f : A ⟶ B) (g g' : B ⟶ C),
      f ≫ (g + g') = f ≫ g + f ≫ g') := by
  exact pair_composition_bilinear (stageSystem D l hl Ω Y)
    (fun hA hB f g ↦ mkHom_add hA hB f g)

/-- Preadditivity uses the actual colimit abelian groups.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance preadditive : Preadditive (Pair D l hl Ω Y) where
  homGroup A B := homAddCommGroup A B
  add_comp A B C f f' g := composition_bilinear.1 A B C f f' g
  comp_add A B C f g g' := composition_bilinear.2 A B C f g g'

/-- The existing upstream inclusion of the actual rational finite stage.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev inclusion (E : Index l Ω) : Stage D l hl Ω Y E ⥤ Pair D l hl Ω Y :=
  (stageSystem D l hl Ω Y).ι E

/-- The inclusion preserves the abelian-colimit addition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: inclusion sends f to its normalized representative, and homCoordinates sends
that representative to its direct-limit class. Both normalization by fixed unit
components and the direct-limit structure maps are additive. -/
@[instance]
theorem inclusion_additive
    {D : WeilConjectures.FiniteFieldDatum.{d}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (E : Padic.FiniteCoefficientFields l Ω) : (SfAlgebraicallyClosedCoefficients.inclusion E :
        SfAlgebraicallyClosedCoefficients.Stage D l hl Ω Y E ⥤ _).Additive := by
  constructor
  intro X Z f g
  rw [StageSystem.ι_map_eq le_rfl, StageSystem.ι_map_eq le_rfl,
    StageSystem.ι_map_eq le_rfl, Functor.map_add]
  exact (mkHom_add (D := D) (l := l) (hl := hl) (Ω := Ω) (Y := Y)
    (A := ⟨E, X⟩) (B := ⟨E, Z⟩) le_rfl le_rfl _ _).symm

/-- Every class has a finite representative, and equality is equality at a later stage.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: composita make each common-overfield index nonempty and directed. The normalized
tensor unit and associator pentagon make transport an actual directed system. Apply
Mathlib's directed-colimit representation and zero-exactness criteria to the difference
of two representatives. This gives precisely equality after one further extension. -/
theorem representatives
    {D : WeilConjectures.FiniteFieldDatum.{d}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (A B : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) :
    (∀ f : A ⟶ B, ∃ (L : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (u : SfAlgebraicallyClosedCoefficients.StageHom A B ⟨L, hA, hB⟩), f =
          SfAlgebraicallyClosedCoefficients.ofHom A B L hA hB u) ∧
    (∀ (L M : SfAlgebraicallyClosedCoefficients.Common A B) (f :
        SfAlgebraicallyClosedCoefficients.StageHom A B L) (g :
        SfAlgebraicallyClosedCoefficients.StageHom A B M),
      SfAlgebraicallyClosedCoefficients.ofHom A B L.val L.property.1 L.property.2 f =
          SfAlgebraicallyClosedCoefficients.ofHom A B M.val M.property.1 M.property.2 g ↔
        ∃ (N : SfAlgebraicallyClosedCoefficients.Common A B) (hL : L ≤ N) (hM : M ≤ N),
          SfAlgebraicallyClosedCoefficients.transport A B L N hL f =
              SfAlgebraicallyClosedCoefficients.transport A B M N hM g) := by
  constructor
  · intro f
    induction f using StageSystem.PairCategory.hom_induction with
    | h L hA hB f => exact ⟨L, hA, hB, f, rfl⟩
  · intro L M f g
    constructor
    · intro e
      obtain ⟨N, hL, hM, he⟩ :=
        (StageSystem.PairCategory.mkHom_eq_mkHom_iff' f g).mp e
      exact ⟨⟨N, L.property.1.trans hL, L.property.2.trans hL⟩, hL, hM, he⟩
    · rintro ⟨N, hL, hM, he⟩
      exact (StageSystem.PairCategory.mkHom_eq_mkHom_iff' f g).mpr
        ⟨N.val, hL, hM, he⟩

/-- Stagewise object shift, with the coefficient field unchanged.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def shiftPair (n : ℤ) (A : Pair D l hl Ω Y) : Pair D l hl Ω Y :=
  ⟨A.stage, (shiftFunctor (Stage D l hl Ω Y A.stage) n).obj A.obj⟩

/-- The shifted representative uses the prescribed scalar-extension shift comparison.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def shiftRepresentative (n : ℤ) (A B : Pair D l hl Ω Y)
    (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) :
    StageHom (shiftPair n A) (shiftPair n B) ⟨L, hA, hB⟩ :=
  ((stageTransition D l hl Ω Y A.stage L hA).commShiftIso n).hom.app A.obj ≫
    (shiftFunctor (Stage D l hl Ω Y L) n).map f ≫
    ((stageTransition D l hl Ω Y B.stage L hB).commShiftIso n).inv.app B.obj

/-- The induced shift is specified on every object, representative and stage inclusion.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: shift each finite representative using shiftRepresentative. Exact scalar
extension and associator compatibility with shifts make this independent of stage.
The finite-stage shift units and addition isomorphisms descend componentwise; equality
and coherence may be checked after moving the finite diagrams to a common field.
The inclusion comparisons are identities on the displayed shifted pairs. Thus these
formulas determine the functors and their coherent comparisons on the generators.
Every object is literally in its own stage. The identity inclusion comparisons and
their coherence equations fix the zero and addition comparisons there, hence everywhere.
This proves uniqueness of the full shift structure, not just its object and arrow maps. -/
theorem shift_existsUnique :
    ∃! s : HasShift (Pair D l hl Ω Y) ℤ,
      (fun [shiftInst : HasShift (Pair D l hl Ω Y) ℤ] ↦
        (∀ n : ℤ, (shiftFunctor (Pair D l hl Ω Y) n).Additive) ∧
        (∀ (n : ℤ) (A : Pair D l hl Ω Y),
          (shiftFunctor (Pair D l hl Ω Y) n).obj A = shiftPair n A) ∧
        (∀ (n : ℤ) (A B : Pair D l hl Ω Y) (L : Index l Ω)
          (hA : A.stage ≤ L) (hB : B.stage ≤ L) (f : StageHom A B ⟨L, hA, hB⟩),
          HEq ((shiftFunctor (Pair D l hl Ω Y) n).map (ofHom A B L hA hB f))
            (ofHom (shiftPair n A) (shiftPair n B) L hA hB
              (shiftRepresentative n A B L hA hB f))) ∧
        ∃ c : ∀ E : Index l Ω, (inclusion E : Stage D l hl Ω Y E ⥤ _).CommShift ℤ,
          (fun [commInst : ∀ E : Index l Ω,
              (inclusion E : Stage D l hl Ω Y E ⥤ _).CommShift ℤ] ↦
            ∀ (n : ℤ) (E : Index l Ω) (K : Stage D l hl Ω Y E),
              HEq (((inclusion E : Stage D l hl Ω Y E ⥤ _).commShiftIso n).hom.app K)
                (𝟙 ((inclusion E : Stage D l hl Ω Y E ⥤ _).obj
                  ((shiftFunctor (Stage D l hl Ω Y E) n).obj K)))) (commInst := c))
        (shiftInst := s) := by
  sorry

/-- The stagewise shift with the representative formula of shift_existsUnique.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance hasShift : HasShift (Pair D l hl Ω Y) ℤ := shift_existsUnique.exists.choose

/-- Each induced integer shift is additive.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance shiftAdditive (n : ℤ) :
    (shiftFunctor (Pair D l hl Ω Y) n).Additive := shift_existsUnique.exists.choose_spec.1 n

/-- The normalized exact-stage shift comparison, fixed to identity on shifted pairs.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance inclusionCommShift (E : Index l Ω) :
    (inclusion E : Stage D l hl Ω Y E ⥤ _).CommShift ℤ :=
  shift_existsUnique.exists.choose_spec.2.2.2.choose E

/-- A stage zero object remains zero after forming directed Hom colimits.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: take the zero object at the bottom coefficient field. Every transition is exact
and therefore preserves zero. At every common field its Hom groups to and from any
object vanish. Their directed colimits vanish, giving the zero-object universal property. -/
theorem zero_exists : HasZeroObject (Pair D l hl Ω Y) := by
  let E := Padic.finiteCoefficientBase l Ω
  let X : Pair D l hl Ω Y := (inclusion E).obj (0 : Stage D l hl Ω Y E)
  refine ⟨⟨X, ?_⟩⟩
  rw [IsZero.iff_id_eq_zero, StageSystem.PairCategory.id_eq_mkHom X le_rfl,
    ← mkHom_zero (A := X) (B := X) le_rfl le_rfl]
  have hz : IsZero (X.toStage le_rfl) :=
    Functor.map_isZero (stageTransition D l hl Ω Y E E le_rfl) (isZero_zero _)
  exact congrArg (StageSystem.PairCategory.mkHom E le_rfl le_rfl) (hz.eq_of_src _ _)

attribute [instance] zero_exists

/-- The canonical coefficient-stage identifications commute with shifts.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: on finite representatives this is scalar-extension shift compatibility and
sfRationalScalar_coherence. The normalized inclusion comparisons are
identities on shifted pairs. The cocycle equation identifies both composites. -/
@[instance]
theorem transitionIso_commShift
    {D : WeilConjectures.FiniteFieldDatum.{d}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) :
    NatTrans.CommShift ((SfAlgebraicallyClosedCoefficients.stageSystem D l hl Ω Y).transIso h).hom ℤ
        := by
  sorry

/-- The recorded common-stage distinguished-triangle criterion.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev Distinguished (T : Triangle (Pair D l hl Ω Y)) : Prop :=
  (stageSystem D l hl Ω Y).CommonStageDistinguished T

/-- The unique pretriangulation supplied by the common-stage Verdier theorem.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance pretriangulated : Pretriangulated (Pair D l hl Ω Y) :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem D l hl Ω Y)).exists.choose

/-- The Verdier axiom for the specified common-stage triangles.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance isTriangulated : IsTriangulated (Pair D l hl Ω Y) :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem D l hl Ω Y)).exists.choose_spec.2.1

/-- Each actual rational finite-stage inclusion is exact.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance inclusion_exact (E : Index l Ω) :
    (inclusion E : Stage D l hl Ω Y E ⥤ _).IsTriangulated :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem D l hl Ω Y)).exists.choose_spec.2.2 E

/-- The triangle criterion, exposing the finite-field-of-definition clause.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: this is the distinguished-set clause of commonStage_verdier_existsUnique
for the actual scalar-extension stage system. -/
theorem distinguished_iff
    {D : WeilConjectures.FiniteFieldDatum.{d}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (T : Triangle (SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y)) :
    T ∈ distTriang (SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) ↔
        SfAlgebraicallyClosedCoefficients.Distinguished T := by
  exact (StageSystem.commonStage_verdier_existsUnique
    (stageSystem D l hl Ω Y)).exists.choose_spec.1 T

/-- A specified cone over L gives exactly the recorded common-stage cone, including
its second and connecting arrows and the literal cone pair (L,C).
Source: blueprint order 1462, common-stage cone clause
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: apply the exact stage inclusion at L to the displayed distinguished triangle.
The canonical isoToStage identifications identify its first two objects with A and B.
Conjugate the arrows by these identifications and the specified inclusion shift
comparison. This is precisely commonStageCone, whose first arrow is the represented u,
second arrow is the represented i with the normalized identity extension, and third
arrow is p followed by the inverse scalar shift comparison. Its third object is the
literal pair (L,C). Isomorphism closure preserves distinguishedness. -/
theorem commonStage_cone (A B : Pair D l hl Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (C : Stage D l hl Ω Y L) (u : A.toStage hA ⟶ B.toStage hB)
    (i : B.toStage hB ⟶ C) (p : C ⟶ (A.toStage hA)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u i p ∈ distTriang (Stage D l hl Ω Y L)) :
    (stageSystem D l hl Ω Y).commonStageCone A B L hA hB C u i p ∈
      distTriang (Pair D l hl Ω Y) := by
  apply (distinguished_iff _).2
  refine ⟨L, Triangle.mk u i p, hT, ⟨?_⟩⟩
  refine Triangle.isoMk _ _ ((stageSystem D l hl Ω Y).isoToStage A hA)
    ((stageSystem D l hl Ω Y).isoToStage B hB) (Iso.refl _) ?_ ?_ ?_
  · change StageSystem.PairCategory.mkHom L hA hB u ≫
        ((stageSystem D l hl Ω Y).isoToStage B hB).hom = _
    rw [StageSystem.mkHom_eq_isoToStage hA hB u]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  · exact Category.comp_id _
  · change (((stageSystem D l hl Ω Y).ι L).map p ≫
        (((stageSystem D l hl Ω Y).ι L).commShiftIso (1 : ℤ)).hom.app _ ≫
        (shiftFunctor (Pair D l hl Ω Y) (1 : ℤ)).map
          ((stageSystem D l hl Ω Y).isoToStage A hA).inv) ≫
        (shiftFunctor (Pair D l hl Ω Y) (1 : ℤ)).map
          ((stageSystem D l hl Ω Y).isoToStage A hA).hom = _
    rw [Category.assoc, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id]
    change _ = 𝟙 _ ≫
      (((stageSystem D l hl Ω Y).ι L).map p ≫
        (((stageSystem D l hl Ω Y).ι L).commShiftIso (1 : ℤ)).hom.app _)
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    exact congrArg (fun f ↦ ((stageSystem D l hl Ω Y).ι L).map p ≫ f)
      (Category.comp_id _)

end SfAlgebraicallyClosedCoefficients

/-- The algebraically closed coefficient category is the pair category itself.
No Karoubi envelope occurs: its objects are finite-field pairs and its Hom groups are
canonically the displayed directed colimits. The companion declarations specify shift,
composition, common-stage distinguished triangles and the Verdier axioms.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev sfAlgebraicallyClosedConstructibleCategory
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u}) :=
  SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y

end WeilConjectures
