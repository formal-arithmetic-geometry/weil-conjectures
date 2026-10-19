/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.CategoryTheory.PerfectConstantLocalChainRepresentative

import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.Data.Int.Interval

/-! # Local algebraicity of bounded constant chain maps

Source: Stacks Project, Cohomology on Sites, Tag 09BE, chain-map step
(blueprint: lem-sfb-bounded-constant-chain-map-local).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem covering_refinement {C : Type u} [Category.{v} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings) {U : C} {S : Sieve U}
    (hS : S ∈ J.toGrothendieck U) : ∃ T ∈ J U, T ≤ S.arrows := by
  classical
  have : J.HasIsos := hJ.1
  induction hS with
  | of X R hR => exact ⟨R, hR, Sieve.le_generate R⟩
  | top X =>
    exact ⟨Presieve.singleton (𝟙 X), J.mem_coverings_of_isIso (𝟙 X), by simp⟩
  | pullback X S hS Y f ih =>
    obtain ⟨R, hR, hle⟩ := ih
    let I := Σ Z : C, {a : Z ⟶ X // R a}
    let V : I → C := fun i ↦ i.1
    let a : ∀ i : I, V i ⟶ X := fun i ↦ i.2.1
    have heq : Presieve.ofArrows V a = R := by
      funext Z b
      apply propext
      constructor
      · rintro ⟨i⟩
        exact i.2.2
      · intro hb
        exact Presieve.ofArrows.mk (Y := V) (f := a) ⟨Z, b, hb⟩
    obtain ⟨P, p, q, hpq, hp⟩ := hJ.2.2 I X V a (heq ▸ hR) Y f
    refine ⟨Presieve.ofArrows P p, hp, ?_⟩
    rintro Z b ⟨i⟩
    change S (p i ≫ f)
    rw [(hpq i).w]
    exact S.downward_closed (hle _ _ i.2.2) (q i)
  | transitive X S T hS hT ihS ihT =>
    obtain ⟨R, hR, hle⟩ := ihS
    have hh : ∀ (Y : C) (f : Y ⟶ X) (_ : R f),
        ∃ Q ∈ J Y, Q ≤ (T.pullback f).arrows := by
      intro Y f hf
      exact ihT (hle _ _ hf)
    choose Q hQ hQT using hh
    refine ⟨R.bind (fun {Y f} hf ↦ Q Y f hf),
      hJ.2.1 X R (fun {Y} f hf ↦ Q Y f hf) hR hQ, ?_⟩
    intro Z f hf
    obtain ⟨Y, g, a, ha, hg, rfl⟩ := hf
    exact hQT Y a ha _ _ hg

section Helpers

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type (max u v)) [CommRing Λ]

/-- The underlying additive sheafification unit of a constant module. -/
private def siteConstantModuleUnit (M : ModuleCat.{max u v} Λ) :
    (Functor.const Cᵒᵖ).obj ((forget₂ (ModuleCat Λ) AddCommGrpCat).obj M) ⟶
      ((siteConstantModuleFunctorGeneral J Λ).obj M).val.presheaf :=
  toSheafify J ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf

private instance (M : ModuleCat.{max u v} Λ) :
    Presheaf.IsLocallyInjective J (siteConstantModuleUnit J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf))

private instance (M : ModuleCat.{max u v} Λ) :
    Presheaf.IsLocallySurjective J (siteConstantModuleUnit J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J
    (toSheafify J ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf))

private lemma siteConstantModuleUnit_naturality {M N : ModuleCat.{max u v} Λ} (f : M ⟶ N)
    (U : Cᵒᵖ) (x : M) :
    ((siteConstantModuleFunctorGeneral J Λ).map f).val.app U
      ((siteConstantModuleUnit J Λ M).app U x) =
        (siteConstantModuleUnit J Λ N).app U (f x) := by
  have h := toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map
    ((siteConstantModulePresheafGeneral (C := C) Λ).map f))
  exact (ConcreteCategory.congr_hom (congr_app h U) x).symm

/-- The constant-module sheaf, viewed as a presheaf of modules over the original ring. -/
private def siteConstantModuleSections (M : ModuleCat.{max u v} Λ) :
    Cᵒᵖ ⥤ ModuleCat.{max u v} Λ where
  obj U := ((PresheafOfModules.restrictScalars
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).obj
      ((siteConstantModuleFunctorGeneral J Λ).obj M).val).obj U
  map f := ((PresheafOfModules.restrictScalars
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).obj
      ((siteConstantModuleFunctorGeneral J Λ).obj M).val).map f
  map_id U := by ext x; simp; rfl
  map_comp f g := by ext x; simp; rfl

/-- The linear form of the constant-module sheafification unit. -/
private def siteConstantModuleUnitSections (M : ModuleCat.{max u v} Λ) :
    (Functor.const Cᵒᵖ).obj M ⟶ siteConstantModuleSections J Λ M where
  app U := (PresheafOfModules.toSheafify
    (M₀ := (siteConstantModulePresheafGeneral (C := C) Λ).obj M)
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))
    (siteConstantModuleUnit J Λ M)).app U
  naturality {U V} f := by
    ext x
    exact NatTrans.naturality_apply (siteConstantModuleUnit J Λ M) f x

variable (M N : ModuleCat.{max u v} Λ)

/-- A map from a constant module sheaf is determined on the constant sections. -/
private theorem siteConstantModule_over_hom_ext (U : C)
    (a b : ((siteConstantModuleFunctorGeneral J Λ).obj M).over U ⟶
      ((siteConstantModuleFunctorGeneral J Λ).obj N).over U)
    (h : ∀ x : M,
      a.val.app (op (Over.mk (𝟙 U))) ((siteConstantModuleUnit J Λ M).app (op U) x) =
      b.val.app (op (Over.mk (𝟙 U))) ((siteConstantModuleUnit J Λ M).app (op U) x)) : a = b := by
  let FM := (siteConstantModuleFunctorGeneral J Λ).obj M
  let FN := (siteConstantModuleFunctorGeneral J Λ).obj N
  let η := siteConstantModuleUnit J Λ M
  have hlocal (V : Over U) (x : M) :
      a.val.app (op V) (η.app (op V.left) x) =
        b.val.app (op V) (η.app (op V.left) x) := by
    have ha := PresheafOfModules.naturality_apply a.val
      (Over.homMk V.hom : V ⟶ Over.mk (𝟙 U)).op (η.app (op U) x)
    have hb := PresheafOfModules.naturality_apply b.val
      (Over.homMk V.hom : V ⟶ Over.mk (𝟙 U)).op (η.app (op U) x)
    have hn := NatTrans.naturality_apply η V.hom.op x
    change η.app (op V.left) x = FM.val.map V.hom.op (η.app (op U) x) at hn
    change a.val.app (op V) (FM.val.map V.hom.op (η.app (op U) x)) =
      FN.val.map V.hom.op (a.val.app (op (Over.mk (𝟙 U))) (η.app (op U) x)) at ha
    change b.val.app (op V) (FM.val.map V.hom.op (η.app (op U) x)) =
      FN.val.map V.hom.op (b.val.app (op (Over.mk (𝟙 U))) (η.app (op U) x)) at hb
    rw [hn, ha, hb, h x]
  ext V s
  apply FN.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J η s)
  intro W f hf
  obtain ⟨x, hx⟩ := hf
  let V' : Over U := Over.mk (f ≫ V.unop.hom)
  have ha := PresheafOfModules.naturality_apply a.val
    (Over.homMk f : V' ⟶ V.unop).op s
  have hb := PresheafOfModules.naturality_apply b.val
    (Over.homMk f : V' ⟶ V.unop).op s
  change a.val.app (op V') (FM.val.map f.op s) = FN.val.map f.op (a.val.app V s) at ha
  change b.val.app (op V') (FM.val.map f.op s) = FN.val.map f.op (b.val.app V s) at hb
  change η.app (op W) x = FM.val.map f.op s at hx
  change FN.val.map f.op (a.val.app V s) = FN.val.map f.op (b.val.app V s)
  rw [← ha, ← hb, ← hx]
  exact hlocal V' x

private theorem constant_unit_injective (V : C) (hV : (⊥ : Sieve V) ∉ J V) :
    Function.Injective ((siteConstantModuleUnit J Λ N).app (op V)) := by
  exact J.toSheafify_const_app_injective
    ((forget₂ (ModuleCat Λ) AddCommGrpCat).obj N) hV

private theorem component_local [Module.Finite Λ M] (U : C)
    (a : ((siteConstantModuleFunctorGeneral J Λ).obj M).over U ⟶
      ((siteConstantModuleFunctorGeneral J Λ).obj N).over U) :
    ∃ S ∈ J U, ∀ (V : C) (g : V ⟶ U), S g →
      (⊥ : Sieve V) ∉ J V → ∃ b : M ⟶ N,
        (SheafOfModules.overMap _ g).map a =
          ((siteConstantModuleFunctorGeneral J Λ).map b).over V := by
  classical
  let FM := (siteConstantModuleFunctorGeneral J Λ).obj M
  let FN := (siteConstantModuleFunctorGeneral J Λ).obj N
  let ηM := siteConstantModuleUnit J Λ M
  let ηN := siteConstantModuleUnit J Λ N
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := Λ) (M := M)
  obtain ⟨S, hS, h⟩ := J.exists_mem_forall_exists_toSheafify_const_app_eq
    ((forget₂ (ModuleCat Λ) AddCommGrpCat).obj N) (U := U)
    (fun m : (t : Set M) ↦ a.val.app (op (Over.mk (𝟙 U))) (ηM.app (op U) m.1))
  refine ⟨S, hS, fun V g hg hV ↦ ?_⟩
  choose n hn using h g hg
  have hn' (m : (t : Set M)) :
      ηN.app (op V) (n m) = a.val.app (op (Over.mk g)) (ηM.app (op V) m.1) := by
    change (toSheafify J ((Functor.const Cᵒᵖ).obj
      ((forget₂ (ModuleCat Λ) AddCommGrpCat).obj N))).app (op V) (n m) = _
    erw [hn]
    have ha := PresheafOfModules.naturality_apply a.val
      (Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 U)).op (ηM.app (op U) m.1)
    have hm := NatTrans.naturality_apply ηM g.op m.1
    change ηM.app (op V) m.1 = FM.val.map g.op (ηM.app (op U) m.1) at hm
    change a.val.app (op (Over.mk g)) (FM.val.map g.op (ηM.app (op U) m.1)) =
      FN.val.map g.op (a.val.app (op (Over.mk (𝟙 U))) (ηM.app (op U) m.1)) at ha
    exact ha.symm.trans (congrArg (a.val.app (op (Over.mk g))) hm.symm)
  let ιN := ((siteConstantModuleUnitSections J Λ N).app (op V)).hom
  let L := (((siteConstantModuleUnitSections J Λ M).app (op V)) ≫
    (ModuleCat.restrictScalars
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app (op V)).hom).map
        (a.val.app (op (Over.mk g)))).hom
  have hinj : Function.Injective ιN := constant_unit_injective J Λ N V hV
  have hle : LinearMap.range L ≤ LinearMap.range ιN := by
    rw [LinearMap.range_eq_map, ← ht, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨n ⟨m, hm⟩, ?_⟩
    exact hn' ⟨m, hm⟩
  let e := LinearEquiv.ofInjective ιN hinj
  let b : M ⟶ N := ModuleCat.ofHom (e.symm.toLinearMap ∘ₗ
    L.codRestrict _ fun m ↦ hle (LinearMap.mem_range_self L m))
  refine ⟨b, siteConstantModule_over_hom_ext J Λ M N V _ _ (fun m ↦ ?_)⟩
  have hb : L m = ηN.app (op V) (b m) :=
    (congrArg Subtype.val
      (e.apply_symm_apply ⟨L m, hle (LinearMap.mem_range_self L m)⟩)).symm
  have hbn := siteConstantModuleUnit_naturality J Λ b (op V) m
  change a.val.app (op (Over.mk g)) (ηM.app (op V) m) =
    ηN.app (op V) (b m) at hb
  change a.val.app (op (Over.mk (𝟙 V ≫ g))) (ηM.app (op V) m) =
    ((siteConstantModuleFunctorGeneral J Λ).map b).val.app (op V)
      (ηM.app (op V) m)
  rw [Category.id_comp]
  exact hb.trans hbn.symm

private theorem constant_over_map_injective (V : C) (hV : (⊥ : Sieve V) ∉ J V)
    (b c : M ⟶ N)
    (h : ((siteConstantModuleFunctorGeneral J Λ).map b).over V =
      ((siteConstantModuleFunctorGeneral J Λ).map c).over V) : b = c := by
  ext x
  apply constant_unit_injective J Λ N V hV
  have hh := congrArg (fun t ↦ t.val.app (op (Over.mk (𝟙 V)))
    ((siteConstantModuleUnit J Λ M).app (op V) x)) h
  exact (siteConstantModuleUnit_naturality J Λ b (op V) x).symm.trans
    (hh.trans (siteConstantModuleUnit_naturality J Λ c (op V) x))

private theorem empty_over_hom_eq (V : C) (hV : (⊥ : Sieve V) ∈ J V)
    (a b : ((siteConstantModuleFunctorGeneral J Λ).obj M).over V ⟶
      ((siteConstantModuleFunctorGeneral J Λ).obj N).over V) : a = b := by
  ext W x
  apply ((siteConstantModuleFunctorGeneral J Λ).obj N).isSheaf.isSeparated
    _ (⊥ : Sieve W.unop.left) (by simpa using J.pullback_stable W.unop.hom hV)
  intro T k hk
  exact False.elim hk

private theorem further_constant_map (U V : C) (g : V ⟶ U) (b : M ⟶ N) :
    (SheafOfModules.overMap
      ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)) g).map
        (((siteConstantModuleFunctorGeneral J Λ).map b).over U) =
      ((siteConstantModuleFunctorGeneral J Λ).map b).over V := by
  ext W x
  rfl

end Helpers

set_option maxHeartbeats 400000 in
-- Comparing the iterated slice restrictions consumes the default heartbeat allowance.
/-- A map of constant complexes with bounded finite source is, after refinement,
induced by an algebraic chain map.
Source: Stacks Project, Cohomology on Sites, Tag 09BE, using Modules on Sites,
Tag 093S(3) (blueprint: lem-sfb-bounded-constant-chain-map-local).

Proof: For each component, lift the images of finitely many source generators through
the constant-section unit on a common covering. On a nonempty-covered object this unit
is injective. The linear range of the component map on constant sections lies in the
unit's range, because it contains the generator images. Its inverse onto that range
constructs the algebraic linear map. Naturality, local surjectivity of the unit, and
separatedness show equality of the resulting morphisms throughout the slice.
There are finitely many nonzero source terms, so intersect their covering sieves and
refine to a covering presieve using the identity, pullback, and bind covering axioms.
On a covering object not covered by the empty sieve, the constant-section unit is
injective, since equality in sheafification is local and a covering sieve there is
nonempty. Apply this injectivity to the values of the chain equations, obtaining
algebraic chain equations, including at the support boundaries. Outside the source
support use zero maps. On an empty-covered object every module sheaf restricts to
zero, so take the zero chain map. The component equalities on the slice follow
from compatibility of constant restriction with the sheafification units. -/
theorem exists_bounded_constant_chain_map_local
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (R : Type (max u v)) [CommRing R]
    (F G : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hF : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q))
    [∀ q : ℤ, Module.Finite R (F.X q)] (U : C)
    (a : (moduleCochainRestriction
        ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) U).obj
        ((constantModuleCochainFunctor J.toGrothendieck R).obj F) ⟶
      (moduleCochainRestriction
        ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) U).obj
        ((constantModuleCochainFunctor J.toGrothendieck R).obj G)) :
    ∃ S : Presieve U, S ∈ J U ∧
      ∀ (V : C) (g : V ⟶ U), S g → ∃ b : F ⟶ G, ∀ q : ℤ,
        (SheafOfModules.overMap
          ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) g).map
          (a.f q) =
        (SheafOfModules.overFunctor
          ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) V).map
          ((siteConstantModuleFunctorGeneral J.toGrothendieck R).map (b.f q)) := by
  classical
  let K := J.toGrothendieck
  let S := (constantSheaf K RingCat.{max u v}).obj (RingCat.of R)
  let E := siteConstantModuleFunctorGeneral K R
  have : E.Additive := (siteConstantModuleFunctorGeneral_exact K R).1
  have (V : C) : (SheafOfModules.overFunctor S V).Additive :=
    (ringedOverFunctor_exactGeneral S V).1
  obtain ⟨lo, hi, hlohi, hzero⟩ := hF
  let I := {q : ℤ // q ∈ Finset.Icc lo hi}
  have hcomponents (q : I) := component_local K R (F.X q.1) (G.X q.1) U (a.f q.1)
  choose T hT hc using hcomponents
  obtain ⟨W, hW, hWT⟩ := covering_refinement J hJ (K.iInf_mem T hT)
  refine ⟨W, hW, fun V g hg ↦ ?_⟩
  by_cases hV : (⊥ : Sieve V) ∈ K V
  · refine ⟨0, fun q ↦ ?_⟩
    exact empty_over_hom_eq K R (F.X q) (G.X q) V hV _ _
  · have hq (q : I) : ∃ b : F.X q.1 ⟶ G.X q.1,
        (SheafOfModules.overMap S g).map (a.f q.1) = (SheafOfModules.overFunctor S V).map
          (E.map b) := by
      exact hc q V g ((iInf_le T q) _ (hWT V g hg)) hV
    choose b hb using hq
    let c (q : ℤ) : F.X q ⟶ G.X q := if h : q ∈ Finset.Icc lo hi then b ⟨q, h⟩ else 0
    have heq (q : ℤ) : (SheafOfModules.overMap S g).map (a.f q) =
        (SheafOfModules.overFunctor S V).map (E.map (c q)) := by
      by_cases h : q ∈ Finset.Icc lo hi
      · simpa only [c, dif_pos h] using hb ⟨q, h⟩
      · have hz : IsZero (F.X q) := hzero q (by
          simp only [Finset.mem_Icc, not_and_or, not_le] at h
          exact h)
        exact ((SheafOfModules.overFunctor S V).map_isZero (E.map_isZero hz)).eq_of_src _ _
    have hcomm (i j : ℤ) : c i ≫ G.d i j = F.d i j ≫ c j := by
      apply constant_over_map_injective K R (F.X i) (G.X j) V hV
      simp only [Functor.map_comp]
      have hdG := further_constant_map K R (G.X i) (G.X j) U V g (G.d i j)
      have hdF := further_constant_map K R (F.X i) (F.X j) U V g (F.d i j)
      have ha := congrArg ((SheafOfModules.overMap S g).map) (a.comm i j)
      rw [Functor.map_comp, Functor.map_comp] at ha
      exact (congrArg₂ (fun x y ↦ x ≫ y) (heq i).symm hdG.symm).trans
        (ha.trans (congrArg₂ (fun x y ↦ x ≫ y) hdF (heq j)))
    exact ⟨{ f := c, comm' := fun i j _ ↦ hcomm i j }, heq⟩

end CategoryTheory
