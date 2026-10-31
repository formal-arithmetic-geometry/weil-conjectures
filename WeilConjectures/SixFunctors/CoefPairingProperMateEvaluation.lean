/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingSystemAdjunctionMap
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.SixFunctors.CoefPairingNativeOperations
import WeilConjectures.AlgebraicGeometry.CompactSupportNativeSystemEvaluation
import WeilConjectures.AlgebraicGeometry.CoefficientNormalizedReductionModels
import WeilConjectures.SixFunctors.CoefPairingFiniteFrameDescent
import WeilConjectures.SixFunctors.CoefPairingSectionsLeftEvaluation

/-! # Finite evaluation of the supplied proper mate

Source: prop-coef-integral-dualizing, second proof paragraph;
Stacks 07A6 and 0B56. No projection formula is asserted here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.CoefPairingFrame

private theorem leftMate_formula
    {C B : Type*} [Category C] [Category B]
    (TC : C × C ⥤ C) (TB : B × B ⥤ B) (L : C ⥤ B) (P : B ⥤ C)
    (a : L ⊣ P) (μ : TC ⋙ L ≅ L.prod L ⋙ TB) (H : C) (M : B) :
    leftMate TC TB L P a μ H M =
      a.homEquiv _ _ (μ.hom.app (H, P.obj M) ≫
        TB.map (Prod.mkHom (𝟙 (L.obj H)) (a.counit.app M))) := by
  simp [leftMate, Adjunction.rightAdjointProjectionMap, Functor.curryObj]

private theorem evaluation_transpose
    {C B c b : Type*} [Category C] [Category B] [Category c] [Category b]
    {L : C ⥤ B} {P : B ⥤ C} {l : c ⥤ b} {p : b ⥤ c}
    (a : L ⊣ P) (d : l ⊣ p) (E : C ⥤ c) (V : B ⥤ b)
    (e : L ⋙ V ≅ E ⋙ l) (r : P ⋙ E ≅ V ⋙ p)
    (hu : ∀ H, E.map (a.unit.app H) ≫ r.hom.app (L.obj H) ≫
      p.map (e.hom.app H) = d.unit.app (E.obj H))
    {H : C} {M : B} (f : L.obj H ⟶ M) :
    E.map (a.homEquiv _ _ f) ≫ r.hom.app M =
      d.homEquiv _ _ (e.inv.app H ≫ V.map f) := by
  rw [a.homEquiv_unit, d.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hr := r.hom.naturality f
  dsimp only [Functor.comp_map] at hr
  rw [hr]
  have h : E.map (a.unit.app H) ≫ r.hom.app (L.obj H) =
      d.unit.app (E.obj H) ≫ p.map (e.inv.app H) := by
    have h := congrArg (fun z ↦ z ≫ p.map (e.inv.app H)) (hu H)
    simp only [Category.assoc, ← p.map_comp, e.hom_inv_id_app] at h
    simpa using h
  rw [← Category.assoc, h, Category.assoc]

private theorem leftMate_evaluation
    {C B c b : Type*} [Category C] [Category B] [Category c] [Category b]
    (TC : C × C ⥤ C) (TB : B × B ⥤ B)
    (tc : c × c ⥤ c) (tb : b × b ⥤ b)
    (L : C ⥤ B) (P : B ⥤ C) (l : c ⥤ b) (p : b ⥤ c)
    (a : L ⊣ P) (d : l ⊣ p)
    (μ : TC ⋙ L ≅ L.prod L ⋙ TB) (ν : tc ⋙ l ≅ l.prod l ⋙ tb)
    (E : C ⥤ c) (V : B ⥤ b)
    (e : L ⋙ V ≅ E ⋙ l) (r : P ⋙ E ≅ V ⋙ p)
    (σ : TC ⋙ E ≅ E.prod E ⋙ tc) (τ : TB ⋙ V ≅ V.prod V ⋙ tb)
    (hu : ∀ H, E.map (a.unit.app H) ≫ r.hom.app (L.obj H) ≫
      p.map (e.hom.app H) = d.unit.app (E.obj H))
    (hc : ∀ M, e.hom.app (P.obj M) ≫ l.map (r.hom.app M) ≫
      d.counit.app (V.obj M) = V.map (a.counit.app M))
    (hμ : ∀ H K, V.map (μ.hom.app (H, K)) ≫ τ.hom.app (L.obj H, L.obj K) ≫
      tb.map (Prod.mkHom (e.hom.app H) (e.hom.app K)) =
      e.hom.app (TC.obj (H, K)) ≫ l.map (σ.hom.app (H, K)) ≫
        ν.hom.app (E.obj H, E.obj K))
    (H : C) (M : B) :
    E.map (leftMate TC TB L P a μ H M) ≫ r.hom.app (TB.obj (L.obj H, M)) ≫
        p.map (τ.hom.app (L.obj H, M) ≫
          tb.map (Prod.mkHom (e.hom.app H) (𝟙 (V.obj M)))) =
      (σ.hom.app (H, P.obj M) ≫
        tc.map (Prod.mkHom (𝟙 (E.obj H)) (r.hom.app M))) ≫
          leftMate tc tb l p d ν (E.obj H) (V.obj M) := by
  rw [leftMate_formula, leftMate_formula]
  dsimp only [Functor.id_obj]
  have he := evaluation_transpose a d E V e r hu
    (H := TC.obj (H, P.obj M)) (M := TB.obj (L.obj H, M))
    (μ.hom.app (H, P.obj M) ≫
      TB.map (Prod.mkHom (𝟙 (L.obj H)) (a.counit.app M)))
  rw [← Category.assoc, he]
  rw [← d.homEquiv_naturality_right]
  erw [← d.homEquiv_naturality_left]
  congr 1
  simp only [Functor.map_comp, Category.assoc]
  have hτ := τ.hom.naturality
    (Prod.mkHom (𝟙 (L.obj H)) (a.counit.app M))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.map_id] at hτ
  rw [reassoc_of% hτ]
  have h₁ : tb.map (Prod.mkHom (𝟙 (V.obj (L.obj H))) (V.map (a.counit.app M))) ≫
      tb.map (Prod.mkHom (e.hom.app H) (𝟙 (V.obj M))) =
      tb.map (Prod.mkHom (e.hom.app H) (e.hom.app (P.obj M))) ≫
        tb.map (Prod.mkHom (𝟙 (l.obj (E.obj H)))
          (l.map (r.hom.app M))) ≫
        tb.map (Prod.mkHom (𝟙 (l.obj (E.obj H))) (d.counit.app (V.obj M))) := by
    simp only [← Functor.map_comp]
    congr 1
    ext <;> simp [hc]
  simp only [V.map_id]
  rw [h₁]
  rw [reassoc_of% (hμ H (P.obj M))]
  simp only [Iso.inv_hom_id_app_assoc]
  have hν := ν.hom.naturality
    (Prod.mkHom (𝟙 (E.obj H)) (r.hom.app M))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.map_id] at hν
  simp only [Functor.map_id] at hν
  rw [← reassoc_of% hν]

private def leftMate_input_iso
    {C B : Type*} [Category C] [Category B]
    (TC : C × C ⥤ C) (TB : B × B ⥤ B) (L : C ⥤ B) (P : B ⥤ C)
    (a : L ⊣ P) (μ : TC ⋙ L ≅ L.prod L ⋙ TB)
    {H H' : C} {M M' : B} (h : H ≅ H') (m : M ≅ M') :
    Arrow.mk (leftMate TC TB L P a μ H M) ≅
      Arrow.mk (leftMate TC TB L P a μ H' M') := by
  let flip := (Functor.flipping (C := C) (D := C) (E := B)).functor
  let w := a.rightAdjointProjectionMap
    (T_C := (Functor.curryObj TB).flip) (T_D := (Functor.curryObj TC).flip)
    (flip.map (Functor.curry.map μ.hom) ≫
      (flip.mapIso (Functor.curryObjProdComp L L TB)).hom)
  refine Arrow.isoMk' _ _ (TC.mapIso (Iso.prod h (P.mapIso m)))
    (P.mapIso (TB.mapIso (Iso.prod (L.mapIso h) m))) ?_
  have hn := (Functor.uncurry.map w).naturality (Prod.mkHom m.hom h.hom)
  simpa [Functor.uncurry_obj_map, Functor.curryObj, leftMate,
    ← Functor.map_comp, w, flip] using hn

private def leftMate_evaluation_iso
    {C B c b : Type*} [Category C] [Category B] [Category c] [Category b]
    (TC : C × C ⥤ C) (TB : B × B ⥤ B)
    (tc : c × c ⥤ c) (tb : b × b ⥤ b)
    (L : C ⥤ B) (P : B ⥤ C) (l : c ⥤ b) (p : b ⥤ c)
    (a : L ⊣ P) (d : l ⊣ p)
    (μ : TC ⋙ L ≅ L.prod L ⋙ TB) (ν : tc ⋙ l ≅ l.prod l ⋙ tb)
    (E : C ⥤ c) (V : B ⥤ b)
    (e : L ⋙ V ≅ E ⋙ l) (r : P ⋙ E ≅ V ⋙ p)
    (σ : TC ⋙ E ≅ E.prod E ⋙ tc) (τ : TB ⋙ V ≅ V.prod V ⋙ tb)
    (hu : ∀ H, E.map (a.unit.app H) ≫ r.hom.app (L.obj H) ≫
      p.map (e.hom.app H) = d.unit.app (E.obj H))
    (hc : ∀ M, e.hom.app (P.obj M) ≫ l.map (r.hom.app M) ≫
      d.counit.app (V.obj M) = V.map (a.counit.app M))
    (hμ : ∀ H K, V.map (μ.hom.app (H, K)) ≫ τ.hom.app (L.obj H, L.obj K) ≫
      tb.map (Prod.mkHom (e.hom.app H) (e.hom.app K)) =
      e.hom.app (TC.obj (H, K)) ≫ l.map (σ.hom.app (H, K)) ≫
        ν.hom.app (E.obj H, E.obj K))
    (H : C) (M : B) :
    Arrow.mk (E.map (leftMate TC TB L P a μ H M)) ≅
      Arrow.mk (leftMate tc tb l p d ν (E.obj H) (V.obj M)) := by
  refine Arrow.isoMk' _ _
    (σ.app (H, P.obj M) ≪≫ tc.mapIso (Iso.prod (Iso.refl _) (r.app M)))
    (r.app (TB.obj (L.obj H, M)) ≪≫
      p.mapIso (τ.app (L.obj H, M) ≪≫
        tb.mapIso (Iso.prod (e.app H) (Iso.refl _)))) ?_
  exact (leftMate_evaluation TC TB tc tb L P l p a d μ ν E V e r σ τ hu hc hμ H M).symm

end CategoryTheory.CoefPairingFrame

namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem pairing_open_evaluation
    {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    (S : CoefficientDerivedSystemCalculus l E X) (G : CoefPairingSystem l E c S)
    (q : ℕ) :
    Nonempty (G.openModules.mapDerivedCategory ⋙
      coefficientSequenceDerivedEvaluation l E c.Z q ≅
      coefficientSequenceDerivedEvaluation l E X q ⋙
        (sfIntrinsicExtensionByZero c.i
          (Padic.coefficientExtensionRing l E (q + 1))).mapDerivedCategory) := by
  have := ProEtale.VaryingRing.extensionAdditive (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i
  have := ProEtale.VaryingRing.extensionLimits (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i
  have := ProEtale.VaryingRing.extensionColimits (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i
  have := sfIntrinsicExtensionByZero_additive c.i
    (Padic.coefficientExtensionRing l E (q + 1))
  have := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (q + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (q + 1))).2.2
  obtain ⟨j, _⟩ := coefPairing_native_operations l E c S G
  exact ⟨Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso j) _ ≪≫
    ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i q ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryNatIso
      (compactSupportOpenModel c.i (Padic.coefficientExtensionRing l E (q + 1))))⟩

/-- Finite evaluation transports the proper mate of a supplied pairing system
to the proper mate of one finite frame, simultaneously for all scalar towers
H and all system inputs M. The two arrows have prescribed endpoints: on the
finite side the scalar input is H evaluated at q and the open input is M
evaluated at q. This is an isomorphism of arrows, not an assertion that either
proper mate is invertible. No finite-Tor or constructibility hypothesis occurs.

Source: Stacks 07A6, 0B56, 0941; prop-coef-integral-dualizing paragraph 2.
(blueprint: lem-coef-pairing-proper-mate-evaluation).

Proof: normalized reductions preserve the supplied tensor structures and supply
their evaluation isomorphisms. Finite-frame descent supplies one F and the proper
left/right evaluation comparisons with their unit, counit and strong tensor
squares; its strong tensor is the descent of the supplied properTensor. The
separate sections-left comparison identifies evaluation of G.frame.sstar(H)
with F.sstar(H_q). Native ordinary open comparison, exact localization and native
open evaluation identify the other input with intrinsic finite open extension.
Expand leftMate as the adjunction transpose of properTensor followed by tensor
of the counit. The unit comparison transports this transpose through evaluation.
Tensor naturality, the counit comparison, and the strong tensor square identify
it with the finite transpose. These equations give the two endpoint isomorphisms
and a commuting arrow square. Finally naturality of the uncurried projection
map transports its two inputs by the sections and open isomorphisms. Composing
these arrow isomorphisms proves the assertion uniformly in H and M. -/
theorem coefPairing_proper_mate_evaluation
    {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    (S : CoefficientDerivedSystemCalculus l E X) (G : CoefPairingSystem l E c S)
    (q : ℕ) :
    ∃ F : CoefPairingFiniteFrame l E c S G q,
      ∀ (H : coefPairingDerived l E) (M : coefficientSequenceDerived.{u, u} l E X),
      Nonempty
        (Arrow.mk ((coefficientSequenceDerivedEvaluation l E Y q).map
          (CategoryTheory.CoefPairingFrame.leftMate
            G.baseTensors.systemClosed.tensor G.compactTensors.systemClosed.tensor
            G.frame.pstar G.properModules.rightDerivedFunctor G.frame.properAdjunction
            G.frame.properTensor (G.frame.sstar.obj H)
            (G.openModules.mapDerivedCategory.obj M))) ≅
          Arrow.mk (CategoryTheory.CoefPairingFrame.leftMate
            (G.baseTensors.finiteClosed q).tensor (G.compactTensors.finiteClosed q).tensor
            F.pstar
            (proEtaleConstantDerivedDirectImage c.g
              (Padic.coefficientExtensionRing l E (q + 1)))
            F.properAdjunction F.properTensor
            (F.sstar.obj ((coefPairingDerivedEvaluation l E q).obj H))
            ((sfIntrinsicExtensionByZero c.i
              (Padic.coefficientExtensionRing l E (q + 1))).mapDerivedCategory.obj
              ((coefficientSequenceDerivedEvaluation l E X q).obj M)))) := by
  obtain ⟨RY, hY, _⟩ := coefficientNormalizedReductionModels l E Y G.baseTensors
  obtain ⟨RZ, hZ, _⟩ := coefficientNormalizedReductionModels l E c.Z G.compactTensors
  have σ : G.baseTensors.systemClosed.tensor ⋙ coefficientSequenceDerivedEvaluation l E Y q ≅
      (coefficientSequenceDerivedEvaluation l E Y q).prod
        (coefficientSequenceDerivedEvaluation l E Y q) ⋙
          (G.baseTensors.finiteClosed q).tensor := by
    rw [← hY]
    exact RY.evaluationTensor q
  have τ : G.compactTensors.systemClosed.tensor ⋙
        coefficientSequenceDerivedEvaluation l E c.Z q ≅
      (coefficientSequenceDerivedEvaluation l E c.Z q).prod
        (coefficientSequenceDerivedEvaluation l E c.Z q) ⋙
          (G.compactTensors.finiteClosed q).tensor := by
    rw [← hZ]
    exact RZ.evaluationTensor q
  obtain ⟨F, e, r, hu, hc, hμ⟩ := coefPairing_finite_frame_descent l E c S G q σ τ
  obtain ⟨s⟩ := coefPairing_sections_left_evaluation l E Y
    G.frame.sstar G.frame.sectionsAdjunction q F.sstar F.sectionsAdjunction
  obtain ⟨j⟩ := pairing_open_evaluation l E c S G q
  refine ⟨F, fun H M ↦ ⟨?_⟩⟩
  exact CategoryTheory.CoefPairingFrame.leftMate_evaluation_iso
    _ _ _ _ _ _ _ _ G.frame.properAdjunction F.properAdjunction
    G.frame.properTensor F.properTensor _ _ e r σ τ hu hc hμ
    (G.frame.sstar.obj H) (G.openModules.mapDerivedCategory.obj M) ≪≫
      CategoryTheory.CoefPairingFrame.leftMate_input_iso
        _ _ _ _ F.properAdjunction F.properTensor (s.app H) (j.app M)

end WeilConjectures
