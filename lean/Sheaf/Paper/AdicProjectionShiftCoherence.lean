/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W9
-/
module

public import Sheaf.Paper.AdicProjectionShiftData
import Sheaf.Paper.AdicCompletedProjectionShift
import Sheaf.Paper.AdicTraceTensorShift
import Sheaf.Paper.AdicExceptionalShiftCoherence
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Shifts of the integral compact-support projection and its trace transpose
Source: blueprint sec-smooth-purity/sk-thm-purity-transport, adic Step 2
(blueprint: lem-pur-adic-projection-shift-coherence). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open IntegralSystemRealization

section AdjunctionAlgebra
variable {A B : Type*} [Category* A] [Category* B]
  [HasShift A ℤ] [HasShift B ℤ] {P : A ⥤ B} {G : B ⥤ A}

private theorem counit_shift_unique (adj : P ⊣ G)
    (e : shiftFunctor A (1 : ℤ) ⋙ P ≅ P ⋙ shiftFunctor B (1 : ℤ))
    (σ τ : shiftFunctor B (1 : ℤ) ⋙ G ≅ G ⋙ shiftFunctor A (1 : ℤ))
    (hσ : Adjunction.CommShift.CompatibilityCounit adj e σ)
    (hτ : Adjunction.CommShift.CompatibilityCounit adj e τ) : σ = τ := by
  apply Iso.ext
  ext K
  have h : P.map (σ.hom.app K ≫ τ.inv.app K) ≫ adj.counit.app (K⟦(1 : ℤ)⟧) =
      adj.counit.app (K⟦(1 : ℤ)⟧) := by
    rw [hτ K]
    simp only [Functor.map_comp, Category.assoc, ← P.map_comp_assoc,
      Iso.inv_hom_id_app, P.map_id, Category.id_comp]
    exact (hσ K).symm.trans (hτ K)
  have hi : σ.hom.app K ≫ τ.inv.app K = 𝟙 _ := by
    apply (adj.homEquiv _ _).symm.injective
    simpa only [Adjunction.homEquiv_counit, P.map_id, Category.id_comp] using h
  apply (cancel_mono (τ.inv.app K)).mp
  simpa only [Iso.hom_inv_id_app] using hi

end AdjunctionAlgebra

section Exceptional
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (F : Type u) [Field F] [Algebra ℚ_[C.l] F] [FiniteDimensional ℚ_[C.l] F]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (S : ConstructibleExceptionalCoefficients.RingSystem C.l C.Qbar D C.different (f := f))
  (c : Compactification f)

/-- The completed projection, the trace map u, and its exceptional transpose commute
with the shift in the second input; the exceptional comparison is uniquely
characterized by the shifted counit. No restriction on the degrees of T is made.
Source: blueprint purity transport, adic Step 2
(blueprint: lem-pur-adic-projection-shift-coherence).

Proof: choose the displayed compactification. Its projection is the canonical proper
counit mate followed by the open tensor comparison (def-exchange-projection), and is
invertible by fix-prop-projection-formula. The ringed projection-mate exactness lemma
gives the shift square of the proper factor. On K-flat representatives of the open
factor, shifting the second tensor input multiplies the summand of first degree a by
(-1)^a on both sides. Exact termwise open extension and pullback composition preserve
this equality. The argument also applies to strict systems over the ring diagram,
before finite evaluation. System projection coherence identifies that map with the
specified proper/open composite. The integral realization maps intertwine this same
map, its whiskerings and the total derived inverse limit. Integral realization shift
coherence transports the system square to the completed map below; it does not infer
an equality from finite evaluations. Invert the projection square and use tensor
naturality for t to obtain the u square. The unique adjunction shift comparison is
characterized by the shifted counit. Transpose the u square through this adjunction
to obtain the gamma square. Apply the same assertion to proper-only and open-only
compactifications to obtain the two constituent squares. -/
theorem adicProjectionShiftCoherence
    (d : RingedModels C.l F) (b : RingedOpenComparisons C.l F d)
    (T : finiteTorConstructibleIntegralCategory C.l F X) :
    ∃ (hχ : ∀ K : finiteTorConstructibleIntegralCategory C.l F Y,
        IsIso (((d.tensor Y).chi C.l F).app
          ((PurCompactSupport.image (PurCompactSupport.completed C.l F) c).obj T.obj, K.obj)))
      (hA : ∀ K : finiteTorConstructibleIntegralCategory C.l F Y,
        finiteTorConstructibleIntegral C.l F X
          ((integralCompletedTensor C.l F X).obj
            (T.obj, (integralDerivedPullback C.l F f).obj K.obj)))
      (hPF : ∀ K : finiteTorConstructibleIntegralCategory C.l F Y,
        IsIso (adicProjection C.l F d b c T.obj K.obj (hχ K))),
      (∀ hp : IsProper f,
        AdicProjectionShiftSquare C.l F d b (@Compactification.ofIsProper X Y f hp) T) ∧
      (∀ hj : IsOpenImmersion f,
        AdicProjectionShiftSquare C.l F d b (@Compactification.ofIsOpenImmersion X Y f hj) T) ∧
      (∃! σ : shiftFunctor (finiteTorConstructibleIntegralCategory C.l F Y) (1 : ℤ) ⋙
          (S.operation c (.integral { carrier := F })).G ≅
        (S.operation c (.integral { carrier := F })).G ⋙
          shiftFunctor (finiteTorConstructibleIntegralCategory C.l F X) (1 : ℤ),
        Adjunction.CommShift.CompatibilityCounit
          (S.operation c (.integral { carrier := F })).adjunction
          (Functor.commShiftIso _ (self := adicSupportShift D C F f S c) (1 : ℤ)) σ) ∧
      (∀ K : finiteTorConstructibleIntegralCategory C.l F Y,
        adicProjection C.l F d b c T.obj (K⟦(1 : ℤ)⟧).obj (hχ (K⟦(1 : ℤ)⟧)) ≫
            (PurCompactSupport.image (PurCompactSupport.completed C.l F) c).map
              (adicTensorInputShift C.l F f T.obj K).hom ≫
            ((PurCompactSupport.image (PurCompactSupport.completed C.l F) c).commShiftIso
              (1 : ℤ)).hom.app _ =
          (integralCompletedTensor C.l F Y).map
              (Prod.mkHom (𝟙 _) (adicInputShift C.l F Y K).hom) ≫
            ((tensorShifts C.l F).integralRight Y 1).hom.app
              ((PurCompactSupport.image (PurCompactSupport.completed C.l F) c).obj T.obj,
                K.obj) ≫
            (adicProjection C.l F d b c T.obj K.obj (hχ K))⟦(1 : ℤ)⟧') ∧
      (∀ (t : (PurCompactSupport.image (PurCompactSupport.completed C.l F) c).obj T.obj ⟶
          (calculus C.l F Y).integralClosed.monoidal.tensorUnit)
        (K : finiteTorConstructibleIntegralCategory C.l F Y),
        adicTraceMap C.l F d b c T.obj (K⟦(1 : ℤ)⟧).obj
            (hχ (K⟦(1 : ℤ)⟧)) (hPF (K⟦(1 : ℤ)⟧)) t ≫
            (adicInputShift C.l F Y K).hom =
          (PurCompactSupport.image (PurCompactSupport.completed C.l F) c).map
              (adicTensorInputShift C.l F f T.obj K).hom ≫
            ((PurCompactSupport.image (PurCompactSupport.completed C.l F) c).commShiftIso
              (1 : ℤ)).hom.app _ ≫
            (adicTraceMap C.l F d b c T.obj K.obj (hχ K) (hPF K) t)⟦(1 : ℤ)⟧' ∧
        adicTranspose D C F f S c
            ⟨_, hA (K⟦(1 : ℤ)⟧)⟩ (K⟦(1 : ℤ)⟧)
            (adicTraceMap C.l F d b c T.obj (K⟦(1 : ℤ)⟧).obj
              (hχ (K⟦(1 : ℤ)⟧)) (hPF (K⟦(1 : ℤ)⟧)) t) ≫
            ((adicExceptionalShift D C F f S c).hom.app K).hom ≫
            (adicInputShift C.l F X
              ((S.operation c (.integral { carrier := F })).G.obj K)).hom =
          (adicTensorInputShift C.l F f T.obj K).hom ≫
            (adicTranspose D C F f S c ⟨_, hA K⟩ K
              (adicTraceMap C.l F d b c T.obj K.obj (hχ K) (hPF K) t))⟦(1 : ℤ)⟧') := by
  obtain ⟨hχ, hA, hPF, hshift⟩ := adicCompletedProjectionShift D C F f c d b T
  refine ⟨hχ, hA, hPF, ?_, ?_, ?_, hshift, ?_⟩
  · intro hp
    obtain ⟨hχ', _, _, hs⟩ :=
      adicCompletedProjectionShift D C F f (@Compactification.ofIsProper X Y f hp) d b T
    exact ⟨hχ', hs⟩
  · intro hj
    obtain ⟨hχ', _, _, hs⟩ :=
      adicCompletedProjectionShift D C F f (@Compactification.ofIsOpenImmersion X Y f hj) d b T
    exact ⟨hχ', hs⟩
  · let adj := (S.operation c (.integral { carrier := F })).adjunction
    let := adicSupportShift D C F f S c
    let := adj.rightAdjointCommShift ℤ
    let := adj.commShift_of_leftAdjoint ℤ
    have hc : Adjunction.CommShift.CompatibilityCounit adj
        (Functor.commShiftIso _ (1 : ℤ)) (adicExceptionalShift D C F f S c) := by
      intro K
      simpa only [Functor.commShiftIso_comp_hom_app, adicExceptionalShift,
        Category.assoc] using
        (adj.commShiftIso_hom_app_counit_app_shift ℤ (1 : ℤ) K).symm
    exact ⟨adicExceptionalShift D C F f S c, hc,
      fun σ hσ ↦ counit_shift_unique adj _ σ _ hσ hc⟩
  · intro t K
    have hu : adicTraceMap C.l F d b c T.obj (K⟦(1 : ℤ)⟧).obj
          (hχ (K⟦(1 : ℤ)⟧)) (hPF (K⟦(1 : ℤ)⟧)) t ≫
          (adicInputShift C.l F Y K).hom =
        (PurCompactSupport.image (PurCompactSupport.completed C.l F) c).map
            (adicTensorInputShift C.l F f T.obj K).hom ≫
          ((PurCompactSupport.image (PurCompactSupport.completed C.l F) c).commShiftIso
            (1 : ℤ)).hom.app _ ≫
          (adicTraceMap C.l F d b c T.obj K.obj (hχ K) (hPF K) t)⟦(1 : ℤ)⟧' := by
      let := hPF K
      let := hPF (K⟦(1 : ℤ)⟧)
      apply (cancel_epi
        (adicProjection C.l F d b c T.obj (K⟦(1 : ℤ)⟧).obj (hχ (K⟦(1 : ℤ)⟧)))).mp
      simp only [adicTraceMap, Category.assoc, IsIso.hom_inv_id_assoc]
      rw [adicTraceTensorShift C.l F d c T.obj hχ t K]
      erw [reassoc_of% hshift K]
      simp only [Functor.map_comp, Functor.map_inv]
      erw [IsIso.hom_inv_id_assoc]
      rfl
    exact ⟨hu, adicExceptionalTransposeShift D C F f S c
      ⟨_, hA K⟩ ⟨_, hA (K⟦(1 : ℤ)⟧)⟩ K
      (adicTensorInputShift C.l F f T.obj K).hom _ _ hu⟩

end Exceptional
end WeilConjectures
