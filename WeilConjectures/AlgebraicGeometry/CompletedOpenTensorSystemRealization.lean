/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReductionComparison
public import WeilConjectures.SixFunctors.OpenSemilinearTensorModel
public import WeilConjectures.AlgebraicGeometry.CompletedOperationTowerSubstitution
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.SfImmersionCompletedPullbackComparison
public import WeilConjectures.AlgebraicGeometry.CompletedOpenTensorRepresentatives
import WeilConjectures.AlgebraicGeometry.PurNormalizedReconstructionAdjunctionCalculus

/-! # Completion-unit realization of the strict open tensor map

Source: Stacks Project, sites-cohomology.tex Tag 0GL1 and sites-modules.tex Tag 0E8I;
strict-system and completion-unit refinement, node proof steps 4--9
(blueprint: lem-pur-completed-open-tensor-system-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedOpenTensor
open IntegralOpenReduction

private theorem adjunction_map_square
    {A B : Type*} [Category* A] [Category* B]
    {R : A ⥤ B} {L : B ⥤ A} (adj : R ⊣ L)
    {X Y Z : A} {T S : B} (g : X ⟶ Y) (q : R.obj X ≅ T)
    (f : R.obj Y ⟶ S) (b : L.obj S ⟶ Z) :
    adj.unit.app X ≫ L.map q.hom ≫ L.map (q.inv ≫ R.map g ≫ f) ≫ b =
      g ≫ adj.unit.app Y ≫ L.map f ≫ b := by
  rw [← L.map_comp_assoc, q.hom_inv_id_assoc, L.map_comp]
  have hn : adj.unit.app X ≫ L.map (R.map g) = g ≫ adj.unit.app Y :=
    (adj.unit.naturality g).symm
  simp only [Category.assoc]
  rw [reassoc_of% hn]

private theorem extension_unit_square
    {A B D F : Type*} [Category* A] [Category* B] [Category* D] [Category* F]
    (j : A ⥤ B) (RU : A ⥤ D) (RV : B ⥤ F) (J : D ⥤ F) (L : F ⥤ B)
    (r : j ⋙ RV ≅ RU ⋙ J) (η : 𝟭 B ⟶ RV ⋙ L)
    {H M : A} (a : H ⟶ M) (e : j.obj M ≅ L.obj (RV.obj (j.obj M)))
    (he : e.hom = η.app (j.obj M)) :
    η.app (j.obj H) ≫ L.map (r.hom.app H ≫ J.map (RU.map a)) ≫
      L.map (r.inv.app M) ≫ e.inv = j.map a := by
  have hn : r.hom.app H ≫ J.map (RU.map a) = RV.map (j.map a) ≫ r.hom.app M :=
    (r.hom.naturality a).symm
  rw [hn, L.map_comp]
  simp only [Category.assoc]
  rw [← L.map_comp_assoc (r.hom.app M) (r.inv.app M), r.hom_inv_id_app]
  simp only [L.map_id, Category.id_comp]
  have hn' : η.app (j.obj H) ≫ L.map (RV.map (j.map a)) =
      j.map a ≫ η.app (j.obj M) := (η.naturality (j.map a)).symm
  rw [reassoc_of% hn', ← he]
  simp

private theorem transition_bijective_of_iso
    {C A B : Type*} [Category* C] [Category* A] [Category* B]
    (F : C ⥤ A) (G : C ⥤ B) (T : B ⥤ A) (τ : F ⟶ G ⋙ T)
    {X Y : C} (e : X ≅ Y)
    (hX : ∀ P : B, Function.Bijective (fun f : G.obj X ⟶ P ↦ τ.app X ≫ T.map f))
    (P : B) : Function.Bijective (fun f : G.obj Y ⟶ P ↦ τ.app Y ≫ T.map f) := by
  let fn := Iso.homCongr (G.mapIso e) (Iso.refl P)
  let fm := Iso.homCongr (F.mapIso e) (Iso.refl (T.obj P))
  have heq : (fun f : G.obj Y ⟶ P ↦ τ.app Y ≫ T.map f) =
      fm ∘ (fun f ↦ τ.app X ≫ T.map f) ∘ fn.symm := by
    funext f
    simp only [Function.comp_apply, fm, fn, Iso.homCongr_symm, Iso.homCongr_apply,
      Iso.refl_symm, Iso.symm_inv, Iso.refl_hom, Category.comp_id,
      Functor.mapIso_hom, Functor.mapIso_inv]
    rw [T.map_comp]
    have hn : F.map e.inv ≫ τ.app X = τ.app Y ≫ T.map (G.map e.inv) :=
      τ.naturality e.inv
    rw [reassoc_of% hn, ← T.map_comp_assoc, ← G.map_comp, e.inv_hom_id,
      G.map_id, T.map_id, Category.id_comp]
  rw [heq]
  exact fm.bijective.comp ((hX P).comp fn.symm.bijective)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U V : Scheme.{t}} (j : U ⟶ V) [IsOpenImmersion j]
  (C : Context l E j)
  (K : DerivedCategory (scalarReductionSource l E U))
  (N : DerivedCategory (scalarReductionSource l E V))

private theorem complete_of_iso (W : Scheme.{t})
    {A B : DerivedCategory (scalarReductionSource l E W)} (e : A ≅ B)
    (hA : complete l E W A) : complete l E W B := by
  obtain ⟨D, hlD, P, G, q, hq, a, hprod, δ, hδ⟩ := hA
  let := hprod
  refine ⟨D, hlD, P, G, q, hq, a ≪≫ e, hprod,
    δ ≫ (shiftFunctor _ (1 : ℤ)).map e.hom, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hδ _
  refine Pretriangulated.Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · apply Pi.hom_ext
    intro n
    simp [Category.assoc]
  · simp
  · simp [Category.assoc, ← Functor.map_comp]

private theorem normalized_of_iso (W : Scheme.{t})
    {A B : coefficientSequenceDerived l E W} (e : A ≅ B)
    (hA : IsNormalizedCoefficientSequence l E W A) :
    IsNormalizedCoefficientSequence l E W B := by
  intro m n h P
  exact transition_bijective_of_iso (coefficientSequenceDerivedEvaluation l E W m)
    (coefficientSequenceDerivedEvaluation l E W n) (normalizedDVRRes l E W h)
    (coefficientSequenceDerivedTransition l E W h) e (hA h) P

private theorem completion_hom_injective (W : Scheme.{t})
    (hl : IsUnit (l : Γ(W, ⊤))) (S : CoefficientDerivedSystemCalculus l E W)
    (c : IntegralOnSlice.completion l E W none ≅
      S.reduction ⋙ coefficientSequenceLimit l E W)
    (hu : ∀ X, (IntegralOnSlice.completionUnit l E W none).app X ≫ c.hom.app X =
      S.adjunction.unit.app X)
    (X Y : DerivedCategory (scalarReductionSource l E W)) (hY : complete l E W Y) :
    Function.Injective (fun f : (IntegralOnSlice.completion l E W none).obj X ⟶ Y ↦
      (IntegralOnSlice.completionUnit l E W none).app X ≫ f) := by
  have hR := purNormalizedReconstruction l E W hl S
  have : IsIso (S.adjunction.unit.app Y) := hR.2 Y hY
  have : IsIso (S.adjunction.counit.app (S.reduction.obj X)) :=
    (hR.1 _ (S.reduction_normalized X)).2
  have : IsIso (S.reduction.map (S.adjunction.unit.app X)) := by
    have ht : S.reduction.map (S.adjunction.unit.app X) ≫
        S.adjunction.counit.app (S.reduction.obj X) = 𝟙 _ :=
      S.adjunction.left_triangle_components X
    have hi : IsIso (S.reduction.map (S.adjunction.unit.app X) ≫
        S.adjunction.counit.app (S.reduction.obj X)) := by erw [ht]; infer_instance
    exact IsIso.of_isIso_comp_right _ (S.adjunction.counit.app (S.reduction.obj X))
  intro f g hfg
  have hfg' : S.adjunction.unit.app X ≫ c.inv.app X ≫ f =
      S.adjunction.unit.app X ≫ c.inv.app X ≫ g := by
    simpa only [← hu X, Category.assoc, Iso.hom_inv_id_app_assoc] using hfg
  have hr : S.reduction.map (c.inv.app X ≫ f) =
      S.reduction.map (c.inv.app X ≫ g) := by
    apply (cancel_epi (S.reduction.map (S.adjunction.unit.app X))).1
    simpa only [← Functor.map_comp, Category.assoc] using congrArg S.reduction.map hfg'
  have hh : c.inv.app X ≫ f = c.inv.app X ≫ g := by
    apply (cancel_mono (S.adjunction.unit.app Y)).1
    calc
      _ = S.adjunction.unit.app _ ≫
          (coefficientSequenceLimit l E W).map (S.reduction.map (c.inv.app X ≫ f)) := by
        simpa only [Functor.id_map, Functor.comp_map] using
          S.adjunction.unit.naturality (c.inv.app X ≫ f)
      _ = S.adjunction.unit.app _ ≫
          (coefficientSequenceLimit l E W).map (S.reduction.map (c.inv.app X ≫ g)) := by erw [hr]
      _ = _ := by
        simpa only [Functor.id_map, Functor.comp_map] using
          (S.adjunction.unit.naturality (c.inv.app X ≫ g)).symm
  exact (cancel_epi (c.inv.app X)).1 hh

private theorem realized_extension_unit
    (H M : DerivedCategory (scalarReductionSource l E U)) (hM : complete l E U M)
    (a : H ⟶ M) :
    C.ambient.adjunction.unit.app ((shriek l E j C.operations).obj H) ≫
      (coefficientSequenceLimit l E V).map
        (C.strictOpen.r.hom.app H ≫ (J l E j C.operations).map (C.openSite.reduction.map a)) ≫
      C.completeOpen.d.hom.app ⟨M, hM⟩ = (shriek l E j C.operations).map a := by
  have hi : C.completeOpen.r.inv.app ⟨M, hM⟩ = C.strictOpen.r.inv.app M := by
    have h : C.strictOpen.r.app M = C.completeOpen.r.app ⟨M, hM⟩ :=
      Iso.ext (C.sameOpen ⟨M, hM⟩)
    exact congrArg Iso.inv h.symm
  have hd := C.completeOpen.dFormula ⟨M, hM⟩
  erw [hi] at hd
  erw [hd]
  exact extension_unit_square (shriek l E j C.operations) C.openSite.reduction
    C.ambient.reduction (J l E j C.operations) (coefficientSequenceLimit l E V)
    C.strictOpen.r C.ambient.adjunction.unit a
    (C.completeOpen.unitX ⟨(shriek l E j C.operations).obj M,
      C.completeOpen.extensionComplete ⟨M, hM⟩⟩)
    (C.completeOpen.unitXHom _)

private theorem realized_tensor_unit (γ : OrdinaryMap l E j C)
    (hc : complete l E U
      ((coefficientSequenceLimit l E U).obj (openSystem l E j C K N)))
    (he : IsIso (C.openSite.adjunction.counit.app (openSystem l E j C K N))) :
    (IntegralOnSlice.completionUnit l E V none).app
        ((ordinarySource l E j C).obj (K, N)) ≫
      (sourceIdentification l E j C K N).hom ≫
      (coefficientSequenceLimit l E V).map (systemMap l E j C K N γ).hom ≫
      (targetIdentification l E j C K N hc he).hom =
    (γ.app (K, N)).hom ≫ (shriek l E j C.operations).map
      ((IntegralOnSlice.completionUnit l E U none).app
        ((ordinaryOpen l E j C).obj (K, N))) := by
  let H := (ordinaryOpen l E j C).obj (K, N)
  let a : H ⟶ (coefficientSequenceLimit l E U).obj (openSystem l E j C K N) :=
    (IntegralOnSlice.completionUnit l E U none).app H ≫
      (openIdentification l E j C K N).hom
  have ha : a = C.openSite.adjunction.unit.app H ≫
      (coefficientSequenceLimit l E U).map
        ((reductionTensorU l E j C).hom.app (K, (star l E j C.operations).obj N)) := by
    dsimp [a, openIdentification]
    erw [← Category.assoc, C.unitU]
  have : IsIso (C.openSite.adjunction.counit.app (openSystem l E j C K N)) := he
  have hra : C.openSite.reduction.map a =
      (reductionTensorU l E j C).hom.app (K, (star l E j C.operations).obj N) ≫
        inv (C.openSite.adjunction.counit.app (openSystem l E j C K N)) := by
    apply (cancel_mono
      (C.openSite.adjunction.counit.app (openSystem l E j C K N))).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    erw [ha, Functor.map_comp]
    erw [Category.assoc, C.openSite.adjunction.counit.naturality]
    erw [← Category.assoc, C.openSite.adjunction.left_triangle_components]
    simp
  have hd := realized_extension_unit l E j C H _ hc a
  erw [hra] at hd
  have hx := adjunction_map_square C.ambient.adjunction (γ.app (K, N)).hom
    ((reductionTensorV l E j C).app ((shriek l E j C.operations).obj K, N))
    (C.strictOpen.r.hom.app H ≫ (J l E j C.operations).map
      ((reductionTensorU l E j C).hom.app (K, (star l E j C.operations).obj N) ≫
        inv (C.openSite.adjunction.counit.app (openSystem l E j C K N))))
    (C.completeOpen.d.hom.app
        ⟨(coefficientSequenceLimit l E U).obj (openSystem l E j C K N), hc⟩ ≫
      (shriek l E j C.operations).map (openIdentification l E j C K N).inv)
  have hs : (IntegralOnSlice.completionUnit l E V none).app
        ((ordinarySource l E j C).obj (K, N)) ≫
      (sourceIdentification l E j C K N).hom ≫
      (coefficientSequenceLimit l E V).map (systemMap l E j C K N γ).hom ≫
      (targetIdentification l E j C K N hc he).hom =
      (γ.app (K, N)).hom ≫ C.ambient.adjunction.unit.app
        ((shriek l E j C.operations).obj H) ≫
      (coefficientSequenceLimit l E V).map
        (C.strictOpen.r.hom.app H ≫ (J l E j C.operations).map
          ((reductionTensorU l E j C).hom.app (K, (star l E j C.operations).obj N) ≫
            inv (C.openSite.adjunction.counit.app (openSystem l E j C K N)))) ≫
      C.completeOpen.d.hom.app
        ⟨(coefficientSequenceLimit l E U).obj (openSystem l E j C K N), hc⟩ ≫
      (shriek l E j C.operations).map (openIdentification l E j C K N).inv := by
    dsimp only [sourceIdentification, systemMap, targetIdentification, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, asIso_inv]
    simp only [Functor.map_comp, Category.assoc] at hx ⊢
    erw [reassoc_of% C.unitV ((ordinarySource l E j C).obj (K, N))]
    exact hx
  apply hs.trans
  have hb : (shriek l E j C.operations).map a ≫
      (shriek l E j C.operations).map (openIdentification l E j C K N).inv =
      (shriek l E j C.operations).map
        ((IntegralOnSlice.completionUnit l E U none).app H) := by
    erw [← Functor.map_comp]
    dsimp only [a]
    erw [Category.assoc, Iso.hom_inv_id]
    simp only [Category.comp_id]
  have hd' := congrArg (fun f ↦ (γ.app (K, N)).hom ≫ f ≫
    (shriek l E j C.operations).map (openIdentification l E j C K N).inv) hd
  erw [hb] at hd'
  simpa only [Functor.map_comp, Category.assoc] using hd'

private theorem restricted_tensor_unit (γ : OrdinaryMap l E j C)
    (g : (IntegralOnSlice.completedTensor l E V none).obj
        ((shriek l E j C.operations).obj K, N) ≅
      (shriek l E j C.operations).obj
        ((IntegralOnSlice.completedTensor l E U none).obj
          (K, (star l E j C.operations).obj N)))
    (hlU : IsUnit (l : Γ(U, ⊤)))
    (hB : complete l E U ((IntegralOnSlice.completedTensor l E U none).obj
      (K, (star l E j C.operations).obj N)))
    (hg : (IntegralOnSlice.completionUnit l E V none).app
        ((ordinarySource l E j C).obj (K, N)) ≫ g.hom =
      (γ.app (K, N)).hom ≫ (shriek l E j C.operations).map
        ((IntegralOnSlice.completionUnit l E U none).app
          ((ordinaryOpen l E j C).obj (K, N)))) :
    (star l E j C.operations).map g.hom ≫
        (C.openUnit.app ((IntegralOnSlice.completedTensor l E U none).obj
          (K, (star l E j C.operations).obj N))).inv =
      (restrictedIdentification l E j C K N γ).hom := by
  apply (cancel_epi (C.restrictionCompletion.inv.app
    ((ordinarySource l E j C).obj (K, N)))).1
  apply completion_hom_injective l E U hlU C.openSite C.completionU C.unitU _ _ hB
  erw [← C.restrictionUnit]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  erw [← Functor.map_comp_assoc, hg, Functor.map_comp]
  dsimp only [restrictedIdentification, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Category.assoc]
  erw [reassoc_of% C.restrictionUnit ((ordinarySource l E j C).obj (K, N))]
  erw [← (IntegralOnSlice.completionUnit l E U none).naturality]
  simp only [Functor.map_comp, Category.assoc]
  convert (congrArg ((star l E j C.operations).map (γ.app (K, N)).hom ≫ ·)
      (C.openUnit.inv.naturality
        ((IntegralOnSlice.completionUnit l E U none).app
          ((ordinaryOpen l E j C).obj (K, N))))) using 1 <;> rfl

private theorem completed_for_context (γ : OrdinaryMap l E j C)
    (hlV : IsUnit (l : Γ(V, ⊤))) (hlU : IsUnit (l : Γ(U, ⊤))) :
    ∃ (hc : complete l E U
        ((coefficientSequenceLimit l E U).obj (openSystem l E j C K N)))
      (he : IsIso (C.openSite.adjunction.counit.app (openSystem l E j C K N)))
      (γc : (IntegralOnSlice.completedTensor l E V none).obj
          ((shriek l E j C.operations).obj K, N) ≅
        (shriek l E j C.operations).obj
          ((IntegralOnSlice.completedTensor l E U none).obj
            (K, (star l E j C.operations).obj N))),
      ((IntegralOnSlice.completionUnit l E V none).app
          ((ordinarySource l E j C).obj (K, N)) ≫ γc.hom =
        (γ.app (K, N)).hom ≫ (shriek l E j C.operations).map
          ((IntegralOnSlice.completionUnit l E U none).app
            ((ordinaryOpen l E j C).obj (K, N)))) ∧
      (∀ g : (IntegralOnSlice.completedTensor l E V none).obj
            ((shriek l E j C.operations).obj K, N) ≅
          (shriek l E j C.operations).obj
            ((IntegralOnSlice.completedTensor l E U none).obj
              (K, (star l E j C.operations).obj N)),
        (IntegralOnSlice.completionUnit l E V none).app
            ((ordinarySource l E j C).obj (K, N)) ≫ g.hom =
          (γ.app (K, N)).hom ≫ (shriek l E j C.operations).map
            ((IntegralOnSlice.completionUnit l E U none).app
              ((ordinaryOpen l E j C).obj (K, N))) → g = γc) ∧
      ((sourceIdentification l E j C K N).hom ≫
          (coefficientSequenceLimit l E V).map (systemMap l E j C K N γ).hom ≫
          (targetIdentification l E j C K N hc he).hom = γc.hom) ∧
      ((star l E j C.operations).map γc.hom ≫
          (C.openUnit.app ((IntegralOnSlice.completedTensor l E U none).obj
            (K, (star l E j C.operations).obj N))).inv =
        (restrictedIdentification l E j C K N γ).hom) := by
  have hS : IsNormalizedCoefficientSequence l E U (openSystem l E j C K N) :=
    normalized_of_iso l E U
    ((reductionTensorU l E j C).app (K, (star l E j C.operations).obj N))
    (C.openSite.reduction_normalized _)
  obtain ⟨hc, he⟩ := (purNormalizedReconstruction l E U hlU C.openSite).1 _ hS
  let := he
  let γc := sourceIdentification l E j C K N ≪≫
    (coefficientSequenceLimit l E V).mapIso (systemMap l E j C K N γ) ≪≫
    targetIdentification l E j C K N hc he
  have hB := complete_of_iso l E U (openIdentification l E j C K N).symm hc
  have hu := realized_tensor_unit l E j C K N γ hc he
  refine ⟨hc, he, γc, hu, ?_, rfl, ?_⟩
  · intro g hg
    apply Iso.ext
    exact completion_hom_injective l E V hlV C.ambient C.completionV C.unitV _ _
      (C.completeOpen.extensionComplete ⟨_, hB⟩) (hg.trans hu.symm)
  · exact restricted_tensor_unit l E j C K N γ γc hlU hB hu

/-- Strict open-tensor systems realize the unique completion-unit-normalized open tensor
isomorphism. Uniqueness uses only the completion-unit equation. The realization and
restriction identities are further conclusions for that uniquely determined isomorphism.

Source: Stacks sites-cohomology.tex Tag 0GL1 and sites-modules.tex Tag 0E8I, with
agent refinement for strict augmentations and completed realization
(blueprint: lem-pur-completed-open-tensor-system-realization).

Proof: construct compatible strict representatives and their ordinary open tensor
map using completedOpenTensorRepresentatives. The reduction tensor comparison
identifies the open system S with the reduction of the ordinary open tensor.
Consequently S is normalized without requiring either tensor input to be complete.
Normalized reconstruction makes L_U S complete and its actual counit invertible.

Define gamma_c as sourceIdentification, total limit of systemMap, then
targetIdentification. Counit naturality and the left triangle identity compute
the reduction of a_U = eta_U followed by openIdentification as q_U followed by
the inverse actual counit. Naturality of strictOpen.r and its agreement with
completeOpen.r on complete objects, together with dFormula and unitXHom, then
show that the realized map satisfies the completion-unit equation. Only the
unit at the complete extension of L_U S is inverted.

For uniqueness, reduction sends every reconstruction unit to an isomorphism:
its composite with the counit is identity and the counit at a reduction is
invertible. Apply reduction to two equal composites with the completion unit,
cancel this isomorphism, and use naturality of the invertible reconstruction
unit at the complete target. Thus precomposition with completionUnit is injective.
This proves uniqueness among maps, hence among isomorphisms. Finally restrict
the characterizing equation, use restrictionUnit and the same injectivity on U,
and apply naturality of the open unit to obtain restrictedIdentification.
Every identity is in the whole derived system category. No finite evaluation is
used to detect equality; all inputs may be unbounded. -/
theorem completedOpenTensorSystemRealization [QuasiCompact j]
    (_hlV : IsUnit (l : Γ(V, ⊤))) (_hlU : IsUnit (l : Γ(U, ⊤))) :
    ∃ (C : Context l E j) (γ : OrdinaryMap l E j C),
      RepresentativeLaws l E j C γ ∧
      ∀ (K : DerivedCategory (scalarReductionSource l E U))
        (N : DerivedCategory (scalarReductionSource l E V)),
        complete l E U K → complete l E V N →
        ∃ (hc : complete l E U
            ((coefficientSequenceLimit l E U).obj (openSystem l E j C K N)))
          (he : IsIso (C.openSite.adjunction.counit.app (openSystem l E j C K N)))
          (γc : (IntegralOnSlice.completedTensor l E V none).obj
              ((shriek l E j C.operations).obj K, N) ≅
            (shriek l E j C.operations).obj
              ((IntegralOnSlice.completedTensor l E U none).obj
                (K, (star l E j C.operations).obj N))),
          ((IntegralOnSlice.completionUnit l E V none).app
              ((ordinarySource l E j C).obj (K, N)) ≫ γc.hom =
            (γ.app (K, N)).hom ≫ (shriek l E j C.operations).map
              ((IntegralOnSlice.completionUnit l E U none).app
                ((ordinaryOpen l E j C).obj (K, N)))) ∧
          (∀ g : (IntegralOnSlice.completedTensor l E V none).obj
                ((shriek l E j C.operations).obj K, N) ≅
              (shriek l E j C.operations).obj
                ((IntegralOnSlice.completedTensor l E U none).obj
                  (K, (star l E j C.operations).obj N)),
            (IntegralOnSlice.completionUnit l E V none).app
                ((ordinarySource l E j C).obj (K, N)) ≫ g.hom =
              (γ.app (K, N)).hom ≫ (shriek l E j C.operations).map
                ((IntegralOnSlice.completionUnit l E U none).app
                  ((ordinaryOpen l E j C).obj (K, N))) → g = γc) ∧
          ((sourceIdentification l E j C K N).hom ≫
              (coefficientSequenceLimit l E V).map (systemMap l E j C K N γ).hom ≫
              (targetIdentification l E j C K N hc he).hom = γc.hom) ∧
          ((star l E j C.operations).map γc.hom ≫
              (C.openUnit.app ((IntegralOnSlice.completedTensor l E U none).obj
                (K, (star l E j C.operations).obj N))).inv =
            (restrictedIdentification l E j C K N γ).hom)  := by
  obtain ⟨C, γ, hγ⟩ := completedOpenTensorRepresentatives l E j _hlV _hlU
  refine ⟨C, γ, hγ, ?_⟩
  intro K N _hK _hN
  exact completed_for_context l E j C K N γ _hlV _hlU

end WeilConjectures.CompletedOpenTensor
