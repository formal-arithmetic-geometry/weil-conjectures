/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.CurveRestrictionFiltrationData
import Sheaf.Paper.CurveClassicalPullbackExists
import Sheaf.Paper.CurveClassicalFiltrationPullback
import Sheaf.Paper.CurveRestrictionLocalPowers

/-! # Assembly of curve restriction, filtrations and local spectra

Source: blueprint latest, real-mixed-by-curves, paragraphs 1--2.
(blueprint: lem-zl-curve-restriction-filtration-spectrum).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.defProp false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor (IsoAlgebra)
open Opposite
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

variable (m : ℕ) (hm : 1 ≤ m)
  (C₀ : Over (Spec (.of (D.extensionSubfield m hm))))
  [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
  (h₀ : C₀ ⟶ constantExtensionModel D m hm X₀) [IsClosedImmersion h₀.left]

attribute [local irreducible] ZlClassicalRealization.weil zlCurveRestriction
  zlCurveGeometricMap zlCurveFiniteStalkIso zlCurveFiniteFrobenius
  constantExtensionHeartForget commonStageDerivedPullback
  sfWeilStageObject ZlCurveLocalConclusions IsCommonStageLisse

private theorem curve_map_eq_top_heq
    {A C : Type*} [Category A] [Category C] (Y : A ⥤ C)
    {a a' : A} {b : C} (h : a = a') (e : Y.obj a' ≅ b) :
    HEq (Y.mapIso (eqToIso h) ≪≫ e) e := by
  cases h
  simp only [eqToIso_refl, Functor.mapIso_refl, Iso.refl_trans]
  rfl

private theorem curve_map_iso_square
    {A C : Type*} [Category A] [Category C] (Y : A ⥤ C)
    {A₁ A₂ B₁ B₂ : A} (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂)
    (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂)
    (h : e₁.hom ≫ g = f ≫ e₂.hom) :
    (Y.mapIso e₁).hom ≫ Y.map g = Y.map f ≫ (Y.mapIso e₂).hom := by
  simpa only [Functor.map_comp, Functor.mapIso_hom] using
    congrArg (fun k : A₁ ⟶ B₂ ↦ Y.map k) h

private theorem curve_comp_iso_square
    {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (d₁ : Y₁ ≅ Z₁) (d₂ : Y₂ ≅ Z₂)
    (h₁ : e₁.hom ≫ g = f ≫ e₂.hom)
    (h₂ : d₁.hom ≫ h = g ≫ d₂.hom) :
    (e₁ ≪≫ d₁).hom ≫ h = f ≫ (e₂ ≪≫ d₂).hom := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [h₂, ← Category.assoc, h₁, Category.assoc]

private def curve_top_iso
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    (X : A ⥤ B) (P : B ⥤ C) (F : A ⥤ E) (Y : E ⥤ C)
    (α : X ⋙ P ≅ F ⋙ Y) (a : A) (b : B) (e : X.obj a ≅ b) :
    Y.obj (F.obj a) ≅ P.obj b :=
  (α.app a).symm ≪≫ P.mapIso e

private theorem curve_top_iso_heq
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    (X : A ⥤ B) (P : B ⥤ C) (F : A ⥤ E) (Y : E ⥤ C)
    (α : X ⋙ P ≅ F ⋙ Y) (a : A) (b : B) (e : X.obj a ≅ b) :
    HEq (curve_top_iso X P F Y α a b e) ((α.app a).symm ≪≫ P.mapIso e) := by
  rfl

private def curve_term_iso
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    (X : A ⥤ B) (P : B ⥤ C) (F : A ⥤ E) (Y : E ⥤ C)
    (α : X ⋙ P ≅ F ⋙ Y) (a : A) (d : E) (β : d ≅ F.obj a) :
    P.obj (X.obj a) ≅ Y.obj d :=
  α.app a ≪≫ Y.mapIso β.symm

private theorem curve_term_square
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    (X : A ⥤ B) (P : B ⥤ C) (F : A ⥤ E) (Y : E ⥤ C)
    (α : X ⋙ P ≅ F ⋙ Y) {a₁ a₂ : A} {d₁ d₂ : E}
    (f : a₁ ⟶ a₂) (g : d₁ ⟶ d₂) (β₁ : d₁ ≅ F.obj a₁) (β₂ : d₂ ≅ F.obj a₂)
    (h : β₁.inv ≫ g = F.map f ≫ β₂.inv) :
    (curve_term_iso X P F Y α a₁ d₁ β₁).hom ≫ Y.map g =
      P.map (X.map f) ≫ (curve_term_iso X P F Y α a₂ d₂ β₂).hom := by
  exact curve_comp_iso_square _ _ _ (α.app a₁) (α.app a₂)
    (Y.mapIso β₁.symm) (Y.mapIso β₂.symm) (α.hom.naturality f).symm
    (curve_map_iso_square Y (F.map f) g β₁.symm β₂.symm h)

@[instance_reducible]
private def curve_zero_structure
    {A : Type*} [Category A] {z : HasZeroMorphisms A}
    {S : @ShortComplex A _ z} (_h : @ShortComplex.ShortExact A _ z S) :
    HasZeroMorphisms A := z

private theorem curve_shortExact_of_iso
    {A : Type*} [Category A] [HasZeroMorphisms A]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : A}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (f' : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃)
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃)
    (hf : e₁.hom ≫ f' = f ≫ e₂.hom)
    (hg : e₂.hom ≫ g' = g ≫ e₃.hom)
    (hz : f' ≫ g' = 0) (he : (ShortComplex.mk f' g' hz).ShortExact) :
    ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact := by
  have h : f ≫ g = 0 := by
    apply (cancel_mono e₃.hom).mp
    calc
      (f ≫ g) ≫ e₃.hom = f ≫ (g ≫ e₃.hom) := Category.assoc _ _ _
      _ = f ≫ (e₂.hom ≫ g') := by rw [hg]
      _ = e₁.hom ≫ (f' ≫ g') := by rw [← Category.assoc, ← hf, Category.assoc]
      _ = 0 ≫ e₃.hom := by rw [hz]; simp
  exact ⟨h, (ShortComplex.shortExact_iff_of_iso
    (ShortComplex.isoMk e₁ e₂ e₃ hf hg)).mpr he⟩

private theorem curve_zero_reindex
    {I A : Type*} [Category A] (T : I → A) {i : I} (hz : IsZero (T i))
    (j : I) (h : i = j) : IsZero (T j) := by
  cases h
  exact hz

/-- Exact restriction of the actual classical lisse Weil filtration to the closed curve,
with its normalized geometric pullback and residue-degree local spectrum.
Source: blueprint latest, thm-zl-real-mixed-by-curves.proof.md, paragraphs 1--2;
Weil II (1.1.8)--(1.1.10); BS 6.8.4, 6.8.14, 6.8.15
(blueprint: lem-zl-curve-restriction-filtration-spectrum).

Proof:
1. Base change preserves separated finite type. A closed immersion is finite, so C₀
and both geometric fibres satisfy the hypotheses, also when empty or disconnected.
2. Apply lem-zl-classical-weil-filtration-heart-transport to the prescribed diagram,
retaining its inclusions, quotients, top identification and both Weil maps at one field.
3. Apply lem-zl-constant-extension-weil-heart-equivalence and
lem-zl-immersion-weil-local-behavior. Their exact heart functors give each short exact
sequence; its cokernel universal property identifies the quotient canonically.
4. Realize the finite diagram by finite locally free integral systems. Ordinary inverse
image preserves their trivializing covers and reduction isomorphisms. Apply
lem-per-lisse-completed-system-comparison and lem-tw-lisse-rational-realization to identify
this with derived inverse image. Their unit normalizations give the displayed comparison.
5. The identity/composition equations give naturality on all arrows and their composites.
Apply them to g_X^m h = h g_C and to the Weil map and its inverse. On point fibres the
restriction/coprojection comparison commutes with each transport, hence every iterate.
The return compositor and ordered Weil product then give the local operator comparison.
6. A closed immersion identifies residue fields. Constant extension sends the local
operator at its image to the residue-degree power of the original operator. Compose
the canonical stalk maps; their composition is exactly the inverse-compositor map here.
Thus f is positive and q_z=q_x^f, without replacing f by the total extension degree m.
7. Apply lem-zl-power-spectrum-conjugation and invariance of characteristic polynomials
under that stalk isomorphism. This counts algebraic multiplicities, including Jordan
blocks and collisions of powers.
8. The same lemma preserves conjugation-stable multisets under powers, so the restricted
local factors remain real. Apply def-wf-iota-real at every closed point.
9. For r=0 the only term and G are zero and there are no quotient conditions. Empty C₀
has no closed points. Rank-zero factors are the empty product 1. No step assumes
semisimplicity or diagonalizability. -/
theorem zl_curve_restriction_filtration_spectrum (iota : Ω ≃+* ℂ) :
    ZlCurveRestrictionFiltrationSpectrum D l hl Ω X₀ m hm C₀ h₀ iota := by
  let := zlCurveSeparated D X₀ m hm C₀ h₀
  let : LocallyOfFiniteType
      (show Over (Spec (.of (constantExtensionDatum D m hm).k₀)) from C₀).hom := by
    change LocallyOfFiniteType C₀.hom
    infer_instance
  let : QuasiCompact
      (show Over (Spec (.of (constantExtensionDatum D m hm).k₀)) from C₀).hom := by
    change QuasiCompact C₀.hom
    infer_instance
  let : IsSeparated
      (show Over (Spec (.of (constantExtensionDatum D m hm).k₀)) from C₀).hom := by
    change IsSeparated C₀.hom
    infer_instance
  let : Fact (∀ x : (D.geometricFiber X₀).left,
      IsUnit (l : (D.geometricFiber X₀).left.presheaf.stalk x)) :=
    ⟨fun x ↦ @isUnit_of_invertible _ _ _ (zlClassicalStalkInvertible D l hl X₀ x)⟩
  let : Fact (∀ x : ((constantExtensionDatum D m hm).geometricFiber C₀).left,
      IsUnit (l : ((constantExtensionDatum D m hm).geometricFiber C₀).left.presheaf.stalk x)) :=
    ⟨fun x ↦ @isUnit_of_invertible _ _ _
      (zlClassicalStalkInvertible (constantExtensionDatum D m hm) l hl C₀ x)⟩
  intro R hR RX RC
  obtain ⟨c, hc, hFib⟩ := zl_curve_classical_pullback_exists D l hl Ω X₀ m hm C₀ h₀ R hR RX RC
  refine ⟨c, ?_⟩
  intro r F G e
  have hF :=
    zl_curve_classical_filtration_pullback D l hl Ω X₀ m hm C₀ h₀ R RX RC c hFib r F
  let F' : ZlClassicalFiltration (constantExtensionDatum D m hm) l Ω C₀ r :=
    { terms := fun j ↦ c.classical.obj (F.terms j)
      quotients := fun j ↦ c.classical.obj (F.quotients j)
      inclusion := fun j ↦ c.classical.map (F.inclusion j)
      quotient := fun j ↦ c.classical.map (F.quotient j)
      zero := fun κ _ _ x ↦ (hF κ x).1
      exact := fun κ _ _ x j ↦ (hF κ x).2 j }
  have ht (j : Fin (r + 1)) : F'.terms j = c.classical.obj (F.terms j) := rfl
  have hq (j : Fin r) : F'.quotients j = c.classical.obj (F.quotients j) := rfl
  let β (j : Fin (r + 1)) := eqToIso (ht j)
  let γ (j : Fin r) := eqToIso (hq j)
  let σ (j : Fin (r + 1)) :=
    curve_term_iso (RX.weil D l hl Ω X₀)
      (zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R) c.classical
      (RC.weil (constantExtensionDatum D m hm) l hl Ω C₀) c.realization
      (F.terms j) (F'.terms j) (β j)
  let τ (j : Fin r) :=
    curve_term_iso (RX.weil D l hl Ω X₀)
      (zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R) c.classical
      (RC.weil (constantExtensionDatum D m hm) l hl Ω C₀) c.realization
      (F.quotients j) (F'.quotients j) (γ j)
  let e₀ :=
    curve_top_iso (RX.weil D l hl Ω X₀)
      (zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R) c.classical
      (RC.weil (constantExtensionDatum D m hm) l hl Ω C₀) c.realization
      (F.terms (Fin.last r)) G e
  let e' := (RC.weil (constantExtensionDatum D m hm) l hl Ω C₀).mapIso
    (β (Fin.last r)) ≪≫ e₀
  have e'_norm : HEq e'
      ((c.realization.app (F.terms (Fin.last r))).symm ≪≫
        (zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R).mapIso e) :=
    HEq.trans
      (curve_map_eq_top_heq (RC.weil (constantExtensionDatum D m hm) l hl Ω C₀)
        (ht (Fin.last r)) e₀)
      (curve_top_iso_heq (RX.weil D l hl Ω X₀)
        (zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R) c.classical
        (RC.weil (constantExtensionDatum D m hm) l hl Ω C₀) c.realization
        (F.terms (Fin.last r)) G e)
  have hX := zl_classical_weil_filtration_heart_transport D l hl Ω X₀ iota RX r F G e
  have hC := zl_classical_weil_filtration_heart_transport
    (constantExtensionDatum D m hm) l hl Ω C₀ iota RC r F'
    ((zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R).obj G) e'
  obtain ⟨tC⟩ := hC
  refine ⟨F', rfl, rfl, (fun _ ↦ HEq.rfl), (fun _ ↦ HEq.rfl), hX,
    ⟨e', e'_norm, ⟨tC⟩⟩, ?_, ?_, ?_, ?_⟩
  · -- Reindex at Fin before realization: literal zeros can carry different NeZero proofs.
    let j₀ : Fin (r + 1) := 0
    have hz := curve_zero_reindex
      (fun j : Fin (r + 1) ↦
        (RC.weil (constantExtensionDatum D m hm) l hl Ω C₀).obj (F'.terms j))
      tC.zero j₀ (Fin.ext (by simp [j₀]))
    have hz' := hz.of_iso (σ j₀)
    refine curve_zero_reindex
      (fun j : Fin (r + 1) ↦ (zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R).obj
        ((RX.weil D l hl Ω X₀).obj (F.terms j))) hz' _ ?_
    exact Fin.ext (by simp [j₀])
  · intro j
    obtain ⟨hz, he⟩ := tC.exact j
    let : HasZeroMorphisms
        (sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl C₀ Ω) :=
      curve_zero_structure he
    have hi : (β j.castSucc).inv ≫ F'.inclusion j =
        c.classical.map (F.inclusion j) ≫ (β j.succ).inv := by
      simp only [β, F', eqToIso_refl, Iso.refl_inv, Category.id_comp, Category.comp_id]
    have hq' : (β j.succ).inv ≫ F'.quotient j =
        c.classical.map (F.quotient j) ≫ (γ j).inv := by
      simp only [β, γ, F', eqToIso_refl, Iso.refl_inv, Category.id_comp, Category.comp_id]
    exact curve_shortExact_of_iso
      (A := sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl C₀ Ω) _ _ _ _
      (σ j.castSucc) (σ j.succ) (τ j)
      (curve_term_square (RX.weil D l hl Ω X₀)
        (zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R) c.classical
        (RC.weil (constantExtensionDatum D m hm) l hl Ω C₀) c.realization
        (F.inclusion j) (F'.inclusion j) (β j.castSucc) (β j.succ) hi)
      (curve_term_square (RX.weil D l hl Ω X₀)
        (zlCurveRestriction D l hl Ω X₀ m hm C₀ h₀ R) c.classical
        (RC.weil (constantExtensionDatum D m hm) l hl Ω C₀) c.realization
        (F.quotient j) (F'.quotient j) (β j.succ) (γ j) hq') hz he
  · intro H _
    exact ⟨hc H, (zl_curve_restriction_local_powers
      D l hl Ω X₀ m hm C₀ h₀ R hR RX RC c ((RX.weil D l hl Ω X₀).obj H) iota).1⟩
  · exact (zl_curve_restriction_local_powers
      D l hl Ω X₀ m hm C₀ h₀ R hR RX RC c G iota).2

end WeilConjectures
