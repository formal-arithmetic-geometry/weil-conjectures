/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
public import Sheaf.RingTheory.FormalGlueingData
import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartOverlapLocalizations
import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartCompletedLocalizations

/-!
# Affine chart transitions before the square and cocycle checks

Source: Stacks Project, Tag 0BLH, first two proof paragraphs; Tag 05EL, item (1).
(blueprint: lem-sbc-punctured-completion-affine-chart-transitions)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace FormalGlueing

/-- The modules and transition equivalences of Tag 05EL, item (1), before checking
its two coherence equations. No data are selected from an existence theorem.
(blueprint: lem-sbc-punctured-completion-affine-chart-transitions) -/
structure Transitions {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {t : ℕ} (f : Fin t → R) where
  M' : ModuleCat.{u} S
  M : ∀ i : Fin t, ModuleCat.{u} (Localization.Away (f i))
  alpha : ∀ i : Fin t,
    localize (f i) (restrict φ M') ≃ₗ[R]
      restrict φ (extend φ (piece (f i) (M i)))
  alpha_smul : ∀ (i : Fin t) (s : S) (x : localize (f i) (restrict φ M')),
    alpha i ((localizedSModule φ (f i) M').smul s x) =
      (s • (alpha i x : extend φ (piece (f i) (M i))))
  alpha_overlap : ∀ i j : Fin t,
    localize (f j) (piece (f i) (M i)) ≃ₗ[R]
      localize (f i) (piece (f j) (M j))

namespace Transitions

variable {R S : Type u} [CommRing R] [CommRing S]
variable {φ : R →+* S} {t : ℕ} {f : Fin t → R}

/-- First square path of Tag 05EL, item (1).
(blueprint: lem-sbc-punctured-completion-affine-chart-transitions) -/
noncomputable abbrev squareLeft (F : Transitions φ f) (i j : Fin t) :=
  (extendMapR φ (F.alpha_overlap i j).toLinearMap).comp
    ((compare φ (f j) (piece (f i) (F.M i))).comp
      (localMap (f j) (F.alpha i).toLinearMap))

/-- Second square path of Tag 05EL, item (1).
(blueprint: lem-sbc-punctured-completion-affine-chart-transitions) -/
noncomputable abbrev squareRight (F : Transitions φ f) (i j : Fin t) :=
  (compare φ (f i) (piece (f j) (F.M j))).comp
    ((localMap (f i) (F.alpha j).toLinearMap).comp
      (swap (f i) (f j) (restrict φ F.M')))

/-- First cocycle path of Tag 05EL, item (1).
(blueprint: lem-sbc-punctured-completion-affine-chart-transitions) -/
noncomputable abbrev cocycleLeft (F : Transitions φ f) (i j k : Fin t) :=
  (localMap (f i) (F.alpha_overlap j k).toLinearMap).comp
    ((swap (f i) (f k) (piece (f j) (F.M j))).comp
      (localMap (f k) (F.alpha_overlap i j).toLinearMap))

/-- Second cocycle path of Tag 05EL, item (1).
(blueprint: lem-sbc-punctured-completion-affine-chart-transitions) -/
noncomputable abbrev cocycleRight (F : Transitions φ f) (i j k : Fin t) :=
  (swap (f i) (f j) (piece (f k) (F.M k))).comp
    ((localMap (f j) (F.alpha_overlap i k).toLinearMap).comp
      (swap (f j) (f k) (piece (f i) (F.M i))))

end Transitions

end FormalGlueing

namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The structural ring homomorphism on sections of an arbitrary open.
Source: Stacks Project, Tag 0BLH (structural maps on affine charts).
(blueprint: lem-sbc-punctured-completion-affine-chart-transitions) -/
noncomputable abbrev chartScalarMap {R : Type u} [CommRing R]
    {Z : Scheme.{u}} (h : Z ⟶ Spec (.of R)) (W : Z.Opens) : R →+* Γ(Z, W) :=
  ((ΓSpecIso (.of R)).inv ≫ h.appTop ≫
    Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {U : (Spec (.of A)).Opens}
variable {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
variable {E : Scheme.{u}} {s : E ⟶ Spec
  (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}

local notation "C" => AdicCompletion (IsLocalRing.maximalIdeal A) A
local notation "φ" => algebraMap A C

/-- The concrete structural action on completed global sections.
Source: Stacks Project, Tag 0BLH.
(blueprint: lem-sbc-punctured-completion-affine-chart-transitions) -/
noncomputable abbrev completedChartModule (s : E ⟶ Spec (.of C)) : Module C Γ(E, ⊤) :=
  Module.compHom _ ((ΓSpecIso (.of C)).inv ≫ s.appTop).hom

/-- Section identifications and generator formulas for transitions, without square or
cocycle. The last two fields record the structural scalar actions, so the identifications
can be localized without mistaking arbitrary additive maps for linear maps.
Source: Stacks Project, Tags 0BLH and 05EL, item (1).
(blueprint: lem-sbc-punctured-completion-affine-chart-transitions) -/
structure AffineChartTransitions (D : CompletionGluingData A U q E s)
    (t : ℕ) (f : Fin t → A) where
  F : FormalGlueing.Transitions φ f
  e : letI := completedChartModule s; F.M' ≃ₗ[C] Γ(E, ⊤)
  c : ∀ i, FormalGlueing.piece (f i) (F.M i) ≃+
    Γ(Y, (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))
  b : ∀ i j, FormalGlueing.localize (f i) (FormalGlueing.piece (f j) (F.M j)) ≃+
    Γ(Y, ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ⊓
      ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f j)))
  d : ∀ i, FormalGlueing.extend φ (FormalGlueing.piece (f i) (F.M i)) ≃+
    Γ(pullback q (completionSpecMap A ∣_ U),
      (pullback.fst q (completionSpecMap A ∣_ U)) ⁻¹ᵁ
        ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)))
  b_left : ∀ i j m, b i j (F.alpha_overlap i j (LocalizedModule.mk m 1)) =
    Y.presheaf.map (homOfLE inf_le_left).op (c i m)
  b_right : ∀ i j m, b i j (LocalizedModule.mk m 1) =
    Y.presheaf.map (homOfLE inf_le_right).op (c j m)
  d_prime : ∀ i m, d i (F.alpha i (LocalizedModule.mk m 1)) =
    (pullback q (completionSpecMap A ∣_ U)).presheaf.map (homOfLE le_top).op
      (D.toCompleted.appTop (e m))
  d_chart : ∀ i m, d i (TensorProduct.tmul A (1 : C) m) =
    (pullback.fst q (completionSpecMap A ∣_ U)).app _ (c i m)
  b_scalar : ∀ i j (a : A) m, b i j (a • m) =
    chartScalarMap (q ≫ U.ι) _ a * b i j m
  d_scalar : ∀ i (z : C) m, d i (z • m) =
    chartScalarMap (pullback.snd q (completionSpecMap A ∣_ U) ≫
      (completionSpecMap A ⁻¹ᵁ U).ι) _ z * d i m

/-- Construct the affine section modules and the transition equivalences, postponing
only the square and cocycle check.

Source: Stacks Project, Tag 0BLH, first two proof paragraphs; Tag 05EL, item (1).
(blueprint: lem-sbc-punctured-completion-affine-chart-transitions)

Proof: let V_i be the inverse image of D(f_i) in Y. The hypotheses give
affineness of E and every V_i. Set M'=Gamma(E,top)
with the structural C-action, and M_i=Gamma(Y,V_i). The structural A-action on
M_i extends uniquely to A_(f_i), since f_i is invertible on V_i. Thus e and
c_i are identity identifications of these actual section rings, not arbitrary
witnesses. The basic-open section localization theorem identifies (M_j)_(f_i)
with Gamma(Y,V_i intersect V_j), defining b_ij by its universal property.
The affine pullback tensor-product description identifies C tensor_A M_i with
Gamma(O,p inverse-image V_i), giving d_i. The given overlap isomorphism D,
and its equation D.over, identify the same completed open with the principal
open f_i of E. Its sections are (M')_(f_i). Compose these section equivalences
to obtain alpha_i, and use the common double intersection to obtain alpha_ij.
All maps commute with structural scalars, proving alpha_smul, b_scalar and
d_scalar. The localization map m to m/1 becomes actual restriction of m,
proving b_left, b_right and d_prime. The tensor map m to 1 tensor m is pullback
of sections, proving d_chart. No square or cocycle is asserted here. Empty
principal opens have the zero section ring and zero localized modules, so
the same universal properties apply. For t=0 only M' and e are needed.
(blueprint: lem-sbc-punctured-completion-affine-chart-transitions-succ)

Proof: construct the affine section modules, localization and tensor-product equivalences,
and scalar and restriction identities for the positive finite chart family as in Tags
0BLH and 05EL.
-/
theorem exists_affine_chart_transitions_succ
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} [IsAffine E] {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin (t + 1) → A)
    (hf : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ U)
    (hV : ∀ i, IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))) :
    Nonempty (AffineChartTransitions D (t + 1) f) := by
  let : Module (AdicCompletion (IsLocalRing.maximalIdeal A) A) Γ(E, ⊤) :=
    completedChartModule s
  obtain ⟨alpha_overlap, b, hbl, hbr, hbs⟩ :=
    exists_chart_overlap_localizations (q ≫ U.ι) (t + 1) f hV
  obtain ⟨alpha, d, has, hdp, hdc, hds⟩ :=
    exists_chart_completed_localizations D (t + 1) f hf hV
  let F : FormalGlueing.Transitions (algebraMap A
      (AdicCompletion (IsLocalRing.maximalIdeal A) A)) f :=
    { M' := completedSectionModule s
      M := fun i ↦ chartSectionModule (q ≫ U.ι) (f i)
      alpha := alpha
      alpha_smul := has
      alpha_overlap := alpha_overlap }
  exact ⟨{
    F := F
    e := LinearEquiv.refl (AdicCompletion (IsLocalRing.maximalIdeal A) A) Γ(E, ⊤)
    c := fun i ↦ AddEquiv.refl _
    b := b
    d := d
    b_left := hbl
    b_right := hbr
    d_prime := hdp
    d_chart := hdc
    b_scalar := hbs
    d_scalar := hds }⟩

private theorem empty_chart_transitions
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens} {Y E : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {s : E ⟶ Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (f : Fin 0 → A) :
    Nonempty (AffineChartTransitions D 0 f) := by
  let _ : Module (AdicCompletion (IsLocalRing.maximalIdeal A) A) Γ(E, ⊤) :=
    completedChartModule s
  let F : FormalGlueing.Transitions
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) f :=
    { M' := ModuleCat.of (AdicCompletion (IsLocalRing.maximalIdeal A) A) Γ(E, ⊤)
      M := fun i ↦ Fin.elim0 i
      alpha := fun i ↦ Fin.elim0 i
      alpha_smul := fun i ↦ Fin.elim0 i
      alpha_overlap := fun i ↦ Fin.elim0 i }
  exact ⟨{
    F := F
    e := LinearEquiv.refl (AdicCompletion (IsLocalRing.maximalIdeal A) A) Γ(E, ⊤)
    c := fun i ↦ Fin.elim0 i
    b := fun i ↦ Fin.elim0 i
    d := fun i ↦ Fin.elim0 i
    b_left := fun i ↦ Fin.elim0 i
    b_right := fun i ↦ Fin.elim0 i
    d_prime := fun i ↦ Fin.elim0 i
    d_chart := fun i ↦ Fin.elim0 i
    b_scalar := fun i ↦ Fin.elim0 i
    d_scalar := fun i ↦ Fin.elim0 i }⟩

theorem exists_affine_chart_transitions
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} [IsAffine E] {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hf : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ U)
    (hV : ∀ i, IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))) :
    Nonempty (AffineChartTransitions D t f) := by
  cases t with
  | zero => exact empty_chart_transitions D f
  | succ t => exact exists_affine_chart_transitions_succ D t f hf hV

end AlgebraicGeometry.Scheme.CompletionGluingData
