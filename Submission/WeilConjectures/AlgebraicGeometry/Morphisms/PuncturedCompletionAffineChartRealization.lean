/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
public import Submission.WeilConjectures.RingTheory.FormalGlueingData
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineChartCoherence

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Realizing formal glueing data on affine principal charts

Source: Stacks Project, Tag 0BLH, first two proof paragraphs; Tag 05EL.
(blueprint: lem-sbc-punctured-completion-affine-chart-realization)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

private theorem empty_chart_transitions
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens} {Y E : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {s : E ⟶ Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (f : Fin 0 → A) :
    Nonempty (AffineChartTransitions D 0 f) := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let : Module C Γ(E, ⊤) := completedChartModule s
  let F : FormalGlueing.Transitions (algebraMap A C) f :=
    { M' := ModuleCat.of C Γ(E, ⊤)
      M := fun i ↦ Fin.elim0 i
      alpha := fun i ↦ Fin.elim0 i
      alpha_smul := fun i ↦ Fin.elim0 i
      alpha_overlap := fun i ↦ Fin.elim0 i }
  exact ⟨{
    F := F
    e := LinearEquiv.refl C Γ(E, ⊤)
    c := fun i ↦ Fin.elim0 i
    b := fun i ↦ Fin.elim0 i
    d := fun i ↦ Fin.elim0 i
    b_left := fun i ↦ Fin.elim0 i
    b_right := fun i ↦ Fin.elim0 i
    d_prime := fun i ↦ Fin.elim0 i
    d_chart := fun i ↦ Fin.elim0 i
    b_scalar := fun i ↦ Fin.elim0 i
    d_scalar := fun i ↦ Fin.elim0 i }⟩

/-- Realize the localization and scalar-extension maps as actual restrictions on
principal affine charts. This statement concerns arbitrary chart and prime elements;
it neither constructs an H0 family nor asserts that the charts cover.

Source: Stacks Project, Tag 0BLH, first two proof paragraphs; Tag 05EL, item (1).
(blueprint: lem-sbc-punctured-completion-affine-chart-realization)

Proof: write V_i for the inverse image of D(f_i) under q followed by U's inclusion.
The containment hypothesis identifies V_i with the finite inverse image of the
whole affine D(f_i), so V_i is affine. The finite scheme E over Spec C is affine.
Use Gamma(E,top) for M' with its structural C-action. Use Gamma(Y,V_i) for M_i,
with the A_{f_i}-action induced by q. Let e and c_i be the identity identifications.
The open V_i intersect V_j is the principal open f_i in V_j. Its section ring
is the localization of M_j at f_i; this gives b_ij (Mathlib's
IsAffineOpen.isLocalization_basicOpen and the module localization universal property).
The overlap above V_i is the
affine base change of V_i to Spec C; its section ring is C tensor_A M_i. This
gives d_i, with tensor factors in Mathlib's order (use pullbackSpecIso and
its projection formulas after the affine identifications). On the E side the supplied
isomorphism D identifies this same open with the principal open f_i of E,
using D.over. Thus its section ring also identifies with the localization of
M' at f_i. Compose these identifications to define alpha_i and alpha_overlap.
They respect scalars because all are induced by morphisms over the affine base.
On double and triple principal opens both routes are restriction of the same
section, proving square and cocycle. More explicitly, restriction to V_i makes
f_i invertible, so its A-action extends uniquely to A_{f_i}. Each localized
section m/f_j^a maps to the restriction of m divided by the image of f_j^a.
For cocycle, on (m/f_j^a)/f_k^b both paths give the restriction of m to the
triple intersection divided by f_j^a f_k^b; the swap maps exchange the order
of these denominators. For square, on (m'/f_i^a)/f_j^b both paths give the
restriction of the E section m' to the completed double intersection divided
by f_i^a f_j^b. The compare maps send (c tensor m)/f_j^b to
c tensor (m/f_j^b), so these are precisely the maps in Data.square.
Every iterated localization element is a fraction, and tensor elements are
sums of pure tensors; these calculations prove equality of the linear maps.
The universal localization map is
restriction on original elements, giving the two b equations. The base-change
map sends 1 tensor m to the pullback of m, giving the second d equation.
The E-side localization map is restriction along D.toCompleted, giving the
first d equation. These arguments include empty or zero principal charts:
their section and localization modules are zero. With t=0 only M' and e remain.
-/
theorem exists_affine_chart_realization
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hf : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ U) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    letI : Algebra A C := φ.toAlgebra
    let g : CommRingCat.of C ⟶ Γ(E, ⊤) := (ΓSpecIso (.of C)).inv ≫ s.appTop
    letI : Module C Γ(E, ⊤) := Module.compHom _ g.hom
    let V := fun i ↦ (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
    let O := pullback q (completionSpecMap A ∣_ U)
    let p : O ⟶ Y := pullback.fst q (completionSpecMap A ∣_ U)
    ∃ (X : FormalGlueing.Data.{u, u, u} φ f) (e : X.M' ≃ₗ[C] Γ(E, ⊤))
      (c : ∀ i, FormalGlueing.piece (f i) (X.M i) ≃+ Γ(Y, V i))
      (b : ∀ i j, FormalGlueing.localize (f i) (FormalGlueing.piece (f j) (X.M j)) ≃+
        Γ(Y, V i ⊓ V j))
      (d : ∀ i, FormalGlueing.extend φ (FormalGlueing.piece (f i) (X.M i)) ≃+
        Γ(O, p ⁻¹ᵁ V i)),
      (∀ i j m, b i j (X.alpha_overlap i j (LocalizedModule.mk m 1)) =
        Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i m)) ∧
      (∀ i j m, b i j (LocalizedModule.mk m 1) =
        Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j m)) ∧
      (∀ i m, d i (X.alpha i (LocalizedModule.mk m 1)) =
        O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V i ≤ ⊤)).op
          (D.toCompleted.appTop (e m))) ∧
      (∀ i m, d i (TensorProduct.tmul A (1 : C) m) = p.app (V i) (c i m)) := by
  let : IsAffine E := isAffine_of_isAffineHom s
  have hV : ∀ i, IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) := by
    intro i
    rw [Scheme.Hom.comp_preimage]
    have hbase : IsAffineOpen (X := Spec (.of A)) (PrimeSpectrum.basicOpen (f i)) :=
      IsAffineOpen.Spec_basicOpen (R := .of A) (f i)
    have hsub : PrimeSpectrum.basicOpen (f i) ≤ U.ι.opensRange := by
      rw [Scheme.Opens.opensRange_ι]
      exact hf i
    exact (hbase.preimage_of_isOpenImmersion U.ι hsub).preimage q
  have hT : Nonempty (AffineChartTransitions D t f) := by
    cases t with
    | zero => exact empty_chart_transitions D f
    | succ t => exact exists_affine_chart_transitions D (t + 1) f hf hV
  obtain ⟨T⟩ := hT
  obtain ⟨hsquare, hcocycle⟩ := affine_chart_transition_coherence D t f hf hV T
  let X : FormalGlueing.Data (algebraMap A
      (AdicCompletion (IsLocalRing.maximalIdeal A) A)) f :=
    { M' := T.F.M'
      M := T.F.M
      alpha := T.F.alpha
      alpha_smul := T.F.alpha_smul
      alpha_overlap := T.F.alpha_overlap
      square := hsquare
      cocycle := hcocycle }
  refine ⟨X, T.e, T.c, T.b, T.d, ?_⟩
  exact ⟨T.b_left, T.b_right, T.d_prime, T.d_chart⟩

end AlgebraicGeometry.Scheme.CompletionGluingData
