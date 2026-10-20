/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.WeilMixedUpperBounds
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Sheaf.Paper.WeilCompactSupportCohomology
public import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.FiniteCompactificationWeilExact
import Sheaf.Paper.FiniteCompactificationEigenvalues
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization

/-! # Quasi-finite compact-support images and upper weights

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-l-dl-general-quasifinite, statement and finite-fibre argument
(blueprint: sk-l-dl-general-quasifinite).

The three clauses use the existing common-stage constructible Weil heart and its
compact-support higher images. The coefficient embedding need not be surjective.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem punctualEigenvalue_of_iso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    {F G : sfCommonStageWeilSheaf D l hl Y₀ Ω} (e : F ≅ G)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (α : Ω)
    (h : SfPunctualEigenvalue D l hl Ω Y₀ F y α) :
    SfPunctualEigenvalue D l hl Ω Y₀ G y α := by
  obtain ⟨L, K, ⟨a⟩, ι, hι, hα⟩ := h
  exact ⟨L, K, ⟨((ObjectProperty.ι _).mapIso e).symm ≪≫ a⟩, ι, hι, hα⟩

private theorem punctualPure_of_iso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (iota : Ω →+* ℂ) (w : ℝ)
    {F G : sfCommonStageWeilSheaf D l hl Y₀ Ω} (e : F ≅ G)
    (h : SfIsPunctuallyPureOfWeight D l hl Ω Y₀ iota F w) :
    SfIsPunctuallyPureOfWeight D l hl Ω Y₀ iota G w := by
  intro y α hα
  exact h y α (punctualEigenvalue_of_iso D l hl Ω Y₀ e.symm y α hα)

private theorem mixed_of_iso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (iota : Ω →+* ℂ) (w : ℝ)
    {F G : sfCommonStageWeilSheaf D l hl Y₀ Ω} (e : F ≅ G)
    (h : SfIsMixedOfWeightsAtMost D l hl Ω Y₀ iota F w) :
    SfIsMixedOfWeightsAtMost D l hl Ω Y₀ iota G w := by
  obtain ⟨m, A, φ, h0, ⟨a⟩, hmono, hpure⟩ := h
  exact ⟨m, A, φ, h0, ⟨a ≪≫ e⟩, hmono, hpure⟩

private theorem mixed_map
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (H : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤ sfCommonStageWeilSheaf D l hl Y₀ Ω)
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (iota : Ω →+* ℂ)
    (hp : ∀ (A : sfCommonStageWeilSheaf D l hl X₀ Ω) (v : ℝ),
      SfIsPunctuallyPureOfWeight D l hl Ω X₀ iota A v →
        SfIsPunctuallyPureOfWeight D l hl Ω Y₀ iota (H.obj A) v)
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) (w : ℝ)
    (h : SfIsMixedOfWeightsAtMost D l hl Ω X₀ iota F w) :
    SfIsMixedOfWeightsAtMost D l hl Ω Y₀ iota (H.obj F) w := by
  obtain ⟨m, A, φ, h0, ⟨a⟩, hmono, hpure⟩ := h
  refine ⟨m, fun i ↦ H.obj (A i), fun i ↦ H.map (φ i), H.map_isZero h0,
    ⟨H.mapIso a⟩, ?_, ?_⟩
  · intro i
    let := hmono i
    infer_instance
  · intro i
    obtain ⟨v, hv, hA⟩ := hpure i
    exact ⟨v, hv, punctualPure_of_iso D l hl Ω Y₀ iota v
      (PreservesCokernel.iso H (φ i)) (hp _ v hA)⟩

private theorem norm_le_of_pow
    {Ω : Type v} [Field Ω] (iota : Ω →+* ℂ) (β : Ω)
    (Q : ℕ) (e : ℕ) (he : e ≠ 0) (w : ℝ)
    (h : ‖iota (β ^ e)‖ ≤ ((Q ^ e : ℕ) : ℝ) ^ (w / 2)) :
    ‖iota β‖ ≤ (Q : ℝ) ^ (w / 2) := by
  rw [map_pow, norm_pow, Nat.cast_pow,
    ← Real.rpow_pow_comm (Nat.cast_nonneg Q)] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg Q) _)
    he).mp h

private theorem norm_eq_of_pow
    {Ω : Type v} [Field Ω] (iota : Ω →+* ℂ) (β : Ω)
    (Q : ℕ) (e : ℕ) (he : e ≠ 0) (w : ℝ)
    (h : ‖iota (β ^ e)‖ = ((Q ^ e : ℕ) : ℝ) ^ (w / 2)) :
    ‖iota β‖ = (Q : ℝ) ^ (w / 2) := by
  rw [map_pow, norm_pow, Nat.cast_pow,
    ← Real.rpow_pow_comm (Nat.cast_nonneg Q)] at h
  exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg Q) _)
    he).mp h

private theorem exists_finite_compactification
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (hqf : Scheme.Hom.IsQuasiFinite f) :
    ∃ c : Compactification f, IsFinite c.g := by
  let := hqf.1
  let := hqf.2.1
  have : LocallyQuasiFinite f := by
    apply locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr
    intro y
    rw [isDiscrete_iff_discreteTopology]
    apply discreteTopology_iff_isOpen_singleton.mpr
    rintro ⟨x, hx⟩
    change f x = y at hx
    subst y
    simpa only [Set.image_singleton, Scheme.Hom.asFiber,
      Homeomorph.apply_symm_apply] using
      (f.fiberHomeo (f x)).isOpenMap _ (hqf.2.2 x)
  obtain ⟨T, j, p, hj, _, hp, h⟩ :=
    f.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  exact ⟨{ Z := T
           i := j
           g := p
           comm := h.symm
           isOpenImmersion := hj
           isProper := inferInstance }, hp⟩

/-- A separated quasi-finite morphism has no positive compact-support higher images;
its degree-zero image preserves mixed and punctual upper weight bounds.
Source: blueprint main-20261015, sk-l-dl-general-quasifinite, unit statement and
finite-fibre argument (blueprint: sk-l-dl-general-quasifinite).

Proof:

1. Translate point-isolation quasi-finiteness into Mathlib local quasi-finiteness.
   The target is quasi-compact and quasi-separated. Zariski Main Theorem gives an
   open immersion followed by a finite morphism, hence a finite compactification.
   This does not imply absolute separatedness: the identity of the doubled-origin
   affine line is finite. All comparisons retain the relative hypotheses.

2. Apply sfFiniteCompactificationWeilExact to this compactification. It supplies
   one additive exact heart functor H, objectwise Weil isomorphisms from H to the
   specified zeroth higher image, and positive-degree vanishing. Compactification
   independence transports the latter to the supplied compactification c.

3. Apply sfFiniteCompactificationEigenvalues to every eigenvalue beta of H(A).
   It gives a source eigenvalue beta^e at x, with e nonzero and q_x = q_y^e.
   For the given embedding iota, multiplicativity gives |iota(beta)|^e equal to
   |iota(beta^e)|. The source upper bound therefore bounds this by
   (q_y^(w/2))^e. Injectivity and monotonicity of the positive integral power on
   nonnegative reals give the desired bound. The equality argument gives purity.
   Neither argument needs surjectivity of iota, and both allow every real weight.

4. Send the input global mixed filtration through the same H. Exactness preserves
   its initial zero object and its monomorphisms, and the preserved-cokernel
   isomorphisms identify its quotients with H of the original pure quotients.
   Step 3 proves their purity at the same weights. Compose the final isomorphism
   with the comparison to the specified zeroth image for c. Isomorphism invariance
   of eigenvalue and mixed predicates follows directly by composing finite Weil
   presentations and final filtration isomorphisms. Length-zero filtrations use
   the same construction.
-/
theorem sfQuasiFiniteCompactSupport
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] (_hqf : Scheme.Hom.IsQuasiFinite f₀.left)
    (c : Compactification f₀.left) (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    (∀ i : ℕ, 0 < i → IsZero (zlWeilHigherShriek D l hl Ω f₀ c i F)) ∧
      ∀ (iota : Ω →+* ℂ) (w : ℝ),
        (SfIsMixedOfWeightsAtMost D l hl Ω X₀ iota F w →
          SfIsMixedOfWeightsAtMost D l hl Ω Y₀ iota
            (zlWeilHigherShriek D l hl Ω f₀ c 0 F) w) ∧
        ((∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left}) (α : Ω),
            SfPunctualEigenvalue D l hl Ω X₀ F x α →
              ‖iota α‖ ≤ (Nat.card (X₀.left.residueField x.val) : ℝ) ^ (w / 2)) →
          ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (β : Ω),
            SfPunctualEigenvalue D l hl Ω Y₀
                (zlWeilHigherShriek D l hl Ω f₀ c 0 F) y β →
              ‖iota β‖ ≤ (Nat.card (Y₀.left.residueField y.val) : ℝ) ^ (w / 2)) := by
  let : CompactSpace Y₀.left :=
    QuasiCompact.compactSpace_of_compactSpace Y₀.hom
  let : QuasiSeparatedSpace Y₀.left :=
    quasiSeparatedSpace_of_quasiSeparated Y₀.hom
  obtain ⟨c', hc'⟩ := exists_finite_compactification f₀.left _hqf
  let := hc'
  obtain ⟨H, hHadd, hHlim, hHcolim, hHobj, hHvanish⟩ :=
    sfFiniteCompactificationWeilExact D l hl Ω f₀ c'
  let := hHadd
  let := hHlim
  let := hHcolim
  have compare (A : sfCommonStageWeilSheaf D l hl X₀ Ω) :
      Nonempty (H.obj A ≅ zlWeilHigherShriek D l hl Ω f₀ c 0 A) := by
    obtain ⟨a⟩ := hHobj A
    obtain ⟨b⟩ := zlWeilHigherShriek_compactification_independent D l hl Ω f₀ c' c 0 A
    exact ⟨a ≪≫ b⟩
  have spectrum (A : sfCommonStageWeilSheaf D l hl X₀ Ω)
      (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) (β : Ω)
      (hβ : SfPunctualEigenvalue D l hl Ω Y₀ (H.obj A) y β) :
      ∃ (x : {x : X₀.left // x ∈ closedPoints X₀.left}) (e : ℕ),
        e ≠ 0 ∧ Nat.card (X₀.left.residueField x.val) =
          Nat.card (Y₀.left.residueField y.val) ^ e ∧
        SfPunctualEigenvalue D l hl Ω X₀ A x (β ^ e) := by
    obtain ⟨a⟩ := hHobj A
    obtain ⟨x, e, _, he, hcard, hx⟩ := sfFiniteCompactificationEigenvalues
      D l hl Ω f₀ c' A y β (punctualEigenvalue_of_iso D l hl Ω Y₀ a y β hβ)
    exact ⟨x, e, he, hcard, hx⟩
  refine ⟨?_, ?_⟩
  · intro i hi
    obtain ⟨a⟩ := zlWeilHigherShriek_compactification_independent D l hl Ω f₀ c c' i F
    exact (hHvanish F i hi).of_iso a
  · intro iota w
    refine ⟨?_, ?_⟩
    · intro hF
      obtain ⟨a⟩ := compare F
      apply mixed_of_iso D l hl Ω Y₀ iota w a
      apply mixed_map D l hl Ω X₀ Y₀ H iota ?_ F w hF
      intro A v hA y β hβ
      obtain ⟨x, e, he, hcard, hx⟩ := spectrum A y β hβ
      have h := hA x (β ^ e) hx
      rw [hcard] at h
      exact norm_eq_of_pow iota β _ e he v h
    · intro hF y β hβ
      obtain ⟨a⟩ := compare F
      obtain ⟨x, e, he, hcard, hx⟩ := spectrum F y β
        (punctualEigenvalue_of_iso D l hl Ω Y₀ a.symm y β hβ)
      have h := hF x (β ^ e) hx
      rw [hcard] at h
      exact norm_le_of_pow iota β _ e he w h

end WeilConjectures
