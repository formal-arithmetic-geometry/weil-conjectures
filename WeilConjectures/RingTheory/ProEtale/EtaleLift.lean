/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.Etale.Basic

/-!
# Lifting étale algebras along a quotient

Let `R` be a ring, `J ⊆ R` an ideal and `S` an étale `R ⧸ J`-algebra. Choosing a submersive
presentation `S = (R ⧸ J)[x₁, …, xₘ] ⧸ (f̄₁, …, f̄ₘ)` (which exists since `S` is
étale, see `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`) and coefficientwise
lifts `fᵢ` of the relations, the algebra
`Algebra.EtaleLift J P = (R[x₁, …, xₘ] ⧸ (f₁, …, fₘ))_Δ`, where `Δ` is the Jacobian
determinant of the `fᵢ`, is étale over `R` and reduces to `S` modulo `J` (Stacks 04D1).
No nilpotence assumption on `J` is needed.

## Main results

- `Algebra.EtaleLift`: the lift of a submersive presentation (blueprint
  `def-exc-etale-algebra-lift`).
- `Algebra.Etale.exists_lift`: every étale `R ⧸ J`-algebra is the reduction of an étale
  `R`-algebra (blueprint `lem-exc-etale-algebra-lift`).
-/

@[expose] public section

universe u

open MvPolynomial

namespace Algebra.EtaleLift

variable {R : Type u} [CommRing R] (J : Ideal R) {S : Type*} [CommRing S] [Algebra (R ⧸ J) S]
  {ι σ : Type} [Finite σ] (P : SubmersivePresentation (R ⧸ J) S ι σ)

/-- Coefficientwise lifts to `R[xᵢ]` of the relations of a presentation over `R ⧸ J`. -/
noncomputable def relation (j : σ) : MvPolynomial ι R :=
  Function.surjInv (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective) (P.relation j)

lemma map_relation (j : σ) :
    MvPolynomial.map (Ideal.Quotient.mk J) (relation J P j) = P.relation j :=
  Function.surjInv_eq _ _

/-- The quotient `R[xᵢ] ⧸ (fⱼ)` by the lifted relations. -/
abbrev Base : Type u := MvPolynomial ι R ⧸ Ideal.span (Set.range (relation J P))

/-- The naive pre-submersive presentation of `Base J P`. -/
noncomputable def basePresentation : PreSubmersivePresentation R (Base J P) ι σ :=
  PreSubmersivePresentation.naive P.map P.map_inj

/-- The Jacobian determinant `Δ` of the lifted relations, in `Base J P`. -/
noncomputable def jacobian : Base J P := (basePresentation J P).jacobian

end Algebra.EtaleLift

open Algebra.EtaleLift in
/-- Blueprint `def-exc-etale-algebra-lift`: lifting a Jacobian presentation. For a submersive
presentation `P` of an `R ⧸ J`-algebra with lifted relations `fⱼ` and Jacobian determinant `Δ`,
this is `(R[xᵢ] ⧸ (fⱼ))_Δ = R[xᵢ, t] ⧸ (fⱼ, tΔ - 1)`. -/
abbrev Algebra.EtaleLift {R : Type u} [CommRing R] (J : Ideal R) {S : Type*} [CommRing S]
    [Algebra (R ⧸ J) S] {ι σ : Type} [Finite σ]
    (P : Algebra.SubmersivePresentation (R ⧸ J) S ι σ) :
    Type u :=
  Localization.Away (jacobian J P)

namespace Algebra.EtaleLift

variable {R : Type u} [CommRing R] (J : Ideal R) {S : Type*} [CommRing S] [Algebra (R ⧸ J) S]
  {ι σ : Type} [Finite σ] (P : SubmersivePresentation (R ⧸ J) S ι σ)

/-- The submersive presentation of `EtaleLift J P`. -/
noncomputable def presentation :
    SubmersivePresentation R (EtaleLift J P) (Unit ⊕ ι) (Unit ⊕ σ) where
  __ := (PreSubmersivePresentation.localizationAway (EtaleLift J P) (jacobian J P)).comp
    (basePresentation J P)
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def, ← map_mul]
    exact IsLocalization.map_units _ (⟨jacobian J P * jacobian J P, 2, by simp [pow_two]⟩ :
      Submonoid.powers (jacobian J P))

lemma etale [Finite ι] (hP : P.dimension = 0) : Algebra.Etale R (EtaleLift J P) := by
  rw [Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero]
  refine (presentation J P).isStandardSmoothOfRelativeDimension ?_
  rw [presentation, PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  simpa [Algebra.Presentation.dimension] using hP

variable [Algebra R S] [IsScalarTower R (R ⧸ J) S]

lemma aeval_relation (j : σ) : aeval P.val (relation J P j) = 0 := by
  rw [← MvPolynomial.aeval_map_algebraMap (R ⧸ J), Ideal.Quotient.algebraMap_eq, map_relation]
  exact P.aeval_val_relation j

/-- The map `R[xᵢ] ⧸ (fⱼ) → S`. -/
noncomputable def baseToAlgHom : Base J P →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aeval P.val) fun g hg ↦ by
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact aeval_relation J P j
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]

lemma baseToAlgHom_mk (g : MvPolynomial ι R) :
    baseToAlgHom J P (Ideal.Quotient.mk _ g) = aeval P.val g := rfl

lemma baseToAlgHom_jacobian : baseToAlgHom J P (jacobian J P) = P.jacobian := by
  classical
  cases nonempty_fintype σ
  rw [jacobian, PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply,
    Ideal.Quotient.algebraMap_eq]
  erw [baseToAlgHom_mk]
  rw [AlgHom.map_det, AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, basePresentation,
    PreSubmersivePresentation.jacobiMatrix_naive, P.jacobiMatrix_apply, ← map_relation J P j,
    MvPolynomial.pderiv_map, ← Ideal.Quotient.algebraMap_eq, MvPolynomial.aeval_map_algebraMap]

/-- The map `EtaleLift J P → S`, sending `xᵢ` to the generators of `S`. -/
noncomputable def toAlgHom : EtaleLift J P →ₐ[R] S :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (jacobian J P)) (f := baseToAlgHom J P) <| by
    rintro ⟨_, n, rfl⟩
    rw [map_pow, baseToAlgHom_jacobian]
    exact P.jacobian_isUnit.pow n

lemma toAlgHom_algebraMap (y : Base J P) :
    toAlgHom J P (algebraMap _ _ y) = baseToAlgHom J P y :=
  IsLocalization.lift_eq _ _

lemma aeval_val_surjective : Function.Surjective (aeval (R := R) P.val) := by
  intro s
  obtain ⟨g, rfl⟩ := P.aeval_val_surjective s
  obtain ⟨g, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective g
  exact ⟨g, by rw [← Ideal.Quotient.algebraMap_eq, MvPolynomial.aeval_map_algebraMap]⟩

lemma toAlgHom_surjective : Function.Surjective (toAlgHom J P) := by
  intro s
  obtain ⟨g, rfl⟩ := aeval_val_surjective J P s
  exact ⟨algebraMap _ _ (Ideal.Quotient.mk _ g), by rw [toAlgHom_algebraMap, baseToAlgHom_mk]⟩

lemma ker_aeval_le : RingHom.ker (aeval (R := R) P.val) ≤
    Ideal.span (Set.range (relation J P)) ⊔ J.map C := by
  intro g hg
  have hmem : MvPolynomial.map (Ideal.Quotient.mk J) g ∈
      Ideal.map (MvPolynomial.map (Ideal.Quotient.mk J))
        (Ideal.span (Set.range (relation J P))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    have h : (MvPolynomial.map (Ideal.Quotient.mk J)) ∘ relation J P = P.relation :=
      funext (map_relation J P)
    rw [h, P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val, RingHom.mem_ker,
      ← Ideal.Quotient.algebraMap_eq, MvPolynomial.aeval_map_algebraMap]
    exact hg
  rwa [← Ideal.mem_comap,
    Ideal.comap_map_of_surjective (MvPolynomial.map (Ideal.Quotient.mk J))
      (map_surjective _ Ideal.Quotient.mk_surjective),
    ← RingHom.ker_eq_comap_bot, MvPolynomial.ker_map, Ideal.mk_ker] at hmem

lemma ker_baseToAlgHom :
    RingHom.ker (baseToAlgHom J P) = J.map (algebraMap R (Base J P)) := by
  refine le_antisymm (fun y hy ↦ ?_) ?_
  · obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span (Set.range (relation J P))))
      (ker_aeval_le J P hy)
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_map] at this
    exact this
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes,
      IsScalarTower.algebraMap_apply R (R ⧸ J) S, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

lemma ker_toAlgHom :
    RingHom.ker (toAlgHom J P) = J.map (algebraMap R (EtaleLift J P)) := by
  refine le_antisymm (fun s hs ↦ ?_) ?_
  · obtain ⟨⟨y, m⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers (jacobian J P)) s
    dsimp only at hs ⊢
    have hy : y ∈ RingHom.ker (baseToAlgHom J P) := by
      rw [RingHom.mem_ker, ← toAlgHom_algebraMap, ← IsLocalization.mk'_spec (EtaleLift J P) y m,
        map_mul, RingHom.mem_ker.1 hs, zero_mul]
    rw [ker_baseToAlgHom] at hy
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    refine Ideal.mul_mem_right _ _ ?_
    have := Ideal.mem_map_of_mem (algebraMap (Base J P) (EtaleLift J P)) hy
    rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at this
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes,
      IsScalarTower.algebraMap_apply R (R ⧸ J) S, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

/-- The reduction isomorphism `EtaleLift J P ⧸ J ≃ S`. -/
noncomputable def reductionEquiv :
    (EtaleLift J P ⧸ J.map (algebraMap R (EtaleLift J P))) ≃ₐ[R] S :=
  (Ideal.quotientEquivAlgOfEq R (ker_toAlgHom J P).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (toAlgHom_surjective J P))

end Algebra.EtaleLift

/-- Blueprint `lem-exc-etale-algebra-lift`: etale algebras lift across an arbitrary quotient. -/
theorem Algebra.Etale.exists_lift {R : Type u} [CommRing R] (J : Ideal R) (S : Type*)
    [CommRing S] [Algebra (R ⧸ J) S] [Algebra R S] [IsScalarTower R (R ⧸ J) S]
    [Algebra.Etale (R ⧸ J) S] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra.Etale R T) (f : T →ₐ[R] S),
      Function.Surjective f ∧ RingHom.ker f = J.map (algebraMap R T) := by
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp ‹_›).out
  exact ⟨Algebra.EtaleLift J P, inferInstance, inferInstance, Algebra.EtaleLift.etale J P hP,
    Algebra.EtaleLift.toAlgHom J P, Algebra.EtaleLift.toAlgHom_surjective J P,
    Algebra.EtaleLift.ker_toAlgHom J P⟩
