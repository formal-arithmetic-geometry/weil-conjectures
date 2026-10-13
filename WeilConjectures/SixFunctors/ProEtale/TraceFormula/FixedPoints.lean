/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FrobeniusFixedPointsCount
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius

/-!
# Fixed points of the model Frobenius

Let `X = X₀ ×_k Ω` be the geometric base change of a scheme `X₀` over a finite field `k` with
`q` elements, `Ω` algebraically closed, with Frobenius `Φ₁` the base change of the `q`-power
Frobenius of `X₀` (`AlgebraicGeometry.ProEtale.WeilComplex.IsModelFrobenius`). The sections
`x : Spec Ω ⟶ X` of `a_X` fixed by `Φ_m`, `m ≥ 1`, correspond via `x ↦ x ≫ p` to the
`Ω`-points of `X₀` fixed by the `q^m`-power map of `Ω`, that is, to `X₀(𝔽_{q^m})`. Hence they
are finite in number, each lies over a closed point of `X₀` whose degree divides `m`, and a
closed point `y` of degree dividing `m` carries exactly `deg y` of them.

## Main statements

- `AlgebraicGeometry.ProEtale.WeilComplex.IsModelFrobenius.finite_fixedPoints`: finiteness of
  the fixed sections.
- `AlgebraicGeometry.ProEtale.WeilComplex.IsModelFrobenius.mem_finitePoints_of_fixedPoint`: a
  fixed section lies over a closed point of degree dividing `m`.
- `AlgebraicGeometry.ProEtale.WeilComplex.IsModelFrobenius.sum_fixedPoints`: a sum over the fixed
  sections of a function of the underlying closed point is `∑_{deg y ∣ m} deg y • h y`.

## Blueprint

These are the parts of `thm-trf-frobenius-fixed-points` used for the Euler product form of the
trace formula.
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.WeilComplex

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}} {Ω : Type u} [Field Ω]
  {aX : X ⟶ Spec (.of Ω)} {W : WeilComplex (A := A) aX} {k : Type u} [Field k]
  {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k)} {σ : Spec (.of Ω) ⟶ Spec (.of k)} {p : X ⟶ X₀}

section Algebra

variable [Fintype k] [Algebra k Ω]

/-- On `Ω`-points, the iterate `Φ_m` of the model Frobenius followed by `p` is the `q^m`-power
map of `Ω`: `t ≫ Φ_m ≫ p = Spec (x ↦ x ^ (q ^ m)) ≫ t ≫ p`. -/
lemma IsModelFrobenius.comp_frobeniusIterate_comp (hΦ : W.IsModelFrobenius f₀ σ p) (m : ℕ)
    (t : Spec (.of Ω) ⟶ X) :
    t ≫ W.frobeniusIterate m ≫ p = Spec.map (CommRingCat.ofHom
      ((FiniteField.frobeniusAlgHom k Ω ^ m : Ω →ₐ[k] Ω) : Ω →+* Ω)) ≫ t ≫ p := by
  obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
  induction m generalizing t with
  | zero =>
    have h1 : CommRingCat.ofHom ((FiniteField.frobeniusAlgHom k Ω ^ 0 : Ω →ₐ[k] Ω) :
        Ω →+* Ω) = 𝟙 _ := by
      ext a
      simp
    rw [frobeniusIterate_zero, Category.id_comp, h1, Spec.map_id, Category.id_comp]
  | succ m ih =>
    have hφ := hF₀ (t ≫ p) (CommRingCat.ofHom
      ((FiniteField.frobeniusAlgHom k Ω : Ω →ₐ[k] Ω) : Ω →+* Ω))
      fun r ↦ by simp [Nat.card_eq_fintype_card]
    have hcomp : CommRingCat.ofHom ((FiniteField.frobeniusAlgHom k Ω : Ω →ₐ[k] Ω) :
        Ω →+* Ω) ≫ CommRingCat.ofHom ((FiniteField.frobeniusAlgHom k Ω ^ m : Ω →ₐ[k] Ω) :
        Ω →+* Ω) = CommRingCat.ofHom ((FiniteField.frobeniusAlgHom k Ω ^ (m + 1) :
        Ω →ₐ[k] Ω) : Ω →+* Ω) := by
      ext a
      simp [pow_succ]
    rw [frobeniusIterate_succ, Category.assoc, ← Category.assoc t, ih, Category.assoc, hp,
      ← Category.assoc t, hφ, ← hcomp, Spec.map_comp, Category.assoc]


/-- The sections of `a_X` fixed by `Φ_m` correspond, via `x ↦ x ≫ p`, to the `Ω`-points of `X₀`
over `k` fixed by the `q^m`-power map of `Ω`, the `k`-algebra structure of `Ω` being the one
given by `σ`. -/
noncomputable def IsModelFrobenius.fixedPointsEquiv (hΦ : W.IsModelFrobenius f₀ σ p)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap k Ω)) = σ) (m : ℕ) :
    {x : Spec (.of Ω) ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x} ≃
      f₀.fixedFieldPoints ((FiniteField.frobeniusAlgHom k Ω ^ m : Ω →ₐ[k] Ω) : Ω →+* Ω) :=
  Equiv.ofBijective
    (fun x ↦ ⟨x.1 ≫ p, (f₀.mem_fixedFieldPoints_iff _ _).2
      ⟨by rw [Category.assoc, hΦ.isPullback.w, ← Category.assoc, x.2.1, Category.id_comp, hσ],
        by rw [← hΦ.comp_frobeniusIterate_comp, ← Category.assoc, x.2.2]⟩⟩)
    ⟨fun x₁ x₂ h ↦ Subtype.ext (hΦ.isPullback.hom_ext (congrArg Subtype.val h)
      (by rw [x₁.2.1, x₂.2.1])), fun g ↦ by
      obtain ⟨hg₁, hg₂⟩ := (f₀.mem_fixedFieldPoints_iff _ _).1 g.2
      have w : g.1 ≫ f₀ = 𝟙 _ ≫ σ := by rw [hg₁, hσ, Category.id_comp]
      refine ⟨⟨hΦ.isPullback.lift g.1 (𝟙 _) w, hΦ.isPullback.lift_snd _ _ w,
        hΦ.isPullback.hom_ext ?_ ?_⟩, Subtype.ext (hΦ.isPullback.lift_fst _ _ w)⟩
      · rw [Category.assoc, hΦ.comp_frobeniusIterate_comp, hΦ.isPullback.lift_fst, hg₂]
      · rw [Category.assoc, frobeniusIterate_comp]⟩

end Algebra

variable [Finite k] [IsAlgClosed Ω]

/-- The sections of `a_X` fixed by `Φ_m`, `m ≥ 1`, are finite in number (they are the points of
`X₀` rational over `𝔽_{q^m}`). Blueprint `thm-trf-frobenius-fixed-points` (finiteness). -/
theorem IsModelFrobenius.finite_fixedPoints (hΦ : W.IsModelFrobenius f₀ σ p) [QuasiCompact f₀]
    [LocallyOfFiniteType f₀] {m : ℕ} (hm : m ≠ 0) :
    Finite {x : Spec (.of Ω) ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x} := by
  let := Fintype.ofFinite k
  let : Algebra k Ω := (Spec.preimage σ).hom.toAlgebra
  have := (f₀.finite_fixedFieldPoints hm
    ((FiniteField.frobeniusAlgHom k Ω ^ m : Ω →ₐ[k] Ω) : Ω →+* Ω) fun a ↦ by
    rw [AlgHom.coe_toRingHom, FiniteField.coe_frobeniusAlgHom_pow,
      Nat.card_eq_fintype_card]).to_subtype
  exact Finite.of_equiv _ (hΦ.fixedPointsEquiv (Spec.map_preimage σ) m).symm

/-- A section `x` of `a_X` fixed by `Φ_m`, `m ≥ 1`, lies over a closed point of `X₀` whose
degree divides `m`. Blueprint `thm-trf-frobenius-fixed-points` (image of a fixed point). -/
theorem IsModelFrobenius.mem_finitePoints_of_fixedPoint (hΦ : W.IsModelFrobenius f₀ σ p)
    {m : ℕ} (hm : m ≠ 0) {x : Spec (.of Ω) ⟶ X} (hx : x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x) :
    (x ≫ p).base default ∈ X₀.finitePoints ∧ f₀.degreeOver ((x ≫ p).base default) ∣ m := by
  let := Fintype.ofFinite k
  let : Algebra k Ω := (Spec.preimage σ).hom.toAlgebra
  exact f₀.mem_finitePoints_of_mem_fixedFieldPoints hm
    ((FiniteField.frobeniusAlgHom k Ω ^ m : Ω →ₐ[k] Ω) : Ω →+* Ω) (fun a ↦ by
    rw [AlgHom.coe_toRingHom, FiniteField.coe_frobeniusAlgHom_pow, Nat.card_eq_fintype_card])
    (hΦ.fixedPointsEquiv (Spec.map_preimage σ) m ⟨x, hx⟩).2

/-- **Counting fixed points.** For a function `h` on the points of `X₀` and `m ≥ 1`, the sum of
`h` over the closed points underlying the sections of `a_X` fixed by `Φ_m` is
`∑_{deg y ∣ m} deg y • h y`: a closed point `y` of degree dividing `m` carries `deg y` fixed
sections, and the other points none. The sum may be taken over any finite set `T` of closed
points containing those of degree dividing `m`. Blueprint `thm-trf-frobenius-fixed-points`
(counting). -/
theorem IsModelFrobenius.sum_fixedPoints (hΦ : W.IsModelFrobenius f₀ σ p) {m : ℕ} (hm : m ≠ 0)
    [Fintype {x : Spec (.of Ω) ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x}]
    {M : Type*} [AddCommMonoid M] (h : X₀ → M) {T : Finset X₀.finitePoints}
    (hT : ∀ y : X₀.finitePoints, f₀.degreeOver y.1 ∣ m → y ∈ T) :
    ∑ x : {x : Spec (.of Ω) ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x},
        h ((x.1 ≫ p).base default) =
      ∑ y ∈ T with f₀.degreeOver y.1 ∣ m, f₀.degreeOver y.1 • h y.1 := by
  let := Fintype.ofFinite k
  let : Algebra k Ω := (Spec.preimage σ).hom.toAlgebra
  let e := hΦ.fixedPointsEquiv (Spec.map_preimage σ) m
  let := Fintype.ofEquiv _ e
  rw [← f₀.sum_fixedFieldPoints hm
    ((FiniteField.frobeniusAlgHom k Ω ^ m : Ω →ₐ[k] Ω) : Ω →+* Ω) (fun a ↦ by
    rw [AlgHom.coe_toRingHom, FiniteField.coe_frobeniusAlgHom_pow, Nat.card_eq_fintype_card])
    h hT]
  exact Fintype.sum_equiv e _ _ fun x ↦ rfl

end AlgebraicGeometry.ProEtale.WeilComplex
