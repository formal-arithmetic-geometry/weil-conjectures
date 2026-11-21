/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.LinearForm
public import WeilConjectures.WeilSheaf.ArtinSchreierMul
public import WeilConjectures.WeilSheaf.FourierInversion.ConvolutionKernel
public import WeilConjectures.WeilSheaf.FourierInversion.Vanishing
public import WeilConjectures.WeilSheaf.LowerShriekOperations
public import WeilConjectures.WeilSheaf.VerdierDualLocalization
public import WeilConjectures.WeilSheaf.WeilAffineSpaceBundleTrace

/-!
# Integrating a linear character over affine space

Let `λ = ∑ᵢ cᵢ xᵢ` be a linear form on `𝔸ⁿ` over the finite field `k₀`, with coefficients
`cᵢ ∈ k₀`, `p : 𝔸ⁿ ⟶ Spec k₀` the structure morphism and `ℒ_{ψ,λ} = λ^* ℒ_ψ` the
Artin–Schreier sheaf of `λ`. This file computes the compactly supported cohomology
`Rp₀! ℒ_{ψ,λ}` as a Weil complex on `Spec k₀`:

* if `λ = 0`, then `Rp₀! ℒ_{ψ,λ} ≅ ℚ̄_ℓ(-r)[-2r]` with `r = #n`;
* if `λ ≠ 0` and `ψ` is nontrivial, then `Rp₀! ℒ_{ψ,λ} = 0`.

## Main definitions

- `AlgebraicGeometry.AffineSpace.linearFunction`: the linear form `∑ᵢ cᵢ xᵢ` on `𝔸ⁿ_{k₀}`.

## Main statements

- `AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_artinSchreierOf_linearFunction`:
  `Rp₀! ℒ_{ψ,0} ≅ ℚ̄_ℓ(-r)[-2r]`.
- `AlgebraicGeometry.WeilComplex.isZero_derivedLowerShriek_artinSchreierOf_linearFunction`:
  `Rp₀! ℒ_{ψ,λ} = 0` for `λ ≠ 0` and `ψ` nontrivial.

## Implementation details

For `λ = 0`, `ℒ_{ψ,0} ≅ ℚ̄_ℓ = p^* ℚ̄_ℓ` and `Rp₀! p^* ≅ (-r)[-2r]` (the standard affine-space
trace, `WeilComplex.nonempty_iso_upperStar_comp_derivedLowerShriek_affineSpace_of_isPullback`).
For `cᵢ ≠ 0`, the linear change of variables `AlgebraicGeometry.AffineSpace.linearCoordHom`
presents `𝔸ⁿ` as the trivial line bundle `π : 𝔸ⁿ ⟶ 𝔸^{n ∖ {i}}` with fibre coordinate `λ`, so
`Rπ₀! ℒ_{ψ,λ} = 0` by relative vanishing
(`AlgebraicGeometry.WeilComplex.isZero_derivedLowerShriek_tensorLisse_artinSchreierOf_upperStar`),
and `Rp₀! ≅ Rq₀! ∘ Rπ₀!` for `q : 𝔸^{n ∖ {i}} ⟶ Spec k₀`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace AffineSpace

variable {n : Type u} [Fintype n]

variable (k₀) in
/-- The linear form `x ↦ ∑ᵢ cᵢ xᵢ` on `𝔸ⁿ` over `k₀`, with coefficients `c : n → k₀`. -/
noncomputable def linearFunction (c : n → k₀) : Γ(𝔸(n; Spec (CommRingCat.of k₀)), ⊤) :=
  ∑ i, coord _ i * (𝔸(n; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of k₀)).inv.hom (c i))

omit [Finite k₀] in
@[simp]
lemma linearFunction_zero : linearFunction k₀ (0 : n → k₀) = 0 := by
  simp [linearFunction]

omit [Finite k₀] in
/-- `linearFunction` is the linear form `AffineSpace.linearForm` along `𝟙 (Spec k₀)`, read on
`𝔸ⁿ` through the isomorphism `𝔸ⁿ ×_{k₀} k₀ ≅ 𝔸ⁿ`. -/
lemma linearFunction_eq_appTop_linearForm (c : n → k₀) :
    linearFunction k₀ c = (inv (pullback.fst (𝔸(n; Spec (CommRingCat.of k₀)) ↘
      Spec (CommRingCat.of k₀)) (𝟙 _))).appTop (linearForm (𝟙 _)
        fun j ↦ (Scheme.ΓSpecIso (CommRingCat.of k₀)).inv.hom (c j)) := by
  set p := 𝔸(n; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)
  have hsnd : inv (pullback.fst p (𝟙 _)) ≫ pullback.snd p (𝟙 _) = p := by
    rw [IsIso.inv_comp_eq, ← Category.comp_id (pullback.snd _ _), ← pullback.condition]
  rw [linearForm, map_sum, linearFunction]
  refine (Finset.sum_congr rfl fun j _ ↦ ?_).symm
  rw [map_mul, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, IsIso.inv_hom_id, hsnd, Scheme.Hom.id_appTop,
    CommRingCat.id_apply]

end AffineSpace

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The Artin–Schreier sheaf `ℒ_{ψ,f}` placed in degree zero is the tensor product of `ℒ_{ψ,f}`
with the constant Weil complex `ℚ̄_ℓ`: `ℒ_{ψ,f} ⊗ ℚ̄_ℓ ≅ ℒ_{ψ,f} ⊗ ℒ_{ψ,0} ≅ ℒ_{ψ,f}`. -/
theorem nonempty_toComplex_artinSchreierOf_iso_tensorLisse (ψ : AddChar k₀ (PadicAlgCl l))
    (f : Γ(X, ⊤)) :
    Nonempty (WeilSheaf.toComplex.obj (artinSchreierOf ψ f) ≅
      (WeilComplex.tensorLisse (artinSchreierOf ψ f) (isLisse_artinSchreierOf ψ f)).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X))) := by
  obtain ⟨e₀⟩ := nonempty_iso_artinSchreierOf_zero (k₀ := k₀) (l := l) (X := X) ψ
  obtain ⟨e⟩ := nonempty_iso_tensorObj_artinSchreierOf ψ f 0
  rw [add_zero] at e
  exact ⟨WeilSheaf.toComplex.mapIso e.symm ≪≫
    (WeilComplex.tensorLisseToComplexIso _ _ _).symm ≪≫
    (WeilComplex.tensorLisse _ _).mapIso (WeilSheaf.toComplex.mapIso e₀)⟩

end WeilSheaf

namespace WeilComplex

variable {n : Type u} [Fintype n]

/-- For the zero linear form `λ = ∑ᵢ cᵢ xᵢ`, `c = 0`, on `𝔸ⁿ` over `k₀` with structure morphism
`p`, the compactly supported cohomology of `ℒ_{ψ,λ}` is `Rp₀! ℒ_{ψ,λ} ≅ ℚ̄_ℓ(-r)[-2r]`, `r = #n`. -/
theorem nonempty_iso_derivedLowerShriek_artinSchreierOf_linearFunction
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty ((derivedLowerShriek k₀ l
        (𝔸(n; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))).obj
        (WeilSheaf.toComplex.obj
          (artinSchreierOf ψ (AffineSpace.linearFunction k₀ (0 : n → k₀)))) ≅
      ((tateTwist k₀ l (Spec (CommRingCat.of k₀)) (-(Fintype.card n : ℤ))).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))))⟦
          -(2 * (Fintype.card n : ℤ))⟧) := by
  rw [AffineSpace.linearFunction_zero]
  let p := 𝔸(n; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)
  obtain ⟨e₀⟩ := nonempty_iso_artinSchreierOf_zero (k₀ := k₀) (l := l)
    (X := 𝔸(n; Spec (CommRingCat.of k₀))) ψ
  obtain ⟨T⟩ := nonempty_iso_upperStar_comp_derivedLowerShriek_affineSpace_of_isPullback
    (k₀ := k₀) (l := l) n p (𝟙 _) (IsPullback.id_vert p)
  exact ⟨(derivedLowerShriek k₀ l p).mapIso (WeilSheaf.toComplex.mapIso e₀ ≪≫
    (upperStarAdicConstantIso p).symm) ≪≫ T.app _⟩

/-- For a nonzero linear form `λ = ∑ᵢ cᵢ xᵢ`, `c ≠ 0`, on `𝔸ⁿ` over `k₀` with structure
morphism `p`, and a nontrivial character `ψ`, the compactly supported cohomology of `ℒ_{ψ,λ}`
vanishes: `Rp₀! ℒ_{ψ,λ} = 0`. -/
theorem isZero_derivedLowerShriek_artinSchreierOf_linearFunction
    (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) {c : n → k₀} (hc : c ≠ 0) :
    IsZero ((derivedLowerShriek k₀ l
        (𝔸(n; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))).obj
        (WeilSheaf.toComplex.obj (artinSchreierOf ψ (AffineSpace.linearFunction k₀ c)))) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
  let S := Spec (CommRingCat.of k₀)
  let A := 𝔸(n; S)
  let B := 𝔸({j // j ≠ i}; S)
  let c' : n → Γ(S, ⊤) := fun j ↦ (Scheme.ΓSpecIso (CommRingCat.of k₀)).inv.hom (c j)
  have hc' : IsUnit (c' i) := (Ne.isUnit hi).map _
  have := AffineSpace.isIso_linearCoordHom (𝟙 S) hc'
  -- the linear change of variables `𝔸ⁿ ≅ 𝔸¹(𝔸^{n ∖ {i}})` making `λ` the fibre coordinate
  let e : A ⟶ 𝔸(PUnit.{u + 1}; B) :=
    inv (pullback.fst (A ↘ S) (𝟙 S)) ≫ AffineSpace.linearCoordHom (𝟙 S) c' i
  let π : A ⟶ B := e ≫ 𝔸(PUnit.{u + 1}; B) ↘ B
  let s : A ⟶ affineLine k₀ := e ≫ AffineSpace.map PUnit.{u + 1} (B ↘ S)
  have hsnd : inv (pullback.fst (A ↘ S) (𝟙 S)) ≫ pullback.snd (A ↘ S) (𝟙 S) = A ↘ S := by
    rw [IsIso.inv_comp_eq, ← Category.comp_id (pullback.snd _ _), ← pullback.condition]
  have hπS : π ≫ B ↘ S = A ↘ S := by
    simp only [π, e, Category.assoc]
    rw [AffineSpace.linearCoordHom_over]
    exact hsnd
  have : π.IsOver S := ⟨hπS⟩
  have hpb : IsPullback π s (B ↘ S) (affineLine k₀ ↘ S) := by
    have h₁ : IsPullback e π (𝔸(PUnit.{u + 1}; B) ↘ B) (𝟙 B) :=
      IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩
    simpa using (h₁.paste_horiz (AffineSpace.isPullback_map (n := PUnit.{u + 1}) (B ↘ S))).flip
  have hlin : π.appTop 1 * s.appTop (AffineSpace.coord _ PUnit.unit) =
      AffineSpace.linearFunction k₀ c := by
    rw [map_one, one_mul, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.map_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.linearCoordHom_appTop_coord]
    exact (AffineSpace.linearFunction_eq_appTop_linearForm c).symm
  have h₀ := isZero_derivedLowerShriek_tensorLisse_artinSchreierOf_upperStar ψ hψ π s hpb 1
    isUnit_one (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l B))
  rw [hlin] at h₀
  obtain ⟨E⟩ := WeilSheaf.nonempty_toComplex_artinSchreierOf_iso_tensorLisse (l := l) (X := A) ψ
    (AffineSpace.linearFunction k₀ c)
  have h₁ := h₀.of_iso ((derivedLowerShriek k₀ l π).mapIso
    (E ≪≫ (tensorLisse _ _).mapIso (upperStarAdicConstantIso π).symm))
  obtain ⟨C⟩ := nonempty_iso_derivedLowerShriek_comp (k₀ := k₀) (l := l) π (B ↘ S)
  -- `Rp₀! ≅ Rq₀! ∘ Rπ₀!` for `q : 𝔸^{n ∖ {i}} ⟶ Spec k₀`, as `p = π ≫ q`
  have key : ∀ (f : A ⟶ S) [f.IsOver S] [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f], π ≫ B ↘ S = f → IsZero ((derivedLowerShriek k₀ l f).obj
        (WeilSheaf.toComplex.obj (artinSchreierOf ψ (AffineSpace.linearFunction k₀ c)))) := by
    rintro f _ _ _ _ rfl
    exact ((derivedLowerShriek k₀ l (B ↘ S)).map_isZero h₁).of_iso (C.app _)
  exact key _ hπS

end WeilComplex

end AlgebraicGeometry
