/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
public import WeilConjectures.Evaluation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Lisse Weil sheaves on an open subcurve

Let `j : U₀ ↪ C₀` be an open subscheme of a curve over `𝔽_q`. The closed points of `U₀` are
closed points of `C₀` with the same residue field, so the same norm and degree. If `C₀` is a
smooth geometrically connected curve and `U₀` is a nonempty affine open, then `U₀` is again a
smooth geometrically connected curve (`sk-d-real-setup`).

A lisse Weil sheaf `𝒢` on `C₀` restricts to `U₀`: its representation is pulled back along the
surjection `W(U₀) → W(C₀)`, so it factors through the image of `W(U₀)`, which is all of `W(C₀)`.
Accordingly the restriction is recorded here on the Weil group
`AlgebraicGeometry.WeilGroup.ofIsOpenImmersion`: the group `W(C₀)` itself, with its local
Frobenius elements at the closed points of `U₀`. Local polynomials, reality, determinant weights
and punctual purity at a closed point of `U₀` are those of `𝒢` at its image in `C₀`.

## Main definitions

- `AlgebraicGeometry.WeilGroup.ofIsOpenImmersion`

## Main statements

- `AlgebraicGeometry.IsCurve.comp_of_isOpenImmersion`
- `AlgebraicGeometry.GeometricallyConnected.comp_of_isOpenImmersion`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- An open immersion preserves the norm of a point. -/
theorem pointNorm_of_isOpenImmersion (y : U) : X.pointNorm (j.base y) = U.pointNorm y :=
  Nat.card_congr (asIso (j.residueFieldMap y)).commRingCatIsoToRingEquiv.toEquiv

/-- A point of an open subscheme has finite residue field exactly when its image has. -/
theorem mem_finitePoints_iff_of_isOpenImmersion (y : U) :
    j.base y ∈ X.finitePoints ↔ y ∈ U.finitePoints := by
  let e := (asIso (j.residueFieldMap y)).commRingCatIsoToRingEquiv.toEquiv
  exact ⟨fun h ↦ @Finite.of_equiv _ _ h e, fun h ↦ @Finite.of_equiv _ _ h e.symm⟩

/-- An open immersion over a finite field preserves the degree of a closed point. -/
theorem Hom.degreeOver_comp_of_isOpenImmersion {k : Type u} [Field k] [Finite k]
    (f : X ⟶ Spec (.of k)) {y : U} (hy : y ∈ U.finitePoints) :
    (j ≫ f).degreeOver y = f.degreeOver (j.base y) := by
  have h := (j ≫ f).pointNorm_eq_pow_degreeOver hy
  rw [← pointNorm_of_isOpenImmersion j y,
    f.pointNorm_eq_pow_degreeOver ((mem_finitePoints_iff_of_isOpenImmersion j y).2 hy)] at h
  exact (Nat.pow_right_injective (Finite.one_lt_card (α := k))) h.symm

end Scheme

variable {K : Type u} [Field K] {C U : Scheme.{u}} (p : C ⟶ Spec (.of K)) (j : U ⟶ C)
  [IsOpenImmersion j]

/-- Blueprint `sk-d-real-setup`: a quasi-compact open subscheme of a curve is a curve. -/
theorem IsCurve.comp_of_isOpenImmersion [IsCurve p] [CompactSpace U] : IsCurve (j ≫ p) where
  toQuasiCompact := quasiCompact_of_compactSpace _
  krullDim_le_one := j.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans
    (IsCurve.krullDim_le_one (f := p))

/-- Blueprint `sk-d-real-setup`: a nonempty open subscheme of a smooth geometrically connected
scheme over a field is geometrically connected. Smooth and geometrically connected implies
geometrically irreducible, and a nonempty open of a geometrically irreducible scheme is
geometrically irreducible. -/
theorem GeometricallyConnected.comp_of_isOpenImmersion [Nonempty U] [Smooth p]
    [GeometricallyConnected p] : GeometricallyConnected (j ≫ p) := by
  have : GeometricallyIrreducible p := .of_smooth_of_geometricallyConnected p
  have : Surjective (j ≫ p) := ⟨fun z ↦ by
    obtain ⟨y⟩ := ‹Nonempty U›
    exact ⟨y, Subsingleton.elim _ _⟩⟩
  infer_instance

namespace WeilGroup

variable [Finite K] {p} [IsCurve p] [IsCurve (j ≫ p)]

/-- The restriction of the Weil group data of `C₀` to an open subcurve `j : U₀ ↪ C₀`: the
group `W(C₀)` with its degree, its degree-one lift and, at a closed point `y` of `U₀`, the local
Frobenius of `C₀` at `j y`.

This is the image of `W(U₀) → W(C₀)`, which is surjective
(`AlgebraicGeometry.WeilGroup.Restriction`): a lisse Weil sheaf on `C₀` restricted to `U₀`
is a representation of `W(U₀)` factoring through this image, and its local polynomials at the
closed points of `U₀` are computed by the Frobenius elements recorded here. -/
noncomputable def ofIsOpenImmersion (W : WeilGroup p) : WeilGroup (j ≫ p) where
  carrier := W.carrier
  group := W.group
  topologicalSpace := W.topologicalSpace
  isTopologicalGroup := W.isTopologicalGroup
  deg := W.deg
  deg_surjective := W.deg_surjective
  isOpen_ker := W.isOpen_ker
  compactSpace_ker := W.compactSpace_ker
  totallyDisconnectedSpace_ker := W.totallyDisconnectedSpace_ker
  frobeniusLift := W.frobeniusLift
  deg_frobeniusLift := W.deg_frobeniusLift
  frobenius y :=
    W.frobenius ⟨j.base y.1, (Scheme.mem_finitePoints_iff_of_isOpenImmersion j y.1).2 y.2⟩
  deg_frobenius y := by
    rw [W.deg_frobenius, Scheme.Hom.degreeOver_comp_of_isOpenImmersion j p y.2]

variable {W : WeilGroup p} {l : ℕ} [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  {ρ : Representation (PadicAlgCl l) W.carrier V} (ι : PadicAlgCl l →+* ℂ)

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- A lisse Weil sheaf on `C₀` restricts to a lisse Weil sheaf on `U₀`. -/
theorem IsLisse.ofIsOpenImmersion (hρ : W.IsLisse l ρ) :
    (W.ofIsOpenImmersion j).IsLisse l ρ :=
  ⟨hρ.continuous_toMatrix⟩

/-- Blueprint `sk-d-real-setup`: an `ι`-real lisse Weil sheaf on `C₀` restricts to an `ι`-real
one on `U₀`, reality being a condition at each closed point. -/
theorem IsReal.ofIsOpenImmersion (h : W.IsReal l ρ ι) : (W.ofIsOpenImmersion j).IsReal l ρ ι :=
  fun _ n ↦ h _ n

omit [FiniteDimensional (PadicAlgCl l) V] in
/-- Determinant weights are preserved by restriction to an open subcurve. -/
theorem HasDetWeight.ofIsOpenImmersion {γ : ℝ} (h : W.HasDetWeight l ρ ι γ) :
    (W.ofIsOpenImmersion j).HasDetWeight l ρ ι γ := fun y ↦ by
  have hy := h ⟨j.base y.1, (Scheme.mem_finitePoints_iff_of_isOpenImmersion j y.1).2 y.2⟩
  rw [Scheme.pointNorm_of_isOpenImmersion j y.1] at hy
  exact hy

/-- Punctual purity on an open subcurve is punctual purity of the original sheaf at the closed
points of the open. -/
theorem IsPunctuallyPure.of_ofIsOpenImmersion {w : ℝ}
    (h : (W.ofIsOpenImmersion j).IsPunctuallyPure l ρ ι w) (y : U.finitePoints) :
    ∀ α ∈ W.localEigenvalues l ρ
      ⟨j.base y.1, (Scheme.mem_finitePoints_iff_of_isOpenImmersion j y.1).2 y.2⟩,
      frobeniusWeight ι (C.pointNorm (j.base y.1)) α = w := fun α hα ↦ by
  rw [Scheme.pointNorm_of_isOpenImmersion j y.1]
  exact h y α hα

end WeilGroup

end AlgebraicGeometry
