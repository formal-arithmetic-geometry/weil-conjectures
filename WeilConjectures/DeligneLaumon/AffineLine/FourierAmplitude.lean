/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierTateTwist
public import WeilConjectures.WeilSheaf.HomologySequence
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.DeligneLaumon.AffineLine.Punctual

/-!
# The ordinary amplitude of the Fourier–Deligne transform on the line

This file collects the statements about the ordinary cohomology sheaves of the Fourier–Deligne
transform `FT_ψ` of the affine line which enter the perverse t-exactness of `FT_ψ`
(blueprint `thm-a1-fourier-t-exact`):

- `FT_ψ` lowers the lower bound of the cohomological amplitude by at most one, since `Rpr₂!` is
  left t-exact and `pr₁^*` and the tensor product with the lisse kernel are exact
  (`AlgebraicGeometry.isGE_fourierTransform_obj`);
- by Fourier inversion, `FT_ψ` raises the upper bound by at most one
  (`AlgebraicGeometry.isLE_fourierTransform_obj`);
- a sheaf of finite support transforms into a complex concentrated in degree `-1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- A Weil complex is `≤ n` exactly when its cohomology sheaves vanish in degrees `> n`. -/
lemma isLE_iff_isZero_homologySheaf (K : WeilComplex k₀ l X) (n : ℤ) :
    K.obj.IsLE n ↔ ∀ a : ℤ, n < a → IsZero ((homologySheaf a).obj K) := by
  rw [_root_.DerivedCategory.isLE_iff]
  exact forall₂_congr fun a _ ↦ (isZero_homologySheaf_obj_iff a K).symm

/-- A Weil complex is `≥ n` exactly when its cohomology sheaves vanish in degrees `< n`. -/
lemma isGE_iff_isZero_homologySheaf (K : WeilComplex k₀ l X) (n : ℤ) :
    K.obj.IsGE n ↔ ∀ a : ℤ, a < n → IsZero ((homologySheaf a).obj K) := by
  rw [_root_.DerivedCategory.isGE_iff]
  exact forall₂_congr fun a _ ↦ (isZero_homologySheaf_obj_iff a K).symm

/-- The Tate twist does not change the vanishing of a cohomology sheaf. -/
lemma isZero_homologySheaf_tateTwist_iff (m a : ℤ) (K : WeilComplex k₀ l X) :
    IsZero ((homologySheaf a).obj ((tateTwist k₀ l X m).obj K)) ↔
      IsZero ((homologySheaf a).obj K) :=
  sorry

/-- The Tate twist does not change the support of a cohomology sheaf. -/
lemma support_homologySheaf_tateTwist (m a : ℤ) (K : WeilComplex k₀ l X) :
    ((homologySheaf a).obj ((tateTwist k₀ l X m).obj K)).support =
      ((homologySheaf a).obj K).support :=
  sorry


/-- The truncation triangle `τ_{<n} K ⟶ K ⟶ τ_{≥n} K ⟶` of a Weil complex `K ≤ n`, whose third
term is concentrated in degree `n`, with the same `𝓗ⁿ` as `K`. -/
lemma exists_distTriang_of_isLE (K : WeilComplex k₀ l X) (n : ℤ) (hK : K.obj.IsLE n) :
    ∃ (K₁ K₃ : WeilComplex k₀ l X) (f : K₁ ⟶ K) (g : K ⟶ K₃) (h : K₃ ⟶ K₁⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang _ ∧ K₁.obj.IsLE (n - 1) ∧ K₃.obj.IsLE n ∧
        K₃.obj.IsGE n ∧ Nonempty ((homologySheaf n).obj K₃ ≅ (homologySheaf n).obj K) :=
  sorry
end WeilComplex

/-- **Fourier inversion** on the line: `FT_{ψ⁻¹} ∘ FT_ψ ≅ (-)(-1)`.
(blueprint: `lem-fd-inversion`) -/
theorem nonempty_fourierTransform_comp_fourierTransform_inv_iso
    (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    Nonempty (fourierTransform ψ ⋙ fourierTransform ψ⁻¹ ≅
      WeilComplex.tateTwist k₀ l (affineLine k₀) (-1)) :=
  sorry

/-- `FT_ψ` lowers the lower bound of the amplitude by at most one. -/
theorem isGE_fourierTransform_obj (ψ : AddChar k₀ (PadicAlgCl l)) {a : ℤ}
    {K : WeilComplex k₀ l (affineLine k₀)} (hK : K.obj.IsGE a) :
    ((fourierTransform ψ).obj K).obj.IsGE (a - 1) :=
  sorry

/-- The inverse of `FT_ψ` lowers the lower bound of the amplitude by at most one. -/
theorem isGE_fourierTransform_inv_obj (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) {a : ℤ}
    {K : WeilComplex k₀ l (affineLine k₀)} (hK : K.obj.IsGE a) :
    haveI := isEquivalence_fourierTransform (l := l) ψ hψ
    ((fourierTransform ψ).inv.obj K).obj.IsGE (a - 1) :=
  sorry

/-- `FT_ψ` raises the upper bound of the amplitude by at most one. -/
theorem isLE_fourierTransform_obj (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) {m : ℤ}
    {K : WeilComplex k₀ l (affineLine k₀)} (hK : K.obj.IsLE m) :
    ((fourierTransform ψ).obj K).obj.IsLE (m + 1) :=
  sorry

/-- A sheaf of finite support transforms into a complex `≤ -1`. -/
theorem isLE_fourierTransform_toComplex_of_support_finite (ψ : AddChar k₀ (PadicAlgCl l))
    (P : WeilSheaf k₀ l (affineLine k₀)) (hP : P.support.Finite) :
    ((fourierTransform ψ).obj (WeilSheaf.toComplex.obj P)).obj.IsLE (-1) :=
  sorry

/-- A complex concentrated in degree `n` whose `𝓗ⁿ` has finite support transforms into a
complex `≤ n - 1`. -/
theorem isLE_fourierTransform_of_isGE_of_isLE (ψ : AddChar k₀ (PadicAlgCl l)) {n : ℤ}
    {K : WeilComplex k₀ l (affineLine k₀)} (hge : K.obj.IsGE n) (hle : K.obj.IsLE n)
    (hK : ((WeilComplex.homologySheaf n).obj K).support.Finite) :
    ((fourierTransform ψ).obj K).obj.IsLE (n - 1) :=
  sorry

/-- The top cohomology sheaf of the transform of a complex `≤ m` has finite support. -/
theorem support_homologySheaf_fourierTransform_finite (ψ : AddChar k₀ (PadicAlgCl l))
    (hψ : ψ ≠ 1) {m : ℤ} {K : WeilComplex k₀ l (affineLine k₀)} (hK : K.obj.IsLE m) :
    ((WeilComplex.homologySheaf (m + 1)).obj ((fourierTransform ψ).obj K)).support.Finite :=
  sorry

end AlgebraicGeometry
