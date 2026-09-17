/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.AlgebraicGeometry.Modules.Picard

/-!
# Tensoring by an invertible sheaf of modules is exact

Tensoring a sheaf of `𝒪ₓ`-modules by an invertible one is an *equivalence* of `X.Modules` with
itself, the inverse being tensoring by the inverse sheaf: this is
`AlgebraicGeometry.Scheme.Modules.tensorRightEquiv`. In particular it preserves all limits and
colimits, so it carries a short exact sequence of sheaves of modules to a short exact sequence,
which is `AlgebraicGeometry.Scheme.Modules.shortExact_tensorRightShortComplex`.

This is the step of the proof of Snapper's theorem `thm:deg-snapper` where the hyperplane exact
sequence of `WeilConjectures.AlgebraicGeometry.Modules.HyperplaneSection` is tensored by the
twisting factor `L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r` before the Euler characteristic is summed along it.

## Main results

- `AlgebraicGeometry.Scheme.Modules.tensorRightEquiv`: tensoring by an invertible sheaf of
  modules is an equivalence of categories.
- `AlgebraicGeometry.Scheme.Modules.shortExact_tensorRightShortComplex`: a short exact sequence
  of sheaves of modules stays short exact after tensoring by an invertible sheaf.
- `AlgebraicGeometry.Scheme.Modules.isZero_tensorObj_of_isZero`: tensoring a zero sheaf of
  modules by an invertible sheaf gives a zero sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {N N' : X.Modules}

/-- If `N ⊗ N'` is the tensor unit then tensoring by `N` and then by `N'` is the identity:
`(Y ⊗ N) ⊗ N' ≅ Y ⊗ (N ⊗ N') ≅ Y ⊗ 𝟙 ≅ Y`, naturally in `Y`. -/
noncomputable def tensorRightCompIso (e : N ⊗ N' ≅ 𝟙_ X.Modules) :
    tensorRight N ⋙ tensorRight N' ≅ 𝟭 X.Modules :=
  NatIso.ofComponents (fun Y ↦ α_ Y N N' ≪≫ whiskerLeftIso Y e ≪≫ ρ_ Y) (by
    intro A B f
    show f ▷ N ▷ N' ≫ _ = _
    simp only [Iso.trans_hom, whiskerLeftIso_hom, Functor.id_map, Category.assoc]
    rw [← Category.assoc (f ▷ N ▷ N'), associator_naturality_left, Category.assoc,
      ← Category.assoc (f ▷ (N ⊗ N')), ← whisker_exchange, Category.assoc]
    simp)

variable (hN : N.Invertible)
include hN

/-- **Tensoring by an invertible sheaf of modules is an equivalence** of `X.Modules` with itself,
the inverse being tensoring by the inverse sheaf. -/
noncomputable def tensorRightEquiv : X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (tensorRight N) (tensorRight hN.tensorInv)
    (tensorRightCompIso hN.tensorInvIso).symm
    (tensorRightCompIso (β_ _ _ ≪≫ hN.tensorInvIso))

lemma isEquivalence_tensorRight : (MonoidalCategory.tensorRight N).IsEquivalence :=
  (tensorRightEquiv hN).isEquivalence_functor

/-- **Whiskering the zero morphism by an invertible sheaf of modules gives zero.** -/
lemma zero_whiskerRight {A B : X.Modules} : (0 : A ⟶ B) ▷ N = 0 := by
  have : (MonoidalCategory.tensorRight N).IsEquivalence := isEquivalence_tensorRight hN
  exact (MonoidalCategory.tensorRight N).map_zero A B

/-- **Tensoring a zero sheaf of modules by an invertible sheaf gives a zero sheaf.** -/
lemma isZero_tensorObj_of_isZero {F : X.Modules} (hF : IsZero F) : IsZero (F ⊗ N) := by
  rw [IsZero.iff_id_eq_zero, ← id_whiskerRight F N, hF.eq_of_src (𝟙 F) 0, zero_whiskerRight hN]

variable (S : ShortComplex X.Modules)

/-- The short complex `S ⊗ N` obtained by tensoring each term of the short complex `S` by an
invertible sheaf of modules `N`. -/
@[simps X₁ X₂ X₃ f g]
noncomputable def tensorRightShortComplex : ShortComplex X.Modules :=
  ShortComplex.mk (S.f ▷ N) (S.g ▷ N) (by rw [← comp_whiskerRight, S.zero, zero_whiskerRight hN])

/-- **Tensoring a short exact sequence of sheaves of modules by an invertible sheaf keeps it
short exact**, tensoring by an invertible sheaf being an equivalence. -/
theorem shortExact_tensorRightShortComplex (hS : S.ShortExact) :
    (tensorRightShortComplex hN S).ShortExact := by
  have : (MonoidalCategory.tensorRight N).IsEquivalence := isEquivalence_tensorRight hN
  exact hS.map_of_exact (MonoidalCategory.tensorRight N)

end AlgebraicGeometry.Scheme.Modules
