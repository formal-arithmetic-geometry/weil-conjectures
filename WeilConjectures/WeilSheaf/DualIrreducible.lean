/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.FiniteLength

/-!
# The dual of an irreducible lisse Weil sheaf

On a `k₀`-scheme with irreducible geometric fiber, the dual `M^∨` of an irreducible lisse Weil
sheaf `M` is irreducible lisse: a lisse subsheaf `N ⊆ M^∨` dualises to a lisse quotient
`M ≅ M^∨∨ ↠ N^∨`, whose kernel is a lisse subsheaf of `M`.

The dualised morphism `M ⟶ N^∨` is the transpose `m ↦ (n ↦ i(n)(m))` of the inclusion
`i : N ⟶ M^∨` (`AlgebraicGeometry.WeilSheaf.dualTranspose`), which is compatible with the Weil
structures since the evaluations `F^∨ ⊗ F ⟶ ℚ̄_ℓ` are. If it vanishes, so does `i`; otherwise
it is injective, `M` being irreducible, and comparing the ranks of the stalks shows that `i` is
an isomorphism.

## Main statements

- `AlgebraicGeometry.WeilSheaf.dualTranspose`: the transpose `M ⟶ N^∨` of a morphism
  `N ⟶ M^∨` of Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.dual`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal ProEtale

namespace AlgebraicGeometry.WeilSheaf

section Transpose

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The evaluation `P^∨ ⊗ P ⟶ ℚ̄_ℓ` after the Weil structure of `P^∨`, in terms of the
Frobenius pullback of the evaluation (`AlgebraicGeometry.WeilSheaf.dual_evaluation_str`). -/
lemma dualStr_whiskerRight_evaluation (P : WeilSheaf k₀ l X) (hP : P.IsLisse) :
    (P.dual hP).obj.str.hom.hom ▷ P.obj.carrier.X ≫
        Mod.evaluation P.obj.carrier (adicConstant k₀ l X).obj.carrier =
      _ ◁ P.obj.str.inv.hom ≫
        μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l]
          (P.dual hP).obj.carrier.X P.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map
          (Mod.evaluation P.obj.carrier (adicConstant k₀ l X).obj.carrier) ≫
        (adicConstant k₀ l X).obj.str.hom.hom := by
  rw [← dual_evaluation_str P hP, tensorHom_def', ← MonoidalCategory.whiskerLeft_comp_assoc]
  have hφ : P.obj.str.inv.hom ≫ P.obj.str.hom.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Iso.inv_hom_id, Mod.id_hom']
  rw [hφ, MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- The transpose `M ⟶ N^∨`, `m ↦ (n ↦ i(n)(m))`, of a morphism `i : N ⟶ M^∨` of Weil sheaves,
`M` and `N` being lisse: the transpose `CategoryTheory.Mod.transpose` of the underlying
morphism of sheaves, which is compatible with the Weil structures since the evaluations
`M^∨ ⊗ M ⟶ ℚ̄_ℓ` and `N^∨ ⊗ N ⟶ ℚ̄_ℓ` are. -/
noncomputable def dualTranspose {M N : WeilSheaf k₀ l X} (hM : M.IsLisse) (hN : N.IsLisse)
    (i : N ⟶ M.dual hM) : M ⟶ N.dual hN :=
  ObjectProperty.homMk (ObjectProperty.homMk
    ⟨Mod.transpose i.hom.hom.f, Mod.uncurryHom_injective (by
      sorry)⟩)

lemma dualTranspose_hom_hom_f {M N : WeilSheaf k₀ l X} (hM : M.IsLisse) (hN : N.IsLisse)
    (i : N ⟶ M.dual hM) : (dualTranspose hM hN i).hom.hom.f = Mod.transpose i.hom.hom.f :=
  rfl

end Transpose

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]

/-- The dual of an irreducible lisse Weil sheaf is irreducible lisse. -/
theorem IsIrreducibleLisse.dual {M : WeilSheaf k₀ l X} (hM : M.IsIrreducibleLisse) :
    (M.dual hM.1).IsIrreducibleLisse :=
  sorry

end AlgebraicGeometry.WeilSheaf
