/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ProjectionFormula.UpperStarTensorWeil
public import WeilConjectures.WeilSheaf.ProjectionFormula.LisseTensor
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# Pushforward of pro-étale Weil sheaves and internal homs

For a morphism `φ : X ⟶ Y` of `k₀`-schemes and a pro-étale Weil sheaf `A` on `Y`,
`φ_* [φ^* A, -] ≅ [A, φ_* -]`
(`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_lowerStarCompIhomFunctorIso`): the right adjoints
of `φ^*(- ⊗ A)` and `φ^*(-) ⊗ φ^* A` agree, as these left adjoints do
(`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_tensorFunctorCompUpperStarIso`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

/-- **Pushforward and internal homs**: `φ_* [φ^* A, -] ≅ [A, φ_* -]`, by conjugation of
`φ^*(- ⊗ A) ≅ φ^*(-) ⊗ φ^* A` along the tensor-hom and pullback-pushforward adjunctions. -/
theorem nonempty_lowerStarCompIhomFunctorIso (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (A : ProEtaleWeilSheaf k₀ l Y) :
    Nonempty (lowerStar k₀ l φ ⋙ ihomFunctor k₀ l Y A ≅
      ihomFunctor k₀ l X ((upperStar k₀ l φ).obj A) ⋙ lowerStar k₀ l φ) := by
  obtain ⟨e⟩ := nonempty_tensorFunctorCompUpperStarIso φ A
  exact ⟨conjugateIsoEquiv
    ((tensorIhomAdjunction k₀ l Y A).comp (upperStarLowerStarAdjunction k₀ l φ))
    ((upperStarLowerStarAdjunction k₀ l φ).comp
      (tensorIhomAdjunction k₀ l X ((upperStar k₀ l φ).obj A))) e.symm⟩

/-- The pushforward of pro-étale Weil sheaves preserves K-injective complexes, being right adjoint
to the exact pullback. -/
instance preservesKInjectiveComplexes_lowerStar (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] :
    (lowerStar k₀ l φ).PreservesKInjectiveComplexes :=
  (upperStarLowerStarAdjunction k₀ l φ).preservesKInjectiveComplexes

/-- **Derived pushforward and internal homs out of a lisse sheaf**:
`Rφ_* R[φ^* A, -] ≅ R[A, -] Rφ_*` for a pro-étale Weil sheaf `A` with lisse underlying sheaf. -/
theorem nonempty_rightDerivedLowerStarCompIhomFunctorIso (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (A : ProEtaleWeilSheaf k₀ l Y)
    (hA : ProEtale.IsAdicLisseSheaf A.carrier) :
    Nonempty ((lowerStar k₀ l φ).rightDerivedFunctor ⋙ (ihomFunctor k₀ l Y A).rightDerivedFunctor ≅
      (ihomFunctor k₀ l X ((upperStar k₀ l φ).obj A)).rightDerivedFunctor ⋙
        (lowerStar k₀ l φ).rightDerivedFunctor) := by
  have := preservesKInjectiveComplexes_ihomFunctor ((upperStar k₀ l φ).obj A)
    (hA.upperStar (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))))
  obtain ⟨e⟩ := nonempty_lowerStarCompIhomFunctorIso φ A
  exact ⟨(Functor.rightDerivedFunctorCompIso _ _).symm ≪≫ Functor.rightDerivedFunctorNatIso e ≪≫
    Functor.rightDerivedFunctorCompIso _ _⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
