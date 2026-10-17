/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality

/-!
# The open–closed triangle under the direct image with compact support

A form of the open–closed triangle under `Rf_!` of blueprint `prop-functor-package` (clause 3)
with explicit morphisms and prescribed composites `fj = j ≫ f` and `fi = i ≫ f`, derived from
`AlgebraicGeometry.WeilComplex.exists_distTriang_derivedLowerShriek_openClosed`.

## Main statements

- `AlgebraicGeometry.WeilComplex.exists_distTriang_derivedLowerShriek_openClosed_comp`: the
  triangle `R(fj)_! j^*K ⟶ Rf_! K ⟶ R(fi)_! i^*K ⟶`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The open–closed triangle under `Rf_!`**: for a closed immersion `i : Z ↪ X` with open
complement `j : U ↪ X`, a morphism `f : X ⟶ Y` of `k₀`-schemes and a Weil complex `K` on `X`,
applying `Rf_!` to the localization triangle `j_!j^*K ⟶ K ⟶ i_*i^*K ⟶` gives a distinguished
triangle

`R(fj)_! j^*K ⟶ Rf_! K ⟶ R(fi)_! i^*K ⟶ R(fj)_! j^*K[1]`.

The composites `fj = j ≫ f` and `fi = i ≫ f` are given as separate morphisms. This is
`AlgebraicGeometry.WeilComplex.exists_distTriang_derivedLowerShriek_openClosed` with the
vertices of the triangle replaced by the isomorphic ones. -/
theorem exists_distTriang_derivedLowerShriek_openClosed_comp {U X Z Y : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (fj : U ⟶ Y) [fj.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated fj]
    [LocallyOfFiniteType fj] [QuasiCompact fj] (fi : Z ⟶ Y) [fi.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated fi] [LocallyOfFiniteType fi] [QuasiCompact fi] (hfj : j ≫ f = fj)
    (hfi : i ≫ f = fi) [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    ∃ (α : (derivedLowerShriek k₀ l fj).obj ((upperStar j).obj K) ⟶
        (derivedLowerShriek k₀ l f).obj K)
      (β : (derivedLowerShriek k₀ l f).obj K ⟶
        (derivedLowerShriek k₀ l fi).obj ((upperStar i).obj K))
      (γ : (derivedLowerShriek k₀ l fi).obj ((upperStar i).obj K) ⟶
        ((derivedLowerShriek k₀ l fj).obj ((upperStar j).obj K))⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang (WeilComplex k₀ l Y) := by
  subst hfj hfi
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_distTriang_derivedLowerShriek_openClosed (l := l)
    j i (by rw [hij]; exact isCompl_compl) f K
  refine ⟨e₁.inv ≫ T.mor₁ ≫ e₂.hom, e₂.inv ≫ T.mor₂ ≫ e₃.hom,
    e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _ ?_⟩
  exact Triangle.isoMk _ _ e₁.symm e₂.symm e₃.symm (by simp) (by simp)
    (by simp [← Functor.map_comp])

end WeilComplex

end AlgebraicGeometry
