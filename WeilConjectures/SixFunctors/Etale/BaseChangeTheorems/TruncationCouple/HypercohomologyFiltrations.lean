/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TruncationCouple.ExactCouples

/-!
# The hypercohomology spectral sequences of the proper base change theorem

Let `g' ≫ f = f' ≫ g` be a commutative square of schemes and `K ∈ D⁺(X_ét)` with
`Hᵠ(K) = 0` for `q < a`. The canonical truncation tower `τ_{≤ q} K` defines the spectral
sequences
```
  E₂^{p,q} = Rᵖ f_* Hᵠ(K) ⇒ H^{p+q}(R f_* K),
  E'₂^{p,q} = Rᵖ f'_* g'^* Hᵠ(K) ⇒ H^{p+q}(R f'_* g'^* K),
```
the spectral sequences of the exact couples `AlgebraicGeometry.Etale.hypercohomologyCouple`
(the truncation couple `CategoryTheory.Functor.truncationCouple` of `f_*` at `K`) and
`AlgebraicGeometry.Etale.hypercohomologyCouple'` (the truncation couple of `D g'^*⁺ ⋙ R f'_*⁺` at
`K`, i.e. obtained by applying `R f'_*⁺` to the tower `g'^* τ_{≤ q} K`). Their abutments carry
the image filtrations of `Hⁿ(R f_* τ_{≤ q} K) ⟶ Hⁿ(R f_* K)` and
`Hⁿ(R f'_* g'^* τ_{≤ q} K) ⟶ Hⁿ(R f'_* g'^* K)`
(`DerivedCategory.Plus.functorTruncationCoupleFiltration`, blueprint
`def-weil-pbc-hypercohomology-filtrations`), and both converge (blueprint
`lemma-weil-pbc-hypercohomology-convergence`).
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Pretriangulated

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

open Etale DerivedCategory.Plus

variable {X' X Y' Y : Scheme.{u}}

section Source

variable (f : X ⟶ Y) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))

/-- Blueprint `def-weil-pbc-hypercohomology-filtrations` (first spectral sequence): the
truncation couple of `R f_*⁺` at `K` (`CategoryTheory.Functor.truncationCouple`), with
`D^{p,n} = Hⁿ(R f_* τ_{≤ n - p} K)` and `E^{p,p+q} ≅ Rᵖ f_* Hᵠ(K)`
(`AlgebraicGeometry.Etale.hypercohomologyCoupleE₂Iso`), whose abutment `Hⁿ(R f_* K)`
(`AlgebraicGeometry.Etale.hypercohomologyCoupleAbutmentIso`) carries the image filtration
`DerivedCategory.Plus.functorTruncationCoupleFiltration` of the maps
`Hⁿ(R f_* τ_{≤ q} K) ⟶ Hⁿ(R f_* K)`. -/
noncomputable abbrev Etale.hypercohomologyCouple :
    ExactCouple (Sheaf Y.smallEtaleTopology A) ((-1, 0) : ℤ × ℤ) (2, 1) 0 :=
  functorTruncationCouple (f)_*[A].rightDerivedFunctorPlus K

lemma Etale.hypercohomologyCouple_eq :
    Etale.hypercohomologyCouple A f K = (f)_*[A].truncationCouple K :=
  rfl

/-- The `E₂`-page `E₂^{p,q} ≅ Rᵖ f_* Hᵠ(K)` of the first hypercohomology spectral sequence
(`def-weil-pbc-hypercohomology-filtrations`). -/
noncomputable def Etale.hypercohomologyCoupleE₂Iso (p : ℕ) (q : ℤ) :
    (Etale.hypercohomologyCouple A f K).E (p, p + q) ≅
      ((f)_*[A].rightDerived p).obj ((homologyFunctor _ q).obj K) :=
  (f)_*[A].truncationCoupleEIsoRightDerived K p q

/-- The abutment `D^{0,n} ≅ Hⁿ(R f_* K)` of the first hypercohomology spectral sequence
(`def-weil-pbc-hypercohomology-filtrations`). -/
noncomputable def Etale.hypercohomologyCoupleAbutmentIso (n : ℤ) :
    (Etale.hypercohomologyCouple A f K).D (0, n) ≅
      (homologyFunctor _ n).obj ((f)_*[A].rightDerivedFunctorPlus.obj K) :=
  have := isIso_functorTruncationCoupleι _ K
    (fun X₀ n _ _ hq ↦ (f)_*[A].isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE X₀ n hq)
    0 n le_rfl
  asIso (functorTruncationCoupleι _ K 0 n)

/-- The filtration of the abutment `Hⁿ(R f_* K)` of the first hypercohomology spectral
sequence is the image filtration of `Hⁿ(R f_* τ_{≤ n - p} K) ⟶ Hⁿ(R f_* K)`
(`def-weil-pbc-hypercohomology-filtrations`). -/
lemma Etale.hypercohomologyCouple_filtration (n p : ℤ) :
    (functorTruncationCoupleFiltration (f)_*[A].rightDerivedFunctorPlus K n).F p =
      imageSubobject ((homologyFunctor _ n).map ((f)_*[A].rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.TStructure.t.eTruncLTι ((n - p + 1 : ℤ) : EInt)).app K))) :=
  rfl

end Source

section Target

variable (g' : X' ⟶ X) (f' : X' ⟶ Y') (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))

/-- Blueprint `def-weil-pbc-hypercohomology-filtrations` (second spectral sequence): the
truncation couple of `D g'^*⁺ ⋙ R f'_*⁺` at `K` (`AlgebraicGeometry.Etale.truncationCoupleTarget`),
with `D^{p,n} = Hⁿ(R f'_* g'^* τ_{≤ n - p} K)` and `E^{p,p+q} ≅ Rᵖ f'_* g'^* Hᵠ(K)`
(`AlgebraicGeometry.Etale.hypercohomologyCouple'E₂Iso`), whose abutment `Hⁿ(R f'_* g'^* K)`
(`AlgebraicGeometry.Etale.hypercohomologyCouple'AbutmentIso`) carries the image filtration
`DerivedCategory.Plus.functorTruncationCoupleFiltration` of the maps
`Hⁿ(R f'_* g'^* τ_{≤ q} K) ⟶ Hⁿ(R f'_* g'^* K)`. -/
noncomputable abbrev Etale.hypercohomologyCouple' :
    ExactCouple (Sheaf Y'.smallEtaleTopology A) ((-1, 0) : ℤ × ℤ) (2, 1) 0 :=
  Etale.truncationCoupleTarget A g' f' K

/-- The `E₂`-page `E'₂^{p,q} ≅ Rᵖ f'_* g'^* Hᵠ(K)` of the second hypercohomology spectral
sequence (`def-weil-pbc-hypercohomology-filtrations`), using the exactness of `g'^*`. -/
noncomputable def Etale.hypercohomologyCouple'E₂Iso (p : ℕ) (q : ℤ) :
    (Etale.hypercohomologyCouple' A g' f' K).E (p, p + q) ≅
      ((f')_*[A].rightDerived p).obj (((g')^*[A]).obj ((homologyFunctor _ q).obj K)) :=
  functorTruncationCoupleEIso _ K p (p + q) ≪≫ eqToIso (by rw [add_sub_cancel_left]) ≪≫
    (homologyFunctor _ (p : ℤ)).mapIso ((f')_*[A].rightDerivedFunctorPlus.mapIso
      ((((g')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).app _)) ≪≫
    (f')_*[A].homologyRightDerivedFunctorPlusObjSingleFunctorIso _ p

/-- The abutment `D^{0,n} ≅ Hⁿ(R f'_* g'^* K)` of the second hypercohomology spectral sequence
(`def-weil-pbc-hypercohomology-filtrations`). -/
noncomputable def Etale.hypercohomologyCouple'AbutmentIso (n : ℤ) :
    (Etale.hypercohomologyCouple' A g' f' K).D (0, n) ≅
      (homologyFunctor _ n).obj
        ((((g')^*[A]).mapDerivedCategoryPlus ⋙ (f')_*[A].rightDerivedFunctorPlus).obj K) :=
  have := isIso_functorTruncationCoupleι _ K
    (fun X₀ n _ q hq ↦
      Etale.isZero_homologyFunctor_upperStar_comp_rightDerivedFunctorPlus (g' := g') (f' := f')
        A X₀ n q hq) 0 n le_rfl
  asIso (functorTruncationCoupleι _ K 0 n)

end Target

section Convergence

variable (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
  (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))

/-- Blueprint `lemma-weil-pbc-hypercohomology-convergence`: if `Hᵠ(K) = 0` for `q < a`, both
hypercohomology spectral sequences of `def-weil-pbc-hypercohomology-filtrations` lie in the
region `p ≥ 0`, `q ≥ a` (so in total degree `n` only `a ≤ q ≤ n` occurs), the filtrations of
their abutments are finite (equal to the whole abutment for `p ≤ 0`, zero for `p > n - a`),
exhaustive and separated, and both spectral sequences converge to their abutments with these
filtrations. -/
theorem Etale.hypercohomology_convergence (a : ℤ) [K.IsGE a] :
    (Etale.hypercohomologyCouple A f K).IsHalfPlane a ∧
      (Etale.hypercohomologyCouple' A g' f' K).IsHalfPlane a ∧
      (∀ n, (functorTruncationCoupleFiltration (f)_*[A].rightDerivedFunctorPlus K n).IsFiniteSeparated) ∧
      (∀ n, (functorTruncationCoupleFiltration
        (((g')^*[A]).mapDerivedCategoryPlus ⋙ (f')_*[A].rightDerivedFunctorPlus) K n).IsFiniteSeparated) ∧
      (Etale.hypercohomologyCouple A f K).ConvergesTo (functorTruncationCoupleι _ K)
        (functorTruncationCoupleFiltration _ K) ∧
      (Etale.hypercohomologyCouple' A g' f' K).ConvergesTo (functorTruncationCoupleι _ K)
        (functorTruncationCoupleFiltration _ K) := by
  have hF₁ : ∀ (X₀ : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) (n : ℤ) [X₀.IsGE n]
      (q : ℤ), q < n → IsZero ((homologyFunctor _ q).obj ((f)_*[A].rightDerivedFunctorPlus.obj X₀)) :=
    fun X₀ n _ _ hq ↦ (f)_*[A].isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE X₀ n hq
  have hF₂ := fun (X₀ : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) (n : ℤ) [X₀.IsGE n]
      (q : ℤ) (hq : q < n) ↦
    Etale.isZero_homologyFunctor_upperStar_comp_rightDerivedFunctorPlus (g' := g') (f' := f')
      A X₀ n q hq
  exact ⟨functorTruncationCouple_isHalfPlane _ K hF₁ a,
    functorTruncationCouple_isHalfPlane _ K hF₂ a,
    isFiniteSeparated_functorTruncationCoupleFiltration _ K hF₁ a,
    isFiniteSeparated_functorTruncationCoupleFiltration _ K hF₂ a,
    functorTruncationCouple_convergesTo _ K hF₁ a,
    functorTruncationCouple_convergesTo _ K hF₂ a⟩

end Convergence

end AlgebraicGeometry
