/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TruncationCouple.ExactCouples
public import WeilConjectures.CategoryTheory.DerivedCategory.TruncationSpectralSequence

/-!
# The hypercohomology spectral sequences of the proper base change theorem

Let `g' ≫ f = f' ≫ g` be a commutative square of schemes and `K ∈ D⁺(X_ét)` with
`H^q(K) = 0` for `q < a`. The canonical truncation tower `τ_{≤ q} K` defines the spectral
sequences
```
  E₂^{p,q} = R^p f_* H^q(K) ⇒ H^{p+q}(R f_* K),
  E'₂^{p,q} = R^p f'_* g'^* H^q(K) ⇒ H^{p+q}(R f'_* g'^* K),
```
the spectral sequences of the exact couples `AlgebraicGeometry.Etale.hypercohomologyCouple`
(the truncation couple of `R f_*⁺` at `K`) and `AlgebraicGeometry.Etale.hypercohomologyCouple'`
(the truncation couple of `D g'^*⁺ ⋙ R f'_*⁺` at `K`, i.e. obtained by applying `R f'_*⁺` to
the tower `g'^* τ_{≤ q} K`). Their abutments carry the image filtrations of
`H^n(R f_* τ_{≤ q} K) ⟶ H^n(R f_* K)` and `H^n(R f'_* g'^* τ_{≤ q} K) ⟶ H^n(R f'_* g'^* K)`
(blueprint `def-weil-pbc-hypercohomology-filtrations`), and both converge
(blueprint `lemma-weil-pbc-hypercohomology-convergence`).
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
truncation couple of `R f_*⁺` at `K`, with `D^{p,q} = H^{p+q}(R f_* τ_{≤ q} K)` and
`E^{p,q} = H^{p+q}(R f_* (H^q(K)[-q])) ≅ R^p f_* H^q(K)`
(`AlgebraicGeometry.Etale.hypercohomologyCoupleE₂Iso`), whose abutment `H^n(R f_* K)`
(`AlgebraicGeometry.Etale.hypercohomologyCoupleAbutmentIso`) carries the image filtration of
the maps `H^n(R f_* τ_{≤ q} K) ⟶ H^n(R f_* K)`
(`AlgebraicGeometry.Etale.hypercohomologyCouple_filtration`). -/
noncomputable abbrev Etale.hypercohomologyCouple : ExactCouple (Sheaf Y.smallEtaleTopology A) 0 :=
  truncationCouple (f)_*[A].rightDerivedFunctorPlus K

/-- The `E₂`-page `E₂^{p,q} ≅ R^p f_* H^q(K)` of the first hypercohomology spectral sequence
(`def-weil-pbc-hypercohomology-filtrations`). -/
noncomputable def Etale.hypercohomologyCoupleE₂Iso (p : ℕ) (q : ℤ) :
    (Etale.hypercohomologyCouple A f K).E p q ≅
      ((f)_*[A].rightDerived p).obj ((homologyFunctor _ q).obj K) :=
  rightDerivedTruncationCoupleE₂Iso _ K p q

/-- The abutment `D^{0,n} ≅ H^n(R f_* K)` of the first hypercohomology spectral sequence
(`def-weil-pbc-hypercohomology-filtrations`). -/
noncomputable def Etale.hypercohomologyCoupleAbutmentIso (n : ℤ) :
    (Etale.hypercohomologyCouple A f K).D 0 n ≅
      ((homologyFunctor _ 0).shift n).obj ((f)_*[A].rightDerivedFunctorPlus.obj K) :=
  truncationCoupleAbutmentIso _ K (isZero_homologyFunctor_rightDerivedFunctorPlus _) n

/-- The filtration of the abutment `H^n(R f_* K)` of the first hypercohomology spectral
sequence is the image filtration of `H^n(R f_* τ_{≤ q} K) ⟶ H^n(R f_* K)`
(`def-weil-pbc-hypercohomology-filtrations`). -/
lemma Etale.hypercohomologyCouple_filtration (n p : ℤ) (hp : 0 ≤ p) :
    imageSubobject ((((Etale.hypercohomologyCouple A f K).abutmentFiltration n).F p).arrow ≫
      (Etale.hypercohomologyCoupleAbutmentIso A f K n).hom) =
      truncationCoupleFiltration _ K n (n - p) :=
  imageSubobject_abutmentFiltration_truncationCouple _ K _ n p hp

end Source

section Target

variable (g' : X' ⟶ X) (f' : X' ⟶ Y') (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))

/-- Blueprint `def-weil-pbc-hypercohomology-filtrations` (second spectral sequence): the
truncation couple of `D g'^*⁺ ⋙ R f'_*⁺` at `K` (`AlgebraicGeometry.Etale.truncationCoupleTarget`),
with `D^{p,q} = H^{p+q}(R f'_* g'^* τ_{≤ q} K)` and
`E^{p,q} = H^{p+q}(R f'_* g'^* (H^q(K)[-q])) ≅ R^p f'_* g'^* H^q(K)`
(`AlgebraicGeometry.Etale.hypercohomologyCouple'E₂Iso`), whose abutment `H^n(R f'_* g'^* K)`
(`AlgebraicGeometry.Etale.hypercohomologyCouple'AbutmentIso`) carries the image filtration of
the maps `H^n(R f'_* g'^* τ_{≤ q} K) ⟶ H^n(R f'_* g'^* K)`
(`AlgebraicGeometry.Etale.hypercohomologyCouple'_filtration`). -/
noncomputable abbrev Etale.hypercohomologyCouple' :
    ExactCouple (Sheaf Y'.smallEtaleTopology A) 0 :=
  Etale.truncationCoupleTarget A g' f' K

/-- The `E₂`-page `E'₂^{p,q} ≅ R^p f'_* g'^* H^q(K)` of the second hypercohomology spectral
sequence (`def-weil-pbc-hypercohomology-filtrations`), using the exactness of `g'^*`. -/
noncomputable def Etale.hypercohomologyCouple'E₂Iso (p : ℕ) (q : ℤ) :
    (Etale.hypercohomologyCouple' A g' f' K).E p q ≅
      ((f')_*[A].rightDerived p).obj (((g')^*[A]).obj ((homologyFunctor _ q).obj K)) :=
  truncationCoupleEIso _ K p q ≪≫
    ((homologyFunctor _ 0).shift (p : ℤ)).mapIso ((f')_*[A].rightDerivedFunctorPlus.mapIso
      ((((g')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).app _)) ≪≫
    (f')_*[A].homologyRightDerivedFunctorPlusObjSingleFunctorIso _ p

/-- The abutment `D^{0,n} ≅ H^n(R f'_* g'^* K)` of the second hypercohomology spectral sequence
(`def-weil-pbc-hypercohomology-filtrations`). -/
noncomputable def Etale.hypercohomologyCouple'AbutmentIso (n : ℤ) :
    (Etale.hypercohomologyCouple' A g' f' K).D 0 n ≅
      ((homologyFunctor _ 0).shift n).obj
        ((((g')^*[A]).mapDerivedCategoryPlus ⋙ (f')_*[A].rightDerivedFunctorPlus).obj K) :=
  truncationCoupleAbutmentIso _ K
    (fun X₀ n _ q hq ↦
      Etale.isZero_homologyFunctor_upperStar_comp_rightDerivedFunctorPlus (g' := g') (f' := f')
        A X₀ n q hq) n

/-- The filtration of the abutment `H^n(R f'_* g'^* K)` of the second hypercohomology spectral
sequence is the image filtration of `H^n(R f'_* g'^* τ_{≤ q} K) ⟶ H^n(R f'_* g'^* K)`
(`def-weil-pbc-hypercohomology-filtrations`). -/
lemma Etale.hypercohomologyCouple'_filtration (n p : ℤ) (hp : 0 ≤ p) :
    imageSubobject ((((Etale.hypercohomologyCouple' A g' f' K).abutmentFiltration n).F p).arrow ≫
      (Etale.hypercohomologyCouple'AbutmentIso A g' f' K n).hom) =
      truncationCoupleFiltration _ K n (n - p) :=
  imageSubobject_abutmentFiltration_truncationCouple _ K _ n p hp

end Target

section Convergence

variable (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
  (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))

/-- Blueprint `lemma-weil-pbc-hypercohomology-convergence`: if `H^q(K) = 0` for `q < a`, both
hypercohomology spectral sequences of `def-weil-pbc-hypercohomology-filtrations` lie in the
region `p ≥ 0`, `q ≥ a` (so in total degree `n` only `a ≤ q ≤ n` occurs), i.e. they satisfy
the hypotheses of `thm-sp-half-plane-convergence`, and the filtrations of their abutments are
finite (equal to the whole abutment for `p ≤ 0`, zero for `p > n - a`), hence exhaustive and
separated; consequently `E_∞^{p,q} ≅ grᵖ H^{p+q}` for both
(`CategoryTheory.ExactCouple.IsHalfPlane.grIsoEInfty`). -/
theorem Etale.hypercohomology_convergence (a : ℤ) [K.IsGE a] :
    (Etale.hypercohomologyCouple A f K).IsHalfPlane a ∧
      (Etale.hypercohomologyCouple' A g' f' K).IsHalfPlane a ∧
      (∀ n, ((Etale.hypercohomologyCouple A f K).abutmentFiltration n).IsFinite) ∧
      (∀ n, ((Etale.hypercohomologyCouple' A g' f' K).abutmentFiltration n).IsFinite) := by
  have h₁ := isHalfPlane_truncationCouple _ K
    (isZero_homologyFunctor_rightDerivedFunctorPlus (f)_*[A]) a
  have h₂ := isHalfPlane_truncationCouple _ K
    (fun X₀ n _ q hq ↦
      Etale.isZero_homologyFunctor_upperStar_comp_rightDerivedFunctorPlus (g' := g') (f' := f')
        A X₀ n q hq) a
  exact ⟨h₁, h₂, h₁.abutmentFiltration_isFinite, h₂.abutmentFiltration_isFinite⟩

end Convergence

end AlgebraicGeometry
