/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck

/-!
# The Leray spectral sequence of a morphism of schemes

For a morphism of schemes `f : X ⟶ Y` and an `𝒪_X`-module `ℱ` there is a first quadrant
spectral sequence `E₂^{p,q} = H^p(Y, R^q f_* ℱ) ⇒ H^{p+q}(X, ℱ)`, where the cohomology groups are
the right derived functors of the global sections functors on `𝒪`-modules. It is the
Grothendieck spectral sequence of the composite `Γ(Y, -) ∘ f_* = Γ(X, -)`: injective
`𝒪_X`-modules are flasque, direct images of flasque modules are flasque, and flasque modules are
acyclic for `Γ`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.globalSectionsFunctor`: the global sections functor
  `Γ(X, -) : X.Modules ⥤ Ab`, whose right derived functors are the cohomology groups.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.rightAcyclic_globalSectionsFunctor_of_isFlasque`: flasque
  modules are `Γ`-acyclic.
- `AlgebraicGeometry.Scheme.Modules.exists_leraySpectralSequence`: the Leray spectral sequence.
- `AlgebraicGeometry.Scheme.Modules.exists_leray_lowDegree_exact`: its exact sequence of low
  degree terms.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-- The **global sections functor** `Γ(X, -) : X.Modules ⥤ Ab` on `𝒪_X`-modules. Its right
derived functors `R^p Γ(X, -)` are the cohomology functors `H^p(X, -)`, just as the right derived
functors of the direct image `f_*` are the higher direct images
`AlgebraicGeometry.Scheme.Modules.higherDirectImage`; a short exact sequence of `𝒪_X`-modules
gives a long exact sequence of these derived functors
(`CategoryTheory.ShortComplex.ShortExact.exists_rightDerived_δ_exact`).

(blueprint: `pqf-def-cohomology`) -/
noncomputable def globalSectionsFunctor : X.Modules ⥤ AddCommGrpCat.{u} :=
  toPresheaf X ⋙ (CategoryTheory.evaluation _ _).obj (op ⊤)

instance : (globalSectionsFunctor X).Additive :=
  sorry

variable {X}

/-- **Flasque modules are acyclic for global sections**: if the underlying abelian presheaf of
an `𝒪_X`-module `ℱ` is flasque, then `R^p Γ(X, ℱ) = 0` for `p > 0`. -/
theorem rightAcyclic_globalSectionsFunctor_of_isFlasque [HasInjectiveResolutions X.Modules]
    (ℱ : X.Modules) (h : TopCat.Presheaf.IsFlasque ℱ.presheaf) :
    (globalSectionsFunctor X).rightAcyclic ℱ :=
  sorry

variable {Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The Leray spectral sequence.** For a morphism of schemes `f : X ⟶ Y` and an `𝒪_X`-module
`ℱ` there is a first quadrant spectral sequence
`E₂^{p,q} = H^p(Y, R^q f_* ℱ) ⇒ H^{p+q}(X, ℱ)`, where `H^p(Y, -) = R^p Γ(Y, -)` and
`H^n(X, -) = R^n Γ(X, -)`. It is the Grothendieck spectral sequence of `Γ(Y, -) ∘ f_*`.

(blueprint: `pqf-lem-leray`) -/
theorem exists_leraySpectralSequence [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions Y.Modules] (ℱ : X.Modules) :
    ∃ E : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{u},
      (∀ p q : ℕ, Nonempty ((E.page 2).X (p, q) ≅
        ((globalSectionsFunctor Y).rightDerived p).obj ((higherDirectImage f q).obj ℱ))) ∧
      E.AbutsTo (fun n ↦ ((globalSectionsFunctor X).rightDerived n).obj ℱ) :=
  sorry

/-- **The exact sequence of low degree terms of the Leray spectral sequence.** For a morphism
`f : X ⟶ Y` and an `𝒪_X`-module `ℱ` there is an exact sequence
`0 ⟶ H¹(Y, f_* ℱ) ⟶ H¹(X, ℱ) ⟶ H⁰(Y, R¹ f_* ℱ) ⟶ H²(Y, f_* ℱ)`.

(blueprint: `pqf-lem-leray-lowdegree`) -/
theorem exists_leray_lowDegree_exact [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions Y.Modules] (ℱ : X.Modules) :
    ∃ (a : ((globalSectionsFunctor Y).rightDerived 1).obj ((pushforward f).obj ℱ) ⟶
        ((globalSectionsFunctor X).rightDerived 1).obj ℱ)
      (b : ((globalSectionsFunctor X).rightDerived 1).obj ℱ ⟶
        ((globalSectionsFunctor Y).rightDerived 0).obj ((higherDirectImage f 1).obj ℱ))
      (c : ((globalSectionsFunctor Y).rightDerived 0).obj ((higherDirectImage f 1).obj ℱ) ⟶
        ((globalSectionsFunctor Y).rightDerived 2).obj ((pushforward f).obj ℱ))
      (hab : a ≫ b = 0) (hbc : b ≫ c = 0),
      Mono a ∧ (ShortComplex.mk a b hab).Exact ∧ (ShortComplex.mk b c hbc).Exact :=
  sorry

/-- If `R¹ f_* ℱ = 0`, then `H¹(X, ℱ) ≅ H¹(Y, f_* ℱ)`.

(blueprint: `pqf-lem-leray-lowdegree`) -/
theorem nonempty_rightDerived_one_iso_of_isZero [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions Y.Modules] (ℱ : X.Modules)
    (h : IsZero ((higherDirectImage f 1).obj ℱ)) :
    Nonempty (((globalSectionsFunctor Y).rightDerived 1).obj ((pushforward f).obj ℱ) ≅
      ((globalSectionsFunctor X).rightDerived 1).obj ℱ) :=
  sorry

end AlgebraicGeometry.Scheme.Modules
