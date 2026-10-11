/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.CategoryTheory.Filtration

/-!
# Relative Leray spectral sequences on small etale sites

Source: Stacks Project, Tags 0734 and 015N
(blueprint: lem-weil-pbc-grothendieck-spectral-sequence).

The spectral sequence is in the functor category of sheaves on the source with values in
sheaves on the target. Its evaluation at any sheaf is the desired spectral sequence;
all page identifications, filtration subobjects and graded identifications are natural.
Module-valued sheaves encode modules over the constant sheaf of rings: constant scalars
extend uniquely to locally constant scalars by the sheaf condition.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The relative Leray spectral sequence, functorial in every source sheaf, with finite
filtrations and the stable-page graded identifications.
Source: Stacks Project, Tags 0734, 015M, 015N and 0730
(blueprint: lem-weil-pbc-grothendieck-spectral-sequence).

Proof:
1. The three module-sheaf categories are Grothendieck abelian and have enough injectives
   (`lem-weil-pbc-module-sheaves-grothendieck-abelian`). Direct image is additive and left
   exact, being right adjoint to exact inverse image
   (`prop-weil-pbc-inverse-image-modules-exact`).
2. Pullback pasting identifies the composite direct image with direct image of the
   composite (`lem-weil-pbc-cartesian-square-pasting`), naturally on sections and sheaves.
   Applying one injective resolution identifies their right derived functors.
3. Direct image preserves injectives (`lem-weil-pbc-direct-image-preserves-injectives`),
   hence sends injectives to objects acyclic for the second direct image. This imposes
   no acyclicity condition on the input sheaf.
4. Apply `thm-sp-grothendieck`: take an injective resolution, a Cartan--Eilenberg resolution
   of its direct image, and the spectral sequence of the second direct image of that
   bicomplex. Its second page and abutment are the displayed derived functors.
5. First-quadrant support kills incoming differentials when r > p and outgoing ones
   when r > q + 1. Pages stabilize above max(p,q+1). The image filtration of the total
   complex starts at the whole degree-n cohomology and is zero at n+1, with graded pieces
   the stable page (`def-sp-image-filtration`, `def-sp-convergence`). These constructions
   and their comparison isomorphisms are natural in the source sheaf.
6. For integer coefficients, abelian sheaves carry a unique action of the constant
   integer sheaf and their morphisms are linear. Thus the same construction gives the
   abelian-sheaf version. Bounded-below injective resolutions are K-injective
   (`lem-sp-kinjective-computes`), identifying right derived functors with the cohomology
   of the derived direct image, as stated separately below. -/
theorem exists_module_grothendieck_spectralSequence (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Y ⟶ Z) :
    let A := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    let C := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    let fStar := lowerStar (ModuleCat.{u + 1} Λ) f
    let hStar := lowerStar (ModuleCat.{u + 1} Λ) h
    let hfStar := lowerStar (ModuleCat.{u + 1} Λ) (f ≫ h)
    ∃ E : E₂CohomologicalSpectralSequence (A ⥤ C),
      (∀ p q : ℕ, Nonempty
        ((E.page 2).X ((p : ℤ), (q : ℤ)) ≅ fStar.rightDerived q ⋙ hStar.rightDerived p)) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2).X (p, q))) ∧
      (∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℕ), max (p : ℤ) ((q : ℤ) + 1) < r →
        Nonempty ((E.page (r + 1)).X ((p : ℤ), (q : ℤ)) ≅
          (E.page r hr).X ((p : ℤ), (q : ℤ)))) ∧
      ∃ filtration : ∀ n : ℕ, DecreasingFiltration (hfStar.rightDerived n),
        (∀ n : ℕ, (filtration n).step 0 = ⊤ ∧
          IsZero ((filtration n).step ((n : ℤ) + 1) : A ⥤ C)) ∧
        ∀ (n p : ℕ), p ≤ n → ∀ (r : ℤ) (hr : 2 ≤ r),
          max (p : ℤ) (((n - p : ℕ) : ℤ) + 1) < r →
          Nonempty ((filtration n).gradedPiece (p : ℤ) ≅
            (E.page r hr).X ((p : ℤ), ((n - p : ℕ) : ℤ))) := by
  sorry

/-- The relative Leray spectral sequence, functorial in every source sheaf, with finite
filtrations and the stable-page graded identifications.
Source: Stacks Project, Tags 0734, 015M, 015N and 0730
(blueprint: lem-weil-pbc-grothendieck-spectral-sequence).

Proof:
1. The three module-sheaf categories are Grothendieck abelian and have enough injectives
   (`lem-weil-pbc-module-sheaves-grothendieck-abelian`). Direct image is additive and left
   exact, being right adjoint to exact inverse image
   (`prop-weil-pbc-inverse-image-modules-exact`).
2. Pullback pasting identifies the composite direct image with direct image of the
   composite (`lem-weil-pbc-cartesian-square-pasting`), naturally on sections and sheaves.
   Applying one injective resolution identifies their right derived functors.
3. Direct image preserves injectives (`lem-weil-pbc-direct-image-preserves-injectives`),
   hence sends injectives to objects acyclic for the second direct image. This imposes
   no acyclicity condition on the input sheaf.
4. Apply `thm-sp-grothendieck`: take an injective resolution, a Cartan--Eilenberg resolution
   of its direct image, and the spectral sequence of the second direct image of that
   bicomplex. Its second page and abutment are the displayed derived functors.
5. First-quadrant support kills incoming differentials when r > p and outgoing ones
   when r > q + 1. Pages stabilize above max(p,q+1). The image filtration of the total
   complex starts at the whole degree-n cohomology and is zero at n+1, with graded pieces
   the stable page (`def-sp-image-filtration`, `def-sp-convergence`). These constructions
   and their comparison isomorphisms are natural in the source sheaf.
6. For integer coefficients, abelian sheaves carry a unique action of the constant
   integer sheaf and their morphisms are linear. Thus the same construction gives the
   abelian-sheaf version. Bounded-below injective resolutions are K-injective
   (`lem-sp-kinjective-computes`), identifying right derived functors with the cohomology
   of the derived direct image, as stated separately below. -/
theorem exists_abelian_grothendieck_spectralSequence {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Y ⟶ Z) :
    let A := Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
    let C := Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}
    let fStar := lowerStar AddCommGrpCat.{u + 1} f
    let hStar := lowerStar AddCommGrpCat.{u + 1} h
    let hfStar := lowerStar AddCommGrpCat.{u + 1} (f ≫ h)
    ∃ E : E₂CohomologicalSpectralSequence (A ⥤ C),
      (∀ p q : ℕ, Nonempty
        ((E.page 2).X ((p : ℤ), (q : ℤ)) ≅ fStar.rightDerived q ⋙ hStar.rightDerived p)) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2).X (p, q))) ∧
      (∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℕ), max (p : ℤ) ((q : ℤ) + 1) < r →
        Nonempty ((E.page (r + 1)).X ((p : ℤ), (q : ℤ)) ≅
          (E.page r hr).X ((p : ℤ), (q : ℤ)))) ∧
      ∃ filtration : ∀ n : ℕ, DecreasingFiltration (hfStar.rightDerived n),
        (∀ n : ℕ, (filtration n).step 0 = ⊤ ∧
          IsZero ((filtration n).step ((n : ℤ) + 1) : A ⥤ C)) ∧
        ∀ (n p : ℕ), p ≤ n → ∀ (r : ℤ) (hr : 2 ≤ r),
          max (p : ℤ) (((n - p : ℕ) : ℤ) + 1) < r →
          Nonempty ((filtration n).gradedPiece (p : ℤ) ≅
            (E.page r hr).X ((p : ℤ), ((n - p : ℕ) : ℤ))) := by
  sorry

/-- Higher direct images of abelian sheaves are the cohomology of derived direct image.
Source: Stacks Project, Tags 0734 and 015N
(blueprint: lem-weil-pbc-grothendieck-spectral-sequence).

Proof: take an injective resolution of the source sheaf. It is bounded below and hence
K-injective (`lem-sp-kinjective-computes`). Derived direct image is therefore computed
by applying direct image to that resolution. Its degree-q cohomology computes the
injective-resolution right derived functor (`def-sp-left-exact-additive`). The comparison
is natural in the sheaf, since both constructions apply direct image to resolution maps.
This applies to each of f, h and their composite in the spectral-sequence statement. -/
theorem abelian_rightDerived_iso_higherDirectImage {X Y : Scheme.{u}} (g : X ⟶ Y)
    (q : ℕ) :
    Nonempty ((lowerStar AddCommGrpCat.{u + 1} g).rightDerived q ≅
      DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} g ⋙
          DerivedCategory.Plus.homologyFunctor
            (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)) := by
  sorry

end AlgebraicGeometry.Etale
