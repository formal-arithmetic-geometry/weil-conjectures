/-
Copyright (c) 2026 Weil SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF contributors
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Rationalization
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Localization.Predicate

import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Localization.Linear

/-!
# A scalar-fraction criterion for a localization functor

Source: main-20261015 blueprint, `thm-sfb-extend-scalars-localization.proof.md`,
"Morphisms of the rationalization", "Full faithfulness", and the conclusion
(blueprint: lem-sfb-rationalization-localization-hom-criterion).
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Rationalization

/-- A scalar-fraction criterion for the functor induced from the rationalization to be
fully faithful and essentially surjective, and for the original functor to be a localization.

Source: main-20261015 blueprint, `thm-sfb-extend-scalars-localization.proof.md`,
"Morphisms of the rationalization", "Full faithfulness", and the conclusion
(blueprint: lem-sfb-rationalization-localization-hom-criterion).

Proof plan:
1. The rationalization `Q M C` is an additive localization with its canonical linear
   structure (`lem-sfb-additive-localization-linear`); its objects are essentially images
   of objects of `C`, and scalars in `M` act invertibly (`sk-def-sfb-rationalization`).
2. Lift `F` using `lem-weil-pbc-localization-universal-property`. The factorization
   isomorphism and `lem-sfb-linear-localization-descent` make the lift scalar preserving.
3. Conjugating its Hom maps by the factorization isomorphism gives scalar-preserving maps
   `T` with `T (Q.map u) = F.map u` (`def-weil-linear-category`).
4. For a target arrow, `hSurj` gives `m • h = F.map u`. Divide `Q.map u` by the invertible
   scalar `m`, and cancel `m` on the target using `hUnits` to obtain surjectivity of `T`.
5. Write two source arrows as scalar fractions using
   `lem-sfb-rationalization-scalar-fractions`. Equal images imply that the cross-multiplied
   integral arrows have equal `F`-images; `hEq` gives one further annihilating scalar.
6. Apply `Q` and cancel the product of the three scalars, which is invertible in the
   rationalization (`sk-def-sfb-rationalization`), to obtain injectivity of `T`.
7. Transport the Hom bijections along isomorphisms from image objects to all objects.
   Essential surjectivity of `F` and the factorization isomorphism give that of the lift.
8. Apply `lem-trf-fully-faithful-ess-surj-equivalence` to the lift to obtain a quasi-inverse.
9. Precomposition with this equivalence, followed by precomposition with `Q`, transfers
   the functor-category universal property to `F`, using the factorization isomorphism
   (`lem-weil-pbc-localization-universal-property`).
-/
theorem localization_hom_criterion
    {R : Type w} [CommRing R]
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C] [IsTriangulated C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]
    (M : Submonoid R) (F : C ⥤ D) [F.Additive] [F.Linear R] [F.EssSurj]
    (hInv : (W M C).IsInvertedBy F)
    (hUnits : ∀ m ∈ M, ∀ Y : D, IsIso (m • 𝟙 Y))
    (hSurj : ∀ (A B : C) (h : F.obj A ⟶ F.obj B),
      ∃ m ∈ M, ∃ u : A ⟶ B, m • h = F.map u)
    (hEq : ∀ (A B : C) (u v : A ⟶ B), F.map u = F.map v →
      ∃ n ∈ M, n • u = n • v) :
    (Localization.lift F hInv (Q M C)).Full ∧
      (Localization.lift F hInv (Q M C)).Faithful ∧
      (Localization.lift F hInv (Q M C)).EssSurj ∧ F.IsLocalization (W M C) := by
  sorry

end CategoryTheory.Rationalization
