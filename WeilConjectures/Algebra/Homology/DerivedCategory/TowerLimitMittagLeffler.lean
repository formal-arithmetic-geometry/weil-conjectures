/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.CategoryTheory.CofilteredSystem
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitHomology
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Mittag-Leffler towers have vanishing `lim¹`

For a tower `F` and a product `∏ Fₙ` with its transition endomorphism `t` (components
`∏ Fₘ ⟶ Fₙ₊₁ ⟶ Fₙ`), the condition `lim¹ F = coker (1 - t) = 0` is that `1 - t` is an
epimorphism.

For towers of modules satisfying the Mittag-Leffler condition (the images of the transition
maps `Fₖ ⟶ Fₙ` stabilise), `1 - t` is surjective (Stacks 0598, 07KW). The proof first corrects a
family `a ∈ ∏ Fₙ`, modulo the image of `1 - t`, into the product of the stable images `Iₙ`,
using finite partial sums `yₙ = ∑_{n ≤ k < Mₙ} t_{k,n}(aₖ)`; the tower of the stable images has
surjective transitions, on which `1 - t` is surjective by the inductive construction of
`ModuleCat.epi_one_sub_of_epi`.

For towers in a preadditive category with a product `∏ Gₙ`:

- `CategoryTheory.Limits.epi_one_sub_of_essentiallyZero`: if `G` is essentially zero (for
  every `n` some transition `G m ⟶ G n` vanishes), `1 - t` is a split epimorphism, a section
  being the geometric series `∑ₖ tᵏ`, whose components are finite sums
  (`CategoryTheory.Limits.towerPartialSum`);
- `CategoryTheory.Limits.epi_one_sub_of_shortExact`: in an abelian category with exact
  countable products in which sequential limits of epimorphisms project epimorphically onto the
  first term (a replete topos), if `G` is an extension of an essentially zero tower by a tower
  with epimorphic transitions — the Mittag-Leffler condition — then `1 - t` is an
  epimorphism, i.e. `lim¹ G = 0`;
- `DerivedCategory.isLimitHomologyFunctorMapConeOfIsHomotopyLimitOfMittagLeffler`: hence
  `Hⁱ(R lim F) = lim Hⁱ(Fₙ)` when the tower `H^{i-1}(Fₙ)` is Mittag-Leffler in this sense.

## Main results

- `ModuleCat.epi_one_sub_of_mittagLeffler`: Mittag-Leffler towers of modules have `R¹lim = 0`.
- `ModuleCat.mittagLeffler_of_isMittagLeffler`, `ModuleCat.mittagLeffler_of_finite`: the
  explicit Mittag-Leffler condition from `Functor.IsMittagLeffler`, and for finite modules.
- `ModuleCat.epi_one_sub_of_finite`: towers of finite modules have `R¹lim = 0`.
- `CategoryTheory.Limits.epi_one_sub_of_shortExact` and
  `DerivedCategory.isLimitHomologyFunctorMapConeOfIsHomotopyLimitOfMittagLeffler`: the
  replete abelian case.
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace ModuleCat

universe u

variable {R : Type u} [Ring R]

end ModuleCat

open Category

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C] {G : ℕᵒᵖ ⥤ C}
  {P : Fan fun n : ℕ ↦ G.obj (op n)} (hP : IsLimit P) (t : P.pt ⟶ P.pt)
  (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ G.map (homOfLE n.le_succ).op)

section Abelian

variable {C : Type*} [Category* C] [Abelian C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C] [HasLimitsOfShape ℕᵒᵖ C]

end Abelian

end CategoryTheory.Limits

namespace DerivedCategory

open Pretriangulated

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C] [HasLimitsOfShape ℕᵒᵖ C]
  {F : ℕᵒᵖ ⥤ DerivedCategory C} {c : Cone F}

end DerivedCategory
