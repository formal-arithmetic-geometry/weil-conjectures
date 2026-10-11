/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Hom into an essentially constant ind-diagram

Source: Stacks Project, Categories, Tag 05PY; Derived Categories, Tag 0FND,
first equality in the proof (blueprint: lem-pc-essentially-constant-ind-hom-colimit).
-/

@[expose] public section

universe uJ vJ uC vC

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- For an essentially constant filtered ind-diagram with value `X`, the canonical map
from the colimit of `Hom(Y, F(j))` to `Hom(Y, X)` is bijective. The cocone is the one
selected from the essential-constancy witness `h`; its maps send `f` to `f ≫ p.app j`.

Source: Stacks Project, Categories, Tag 05PY, implication (1) to (2); Derived Categories,
Tag 0FND, first equality (blueprint: lem-pc-essentially-constant-ind-hom-colimit).

Proof: use the natural maps `p`, stage `j₀`, and section `s` from
`def-pc-essentially-constant-ind-diagram`.
1. Naturality of `p` makes the map on representatives descend to the Hom colimit.
2. For any `g : Y ⟶ X`, the representative `g ≫ s` at `j₀` maps to `g`, since
   `s ≫ p.app j₀ = 𝟙 X`. This proves surjectivity.
3. If representatives `f` and `f'` have equal images, apply the factorization clause
   separately at their stages. Filteredness gives a common stage for the two resulting
   stages. Coequalize the resulting two arrows from `j₀` by filteredness once more.
4. At this later stage both transition composites factor as `p.app j ≫ s` followed by
   the same arrow from `F.obj j₀`. The equality of images therefore gives equality of
   the transported representatives, proving injectivity in the quotient colimit.
5. Composition shows compatibility with maps of `Y` (contravariantly) and of cocones,
   so this is the canonical bijection used in Tag 0FND. -/
theorem essentiallyConstantInd_hom_colimit_bijective
    {J : Type uJ} {C : Type uC} [Category.{vJ} J] [Category.{vC} C]
    (F : J ⥤ C) (X : C) (h : IsEssentiallyConstantIndDiagram F X) (Y : C) :
    Function.Bijective
      ((F ⋙ coyoneda.obj (op Y)).descColimitType
        ((F ⋙ coyoneda.obj (op Y)).coconeTypesEquiv.symm
          ((coyoneda.obj (op Y)).mapCocone { pt := X, ι := h.2.choose }))) := by
  sorry

end CategoryTheory
