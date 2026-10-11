/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# The comparison principle for a K-injective target

Source: Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean, `Qh_map_bijective`
and `quasiIso_iff` (blueprint: lem-sp-kinjective-comparison-principle).
-/

universe w v u

open CategoryTheory

namespace CochainComplex.IsKInjective

/-- Precomposition by a quasi-isomorphism induces a bijection on homotopy classes of maps
into a K-injective complex, in any abelian category admitting the derived category.
Source: Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean, `Qh_map_bijective`
and `quasiIso_iff` (blueprint: lem-sp-kinjective-comparison-principle).

Proof: (1) By `lem-weil-pbc-kinjective-hom-derived` (`Qh_map_bijective`), localization
identifies maps from both `A` and `B` into `I` in the homotopy category with maps in the
 derived category. (2) By `def-weil-abstract-derived-category`, localization sends the
quasi-isomorphism `s` to an isomorphism. Precomposition with this isomorphism is bijective,
with inverse precomposition with its inverse. (3) Functoriality of localization identifies
precomposition by `s` with this bijection under the two identifications from (1).
Conjugating by these identifications proves the asserted bijectivity. -/
theorem precomp_bijective_of_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B : CochainComplex C ℤ} (s : A ⟶ B) [QuasiIso s]
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    Function.Bijective
      (fun g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj B ⟶
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I ↦
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map s ≫ g) := by
  sorry

end CochainComplex.IsKInjective
