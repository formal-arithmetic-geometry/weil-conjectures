/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.Abelian.HomologyFilteredColimit

/-!
# Morphisms out of an object of `D(C)` commuting with filtered colimits

Let `C` be an abelian category and `s` an object of its derived category. We say that
`Hom(s, -[n])` *commutes with filtered colimits* of objects of `C`
(`DerivedCategory.HomCommutesWithFilteredColimits`) if for every filtered colimit
`B = colim Bᵢ` in `C` and every `n`, the canonical map `colim Hom(s, Bᵢ[n]) ⟶ Hom(s, B[n])` is
bijective. This is blueprint `sk-lem-constructible-ext-continuity` for targets in degree `0`.

* The class of such `s` contains zero, is closed under isomorphisms, shifts and extensions
  (blueprint `det-lem-constructible-ext-continuity-devissage`, five lemma).
* For `s` bounded above, the comparison is then bijective for every filtered diagram `Yᵢ` in
  `D(C)` of uniformly bounded below objects with a cocone `Y` inducing colimits on cohomology
  (`DerivedCategory.HomCommutesWithFilteredColimits.diagram`), by induction on the amplitude
  along the truncation triangles.
* The class is transported along adjunctions `F ⊣ G` whose right adjoint `G` is left
  `t`-exact up to a shift and commutes with filtered colimits on cohomology
  (`DerivedCategory.HomCommutesWithFilteredColimits.of_adjunction`), and along adjunctions of
  exact functors whose right adjoint preserves filtered colimits
  (`DerivedCategory.HomCommutesWithFilteredColimits.mapDerivedCategory`).

The proofs go through the general notion `CategoryTheory.Limits.Cocone.IsCoyonedaColimit s c`
(every morphism `s ⟶ c.pt` factors through the diagram, and a morphism `s ⟶ X i` vanishing in
`c.pt` vanishes in some `X j`), for which we prove the five lemmas in a pretriangulated
category, in the source (`Cocone.IsCoyonedaColimit.of_distTriang_source`) and in the target
(`Cocone.IsCoyonedaColimit.of_distTriang_target`), and the transport along adjunctions
(`Cocone.IsCoyonedaColimit.adjunction_iff`).
-/

@[expose] public section

universe w

open CategoryTheory Category Limits Pretriangulated Preadditive

namespace CategoryTheory.Pretriangulated.Triangle

section

variable {D : Type*} [Category* D] [Preadditive D] [HasShift D ℤ]

end

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

end CategoryTheory.Pretriangulated.Triangle

namespace CategoryTheory.Limits.Cocone

section Preadditive

variable {D : Type*} [Category* D] [Preadditive D]

namespace IsCoyonedaColimit

variable {I : Type*} [Category* I]

end IsCoyonedaColimit

end Preadditive

section Pretriangulated

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace IsCoyonedaColimit

variable {I : Type*} [Category* I] [IsFiltered I]

end IsCoyonedaColimit

end Pretriangulated

end CategoryTheory.Limits.Cocone

namespace DerivedCategory

open TStructure (t)
open Cocone

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

section Truncation

variable {I : Type*} [Category* I] {Y : I ⥤ DerivedCategory C} {c : Cocone Y}

end Truncation

namespace HomCommutesWithFilteredColimits

variable {C' : Type*} [Category* C'] [Abelian C'] [HasDerivedCategory C']

end HomCommutesWithFilteredColimits

end DerivedCategory
