/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.FilteredComplexBoundariesLECycles

/-! # Row boundaries in the second graded filtration

Source: Stacks Project, Homology, Tags 0130 and 012K.
(blueprint: lem-sp-second-filtration-row-boundary-subobject).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- Under the normalized cycle comparison the first-page boundary subobject is
exactly the image of the incoming row differential into row cycles.
Source: Stacks Project, Tag 0130, clauses 2 and 4; Tag 012K, boundary formula.
(blueprint: lem-sp-second-filtration-row-boundary-subobject).

Proof. The diagonal projection and lift identify the graded row term in each
resolution degree with the corresponding mapped row term. The total differential
has a resolution component and a component raising s; the latter lands in the
next filtration step. Therefore the incoming graded differential corresponds to
the incoming row differential. For r>0 its source is the mapped row term r-1,
and the extension isomorphism identifies its image in the kernel of the outgoing
differential with image(toCycles). The first-page boundary formula says that the
filtered boundary subobject in the graded term is this image of the incoming
graded differential. Factoring it through the cycle mono gives the inclusion
used below. The two normalization equations fix c by monicity, so pulling this
boundary subobject back along c.hom recovers the row boundary image.
For r=0 the incoming extended row term has resolution degree -1 and is zero;
the row differential from prev 0 = 0 to 0 is also zero, so both images are bottom.
The interval argument is [s,s+r] and includes negative s. If a row is zero the
cycle objects and both boundary subobjects are zero. No quotient or homology
isomorphism is asserted or used in this comparison.
-/
theorem secondFiltration_row_boundary_subobject
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (L : DecreasingFiltration
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).secondFiltration n).step
        p)
    (r : ℕ) (s : ℤ)
    (t : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).cycles r ⟶
      (L.step s : CochainComplex B ℤ).X (s + (r : ℤ)))
    (ht : t ≫ (L.step s).arrow.f (s + (r : ℤ)) =
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).iCycles r ≫
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).extendXIso
        ComplexShape.embeddingUpNat (by rfl)).inv ≫
        (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).ιTotal
          (ComplexShape.up ℤ) (r : ℤ) s (s + (r : ℤ)) (by
            change (r : ℤ) + s = s + (r : ℤ)
            omega)))
    (c : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).cycles r ≅
      (L.complexCycles s (s + (r : ℤ)) 1 : B))
    (hc : c.hom ≫ (L.complexCycles s (s + (r : ℤ)) 1).arrow =
      t ≫ (L.complexQuotientπ s (s + 1) (by omega)).f (s + (r : ℤ))) :
    (Subobject.pullback c.hom).obj (imageSubobject (Subobject.ofLE _ _
      (filteredComplex_boundaries_le_cycles
        ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
          (ComplexShape.up ℤ)) L s (s + (r : ℤ)) 1))) =
      imageSubobject
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).toCycles
          ((ComplexShape.up ℕ).prev r) r) := by sorry

end CategoryTheory.Functor
