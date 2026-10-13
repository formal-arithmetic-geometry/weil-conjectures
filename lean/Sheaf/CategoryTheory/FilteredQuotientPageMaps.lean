/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Sheaf.CategoryTheory.FilteredComplexPageDifferential

/-!
# Canonical maps between concrete quotient pages

Source: Stacks Project, Tag 012K, Lemmas 12.24.2 and 12.24.4.
(blueprint: lem-sp-filtered-quotient-page-maps).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The four representative squares specify a map on quotient pages.
Source: Stacks Project, Tag 012K, Lemma 12.24.4.
(blueprint: lem-sp-filtered-quotient-page-maps). -/
def FilteredQuotientPageMapProperty
    (U V : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (t : U ⟶ V) (r : ℤ)
    (DU : FilteredComplexPageDifferential U.obj.obj U.obj.filtration r)
    (DV : FilteredComplexPageDifferential V.obj.obj V.obj.filtration r)
    (m : DU.page ⟶ DV.page) : Prop :=
  ∀ (p q : ℤ)
    (s : ∀ a : ℤ, (U.obj.filtration.step a : CochainComplex C ℤ) ⟶
      (V.obj.filtration.step a : CochainComplex C ℤ))
    (g : U.obj.filtration.gradedPiece p ⟶ V.obj.filtration.gradedPiece p)
    (kz : (U.obj.filtration.complexCycles p (p + q) r : C) ⟶
      (V.obj.filtration.complexCycles p (p + q) r : C))
    (k : filteredComplexPageObject U.obj.obj U.obj.filtration r (p, q) ⟶
        filteredComplexPageObject V.obj.obj V.obj.filtration r (p, q))
    (hs : ∀ i : ℤ, s i ≫ (V.obj.filtration.step i).arrow =
      (U.obj.filtration.step i).arrow ≫ t.hom.hom)
    (hg : U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
        s p ≫ V.obj.filtration.complexQuotientπ p (p + 1) (by omega))
    (hkz : kz ≫ (V.obj.filtration.complexCycles p (p + q) r).arrow =
      (U.obj.filtration.complexCycles p (p + q) r).arrow ≫ g.f (p + q))
    (hk : filteredComplexPageπ U.obj.obj U.obj.filtration r (p, q) ≫ k =
        kz ≫ filteredComplexPageπ V.obj.obj V.obj.filtration r (p, q)),
    m.f (p, q) = k

/-- The quotient page maps exist, obey the category laws, and are determined uniquely.
This statement constructs no successor-page comparison.
Source: Stacks Project, Tag 012K, Lemmas 12.24.2 and 12.24.4.
(blueprint: lem-sp-filtered-quotient-page-maps).

Proof. Restrict a filtered map to every step by its preservation property; these
restrictions are unique after the monic step inclusions. Descend to each graded
piece by the cokernel universal property. Preservation of the pullback defining
cycle representatives induces a map on their graded images. Preservation of the
boundary images makes it descend to the quotient Z_r/B_r. On the epic cover by
cycle representatives, the chain map equation shows that this quotient map
commutes with the representative differentials, hence gives a page chain map.
Cancel the monic cycle inclusion and epic quotient projection to show that any
four squares specify this same map. The squares for identity maps use identity
restrictions; the squares for composites use composites of restrictions. The same
cancellation proves the identity and composition laws. Finally the canonical
restrictions and descents provide squares for each filtered map, so the universal
square property determines every component, and therefore the whole family. -/
theorem filteredQuotient_page_maps
    (D : ∀ (U : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (r : ℤ) (hr : 1 ≤ r),
      FilteredComplexPageDifferential U.obj.obj U.obj.filtration r) :
    ∃! m : ∀ {U V : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)} (t : U ⟶ V)
        (r : ℤ) (hr : 1 ≤ r), (D U r hr).page ⟶ (D V r hr).page,
      (∀ U r hr, m (𝟙 U) r hr = 𝟙 _) ∧
      (∀ U V W (t : U ⟶ V) (t' : V ⟶ W) r hr,
        m (t ≫ t') r hr = m t r hr ≫ m t' r hr) ∧
      (∀ U V (t : U ⟶ V) r hr,
        FilteredQuotientPageMapProperty (C := C) U V t r (D U r hr) (D V r hr) (m t r hr)) := by
  sorry

end CategoryTheory
