module
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace CommRingCat
/-- A filtered colimit cocone of domains has a domain as its vertex, transported
along an equality of the vertex with a specified ring.
(blueprint: new-filtered-colimit-domain-cocone)
The proof represents two factors at stages, lifts them to a common stage, and
uses the domain property there; filteredness detects the zero relation later. -/
theorem isDomain_of_filtered_colimit_cocone
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CommRingCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ i : I, IsDomain (D.obj i))
    {R : CommRingCat.{u}} (e : c.pt = R) : IsDomain R := by
  sorry
end CommRingCat
