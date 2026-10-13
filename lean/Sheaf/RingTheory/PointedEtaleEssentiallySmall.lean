module

public import Sheaf.RingTheory.IsStrictHenselization
public import Mathlib.CategoryTheory.EssentiallySmall

@[expose] public section
universe u
open CategoryTheory
namespace Algebra

/-- Essential smallness follows from finite-presentation representatives of affine etale
algebras and the set of pointings into a fixed K.
Source: Stacks Project, Algebra, Tag 04GW.
(blueprint: lem-sc-pointed-etale-essentially-small). -/
theorem pointedEtale_essentiallySmall
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K] [Algebra R K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K] :
    let P : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Etale R X.left
    EssentiallySmall.{u} P.FullSubcategory := by sorry
end Algebra
