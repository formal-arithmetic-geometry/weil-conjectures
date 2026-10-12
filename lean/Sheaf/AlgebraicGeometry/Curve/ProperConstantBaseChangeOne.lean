module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.IsCurve
variable {Λ : Type (u + 1)}
variable [CommRing Λ]
variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
  (f : C ⟶ Spec (.of k))
/-- Proper constant-sheaf base change in the one degree.
(blueprint: lemma-weil-pbc-smooth-curve-proper-base-change-one)
Proof: apply the corresponding degree part of the proper base-change argument. -/
theorem proper_constant_base_change_one [IsCurve f] [Smooth f] [ConnectedSpace C]
    [IsProper f] (r : ℕ) [Fact r.Prime] (k' : Type u) [Field k']
    [IsAlgClosed k']
    {C' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) 1) := by sorry
end AlgebraicGeometry.IsCurve
