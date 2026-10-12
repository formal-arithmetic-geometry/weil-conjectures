module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- Finite type is local for an open cover when each restricted module is coherent.
Source: Stacks Project, Definitions 01BV and 01B5 and Lemma 01B6.
(blueprint: lem-weil-pbc-coherent-module-finite-type-local-cover)
-/
theorem coherent_module_finite_type_local_cover
    (X : Scheme.{u}) (F : X.Modules) (I : Type u)
    (U : I → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hF : ∀ (i : I), RingedSpace.IsCoherent (U i).toScheme.toRingedSpace
      ((Scheme.Modules.restrictFunctor (U i).ι).obj F)) :
    F.IsFiniteType := by sorry

end AlgebraicGeometry
