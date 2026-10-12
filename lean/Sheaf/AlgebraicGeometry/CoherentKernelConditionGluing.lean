module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Restrict

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Construct finite local-generators data for a kernel from the corresponding kernel
condition on an open cover.  The construction restricts the global map to each
intersection with a member of the cover, uses sectionwise computation of kernels,
and transports finite generators across the resulting restriction isomorphisms.
The cover equality supplies, for every point, a member and a neighbourhood on which
these generators apply; assembling those neighbourhoods is the required local
generators datum.  This is the gluing step in the proof of finite-type descent.
Source: Stacks Project, Modules, Definitions 01BV and 01B5 and Section 01AF.
(blueprint: lem-weil-pbc-coherent-kernel-condition-descent-local-generators). -/
theorem coherent_kernel_condition_local_generators
    (X : Scheme.{u}) (F : X.Modules)
    (I : Type u) (U : I → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hK : ∀ (i : I) (V : (U i).toScheme.Opens) (n : ℕ)
      (f : SheafOfModules.free (R := (U i).toScheme.ringCatSheaf.over V)
        (ULift.{u} (Fin n)) ⟶ ((Scheme.Modules.restrictFunctor (U i).ι).obj F).over V),
      (kernel f).IsFiniteType)
    (W : X.Opens) (n : ℕ)
    (f : SheafOfModules.free (R := X.ringCatSheaf.over W) (ULift.{u} (Fin n)) ⟶
      F.over W) :
    ∃ σ : (kernel f).LocalGeneratorsData, σ.IsFiniteType := by
  sorry

end AlgebraicGeometry
