module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Algebra.Homology.ModuleStalkExact
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.Images

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Stalk exactness identifies the range of the stalk image inclusion with the
range of the stalk map. This is the image part of the proof of
`ideal_multiplication_stalk_range`.
Source: Stacks Project, Modules, Lemma 01AG.
(blueprint: lem-weil-pbc-ideal-multiplication-stalk-range-image).
-/
theorem stalk_image_inclusion_range {X : Scheme.{u}}
    {M N : X.Modules} (f : M ⟶ N) (x : X) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    LinearMap.range (S.map (image.ι f)).hom = LinearMap.range (S.map f).hom := by
  sorry

end
end AlgebraicGeometry.Scheme
