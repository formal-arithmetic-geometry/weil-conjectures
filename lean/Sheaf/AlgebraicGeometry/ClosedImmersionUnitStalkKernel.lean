module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Stalk kernel calculation for a closed immersion

Source: Stacks Project, Modules, Lemma 08KS, using Sheaves, Lemmas 0098 and 00AE.
(blueprint: lem-weil-pbc-closed-immersion-unit-stalk-kernel).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- On a single stalk the range of ideal multiplication is the kernel of the pullback unit.
Source: Stacks Project, Modules, Lemma 08KS, using Sheaves, Lemmas 0098 and 00AE.
(blueprint: lem-weil-pbc-closed-immersion-unit-stalk-kernel).

Proof: Put J = i.ker. Outside i(Z), choose a neighbourhood disjoint from i(Z).
The pushforward module has zero stalk there. The ideal J has the whole ring as its stalk:
on affine neighbourhoods disjoint from i(Z), its defining ideal is the kernel of the map
into the zero ring. The range formula for toModulesι identifies these ideals with the
sections of J. Multiplication by the germ of 1 therefore shows that multiplication has
full range, equal to the kernel of the zero unit map.

At x = i(z), put R = O_{Y,x}, S = O_{Z,z}, and K = ker(R -> S). The closed immersion makes
R -> S surjective. On the affine neighbourhood basis, J is the kernel ideal of the
structure map, so exactness of stalks identifies the range of J_x -> R with K.
The tensor stalk comparison identifies the multiplication map with a tensor map
whose pure tensors a tensor m go to a*m; its range is K times F_x. The pullback stalk
comparison and the closed-pushforward stalk comparison identify the canonical unit
with m |-> 1 tensor m in S tensor_R F_x. Write S = R/K. The map from F_x/(K F_x)
to S tensor_R F_x has inverse r-bar tensor m |-> r*m mod K F_x: changing r by an element
of K changes r*m by an element of K F_x, and the formula respects addition and the
balanced tensor relation. These inverse maps show that the kernel of the canonical
unit is exactly K F_x. Thus both ranges in the claimed equality agree.

Finally any two adjunctions of these same functors differ by a natural isomorphism
of the left adjoint. Their units differ by postcomposition with its pushforward.
On stalks this is an invertible linear map, so it does not change the kernel. This
proves the assertion for the chosen adjunction as well. The zero module, empty closed
subscheme and identity immersion are included: the corresponding ideals are respectively
irrelevant, the whole ring, and zero. -/
theorem closedImmersion_unit_stalk_kernel {Y Z : Scheme.{w}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (F : Y.Modules) (x : Y) :
    let adj := Classical.choice (nonempty_tensorPullbackAdjunction i)
    let J : Y.IdealSheafData := i.ker
    let μ : J.toModules ⊗ F ⟶ F := J.toModulesι ▷ F ≫ (λ_ F).hom
    let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace x
    LinearMap.range (S.map μ).hom = LinearMap.ker (S.map (adj.unit.app F)).hom := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
