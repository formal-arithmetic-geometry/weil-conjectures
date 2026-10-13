module

public import Sheaf.Algebra.Homology.LocalizedTensorComparisonProperty

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]

/-- The ordinary tensor comparison commutes with the canonical first-variable shift maps.
Source: Stacks Project, Tag 0BYJ, and the first-variable tensor shift used in Tag 0DJA(1).

Proof: the scalar-extension shift map is the identity in each degree. On a summand
U^p tensor Q^q, the first-variable tensor shift only reindexes p and has no sign.
The inverse monoidal comparison sends c tensor (u tensor q) to
(c tensor u) tensor (1 tensor q). Both paths send this generator to the same
reindexed tensor, then apply t to its second factor. Tensor induction and the universal
property of the total-complex coproduct give equality in every degree, hence equality
of complex maps. The differentials commute because each constituent is a complex map.
This also works for n=0, zero factors and t=0, and uses no derived model or flatness.
(blueprint: lem-pc-localized-tensor-comparison-shift-square-transport). -/
theorem localizedTensorComparison_shift_transport
    (U Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : CochainComplex (ModuleCat.{u} C) ℤ) (n : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    ∀ (t : F.obj Q ⟶ N),
    let eK := F.mapIso (CochainComplex.mapBifunctorShift₁Iso U Q
      (curriedTensor (ModuleCat.{u} A)) (-n)) ≪≫ (F.commShiftIso (-n)).app (U ⊗ Q)
    let eT := tensorIso ((F.commShiftIso (-n)).app U) (Iso.refl N) ≪≫
      CochainComplex.mapBifunctorShift₁Iso (F.obj U) N
        (curriedTensor (ModuleCat.{u} C)) (-n)
    (Functor.Monoidal.μIso F (U⟦-n⟧) Q).inv ≫ (F.obj (U⟦-n⟧) ◁ t) ≫ eT.hom =
      eK.hom ≫ ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t))⟦-n⟧' := by
  sorry

end ModuleCat
