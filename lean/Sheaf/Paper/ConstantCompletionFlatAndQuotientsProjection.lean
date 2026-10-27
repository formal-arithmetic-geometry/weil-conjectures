module
public import Sheaf.Paper.ConstantCompletionBasic
/-! Projection quotient component of constant coefficient completion.
Source: Stacks Project, Tag 093M (blueprint: lem-weil-pbc-constant-completion-equivalence).
(blueprint: new-h2-constant-completion-projection)
The sectionwise adic algebra limit argument identifies each original completion
projection with the quotient by the extended power of the coefficient ideal. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C]
theorem flat_and_quotients_projection (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∀ (n : ℕ) (U : C),
      Function.Surjective ((projection J A I n).hom.app (op U)) ∧
      RingHom.ker ((projection J A I n).hom.app (op U)).hom =
        Ideal.span (Set.range (fun a : ↥(I ^ (n + 1)) ↦
          (algebraSection (coefficientMap J A I) a).val (op U))) := by
  sorry
end CategoryTheory.ConstantCompletion
