module
public import Sheaf.Paper.ConstantCompletionBasic
/-! Constant quotient component of constant coefficient completion.
Source: Stacks Project, Tag 093M (blueprint: lem-weil-pbc-constant-completion-equivalence).
(blueprint: new-h2-constant-completion-quotient)
The finite constant quotient map is sectionwise surjective and has kernel generated
by the constant sections of the corresponding power of the ideal. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C]
theorem flat_and_quotients_quotient (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∀ (n : ℕ) (U : C),
      Function.Surjective ((quotient J A I n).hom.app (op U)) ∧
      RingHom.ker ((quotient J A I n).hom.app (op U)).hom =
        Ideal.span (Set.range (fun a : ↥(I ^ (n + 1)) ↦
          (constantSection (J := J) (a : A)).val (op U))) := by
  sorry
end CategoryTheory.ConstantCompletion
