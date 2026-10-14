module

public import Sheaf.AlgebraicGeometry.SquareZeroTensorGradedPresentation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- Multiplication descends from the homogeneous algebra to the quotient.
Source: Stacks Project, Tag 09MS, the graded algebra quotient.
(blueprint: lem-sc-square-zero-tensor-graded-quotient-multiply).
Proof: The closed-immersion adjunction unit on each tensor power is locally surjective:
on stalks it is the quotient by the immersion ideal, transported by the unique
adjunction comparison. Locally lift s and t through these units, refining their
covers to a common cover. The equation b_quotient identifies their images under c
with p applied to their b-images. Since p is an algebra morphism, their product is
p applied to the product of those b-images. Apply b_multiply and b_quotient in degree
a+d. Naturality and the monoidal adjunction comparison identify the image of the
tensor product of the lifts with the tensor product of s and t transported through
boundaryPullbackTensorIso. This proves the displayed equality on the common cover;
sheaf separation proves it globally. The argument also works in degree zero, where
tensorPowAddIso and the pullback tensor comparison use the unitors. -/
theorem tensorGradedQuotient_multiply {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) (T : TensorGradedPresentation j L)
    (a d : ℕ) (s : Γ((tensorPullback j).obj (L.tensorPow a), ⊤))
    (t : Γ((tensorPullback j).obj (L.tensorPow d), ⊤)) :
    tensorGradedAlgebraSection T.C ⊤ ((T.c a).app ⊤ s) *
      tensorGradedAlgebraSection T.C ⊤ ((T.c d).app ⊤ t) =
      tensorGradedAlgebraSection T.C ⊤ ((T.c (a + d)).app ⊤
        (((tensorPullback j).map (L.tensorPowAddIso a d).inv).app ⊤
          ((boundaryPullbackTensorIso j (L.tensorPow a) (L.tensorPow d)).inv.app ⊤
            (tmulSection s t)))) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
