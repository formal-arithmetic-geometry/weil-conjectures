module

public import Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- Compatibility of the canonical section-degree comparison with multiplication.
Source: Stacks Project, Tag 01CD, tensor pullback, and Tag 09MS, tensor powers.
(blueprint: lem-sc-square-zero-tensor-section-product-comparison).
Proof: Replace D by canonicalTensorBoundaryComparisons using hD. Its section
comparison is boundaryPullbackPowIso followed by tensorPowMulIso. Expand these
recursive isomorphisms, and use naturality of boundaryPullbackComparison and the
monoidal pullback tensorator. The tensor-power addition map groups the first n
factors and the remaining n(e+1) factors; the tensor-power multiplication map groups
the same factors into blocks of n. Associator coherence identifies these groupings.
The degree-one power tensorPowSection f 1 is f followed by the inverse right unitor;
its unitor cancels the degree-one tensorPowMulIso. Evaluate the resulting morphism
equality at 1, using tensorHom_app_tmulSection and the inverse left unitor formula.
The arithmetic equality hdeg only transports the target degree. For n=0 all factors
are units and the same triangle and unitor identities apply; for e=0 the argument
is the two-block case. No graded presentation or cohomology property is used. -/
theorem tensorSectionProduct_comparison {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D)
    (e : ℕ) (f : 𝟙_ Z.Modules ⟶ ((tensorPullback j).obj L).tensorPow n)
    (x : 𝟙_ Z.Modules ⟶ (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1))
    (hdeg : n * (0 + 1) + n * (e + 1) = n * ((e + 1) + 1)) :
    ((tensorPullback j).map (eqToHom (congrArg L.tensorPow hdeg))).app ⊤
      (((tensorPullback j).map
        (L.tensorPowAddIso (n * (0 + 1)) (n * (e + 1))).inv).app ⊤
        ((boundaryPullbackTensorIso j (L.tensorPow (n * (0 + 1)))
          (L.tensorPow (n * (e + 1)))).inv.app ⊤
          (tmulSection
            ((tensorPowSection f 1 ≫ (D.a 0).inv).app ⊤ (1 : Γ(Z, ⊤)))
            ((x ≫ (D.a e).inv).app ⊤ (1 : Γ(Z, ⊤)))))) =
      ((((λ_ (𝟙_ Z.Modules)).inv ≫ (f ⊗ₘ x)) ≫ (D.a (e + 1)).inv).app ⊤
        (1 : Γ(Z, ⊤))) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
