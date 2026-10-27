module

public import Sheaf.AlgebraicGeometry.RingedSpaceCupPresentation
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Base change and relative derived cup products on ringed spaces

Source: Stacks Project, Cohomology, Tag 0H99, lemma-base-change-cup-product,
and Tag 0B68, remark-cup-product
(blueprint: lem-sfb-ringed-space-derived-cup-base-change).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory SheafOfModules

namespace AlgebraicGeometry.RingedSpace

variable {X X' Y Y' : RingedSpace.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X'))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y'))]
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- The route through cup, exchange, and the upper pullback tensor comparison.
Source: Stacks Project, Tag 0H99, upper and right sides of the diagram
(blueprint: lem-sfb-ringed-space-derived-cup-base-change). -/
def CupSquarePresentation.cupFirst (p : CupSquarePresentation f f' g g')
    (K L : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    p.gEdge.left.obj (p.tensorY.obj (p.fEdge.right.obj K, p.fEdge.right.obj L)) ⟶
      p.f'Edge.right.obj (p.tensorX'.obj (p.g'Edge.left.obj K, p.g'Edge.left.obj L)) :=
  p.gEdge.left.map (RingedSiteCup.relative p.fEdge p.modelY p.modelX K L) ≫
    p.square.exchange.app (p.tensorX.obj (K, L)) ≫
    p.f'Edge.right.map ((p.g'Edge.tensorComparison p.modelX p.modelX').hom.app (K, L))

/-- The route through the lower pullback tensor comparison, two exchanges, and cup.
Source: Stacks Project, Tag 0H99, left and lower sides of the diagram
(blueprint: lem-sfb-ringed-space-derived-cup-base-change). -/
def CupSquarePresentation.exchangeFirstCup (p : CupSquarePresentation f f' g g')
    (K L : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    p.gEdge.left.obj (p.tensorY.obj (p.fEdge.right.obj K, p.fEdge.right.obj L)) ⟶
      p.f'Edge.right.obj (p.tensorX'.obj (p.g'Edge.left.obj K, p.g'Edge.left.obj L)) :=
  (p.gEdge.tensorComparison p.modelY p.modelY').hom.app
      (p.fEdge.right.obj K, p.fEdge.right.obj L) ≫
    p.tensorY'.map (Prod.mkHom (p.square.exchange.app K) (p.square.exchange.app L)) ≫
    RingedSiteCup.relative p.f'Edge p.modelY' p.modelX'
      (p.g'Edge.left.obj K) (p.g'Edge.left.obj L)

/-- Relative cup commutes with base change for every commutative ringed-space square.
Presentations exist and the formula holds in every such canonical presentation; thus
no presentation, tensor coherence, or base-change isomorphism is an extra hypothesis.
The second clause expresses naturality in both complexes and the third is the
coefficient-valued formula for an arbitrary morphism K tensor L to M.

Source: Stacks Project, Tag 0H99, lemma-base-change-cup-product; relative cup is
Tag 0B68, remark-cup-product
(blueprint: lem-sfb-ringed-space-derived-cup-base-change).

Proof, expanding the omitted proof of 0H99:
1. On the four open-set sites take K-flat flat-term tensor models and the tensor
pullbacks of derivedModulePullback_adjunction. Their right adjoints are the recorded
K-injective derived direct images. Commutation including structure maps gives the
ordinary square on generators; its unique derived extension gives the comparison
whose mate is square.exchange (lem-weil-pbc-ringed-exchange-tensor-coherence).
2. The relative cup factors as R(1 tensor counit) after the projection map: both
transposes are tensor comparison followed by the two counits. Use the Hom bijection
of lem-pc-ringed-spaces-derived-adjoint-general, the definition of relative cup,
and the transpose formula of lem-weil-pbc-ringed-projection-mate-exact.
3. Apply ringedExchangeTensorCoherence with Q=Rf_*L. Postcompose with the image
of 1 tensor the upper pullback of the counit at L. Naturality of exchange and of
the tensor comparison turns the first route into cupFirst.
4. The mate counit equation replaces H(counit) theta by counit' C(exchange).
Naturality of projection in its second argument moves this exchange to the input.
The cup factorization of step 2 identifies the result with exchangeFirstCup.
5. All these transformations are natural. For a coefficient morphism a, use
exchange naturality and postcompose with Rf'_*(mu_g' inverse followed by Lg'^*a).
This proves the last formula without inverting exchange, requiring flatness,
or restricting the unbounded complexes. -/
theorem derivedCup_baseChange (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (_comm : g' ≫ f = f' ≫ g) :
    Nonempty (CupSquarePresentation f f' g g') ∧
      ∀ p : CupSquarePresentation f f' g g',
        (∀ K L : DerivedCategory (SheafOfModules.{u} (moduleRings X)),
          p.cupFirst K L = p.exchangeFirstCup K L) ∧
        (∀ (K L K' L' : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
            (a : K ⟶ K') (b : L ⟶ L'),
          p.gEdge.left.map
              (p.tensorY.map (Prod.mkHom (p.fEdge.right.map a) (p.fEdge.right.map b))) ≫
            p.cupFirst K' L' = p.cupFirst K L ≫
              p.f'Edge.right.map
                (p.tensorX'.map (Prod.mkHom (p.g'Edge.left.map a) (p.g'Edge.left.map b)))) ∧
        ∀ (K L M : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
            (a : p.tensorX.obj (K, L) ⟶ M),
          p.gEdge.left.map
              (RingedSiteCup.relative p.fEdge p.modelY p.modelX K L ≫ p.fEdge.right.map a) ≫
            p.square.exchange.app M =
          p.exchangeFirstCup K L ≫ p.f'Edge.right.map
            ((p.g'Edge.tensorComparison p.modelX p.modelX').inv.app (K, L) ≫
              p.g'Edge.left.map a) := by
  sorry

end AlgebraicGeometry.RingedSpace
