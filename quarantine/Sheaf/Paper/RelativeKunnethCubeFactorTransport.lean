module

public import Sheaf.Paper.RelativeKunnethConstructions
import Sheaf.Paper.RelativeProductBaseChangeFactorSquares
import Sheaf.Paper.RelativeProductInputDomains

/-! # Transport of the relative-product cube to normalized coordinates

Source: current blueprint, relative-product coherence (iii)
(blueprint: lem-sf-relative-kunneth-cube-factor-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The seven canonical vertical comparisons in any normalized presentation.
The six equations remain separate, so composing them is a further argument.
Source: current blueprint sec-six-functors/sk-thm-sf-kunneth-relative,
coherence (iii), and lem-sf-relative-product-base-change-factor-squares
(blueprint: lem-sf-relative-kunneth-cube-factor-transport).

Proof: split the positive exponent as m+1. Restrict the supplied pullback and
support functors through the full finite-Tor inclusions. Their equality
normalizations identify these restrictions with the canonical restrictions in
RelativeProductBaseChange. Lift monoidal pullback and pullback composition;
use the three specified compactified squares for the exchanges. A2 gives the
inverse exchanges. Full faithfulness supplies their inverse identities and
naturality and proves every normalization field, giving the cube comparisons.
For any normalized A, full faithfulness and its tensor, composition and exchange
normalizations identify its primitive maps with these lifted maps. Form beta_i
by the seven formulas of RelativeProductBaseChange.beta. At i=0 this is exchange
for h followed by support of the external tensor comparison; at i=6 it is
monoidal pullback followed by tensor of the f and g exchanges. These are exactly
A.sourceIso and A.targetIso by the normalization fields. The two product squares
and the f,g base-change faces imply that the v-face is Cartesian, by pullback
pasting and cancellation. Apply relative_product_input_domains to obtain the
finite etale-origin witnesses (and the integral/common-stage representatives)
required by factor_squares. Apply its six equations. Transport through the full
inclusions, the tensor-model isomorphisms and the equality of compactifications
in G, and cancel inverse coordinate comparisons. This gives the six equations
below for the original factors. This proof uses no equation for their composite;
identity base changes and zero inputs require the same constructions. -/
theorem relativeKunneth_cube_factor_transport
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
    {Q Q' : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.Y.obj.hom] [IsSeparated Q.f.hom.left]
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    [IsSeparated Q'.g.hom.left] [IsSeparated Q'.g'.hom.left] [IsSeparated Q'.f'.hom.left]
    (R : RelativeProductPresentation S s Q) (R' : RelativeProductPresentation S s Q')
    (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left)
    (cg' : Compactification Q'.g.hom.left)
    (ch' : Compactification (Q'.f' ≫ Q'.g).hom.left)
    (G : RelativeKunnethCube Q Q' cg ch cg' ch') :
    Nonempty (RelativeKunnethCubeComparisons R R' G) ∧
    ∀ (A : RelativeKunnethCubeComparisons R R' G) K L,
      ∃ beta : ∀ i : Fin 7,
        (R'.coordinates.operations.pull G.b G.separated_b).obj
          (((relativeProductTerms Q cg ch i).eval
            R.coordinates.operations R.coordinates.tensor).obj (K, L)) ≅
          ((relativeProductTerms Q' cg' ch' i).eval
            R'.coordinates.operations R'.coordinates.tensor).obj
              ((R'.coordinates.operations.pull G.x G.separated_x).obj K,
               (R'.coordinates.operations.pull G.y G.separated_y).obj L),
        beta 0 = A.sourceIso K L ∧ beta 6 = A.targetIso K L ∧
          ∀ i : Fin 6,
            (R'.coordinates.operations.pull G.b G.separated_b).map
                ((R.factors cg ch i).hom.app (K, L)) ≫ (beta i.succ).hom =
              (beta i.castSucc).hom ≫
                (R'.factors cg' ch' i).hom.app
                  ((R'.coordinates.operations.pull G.x G.separated_x).obj K,
                   (R'.coordinates.operations.pull G.y G.separated_y).obj L) := by
  sorry

end WeilConjectures
