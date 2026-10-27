module

public import Sheaf.Paper.RelativeKunnethConstructions
import Sheaf.Paper.RelativeProductCoefficientFactorSquares
import Sheaf.Paper.PointFibreDerivedTensor
import Sheaf.Paper.DerivedPullbackTensorIso

/-! # Closed restrictions and the compact-support point fibre

Source: current blueprint, relative-product final compact-support display
(blueprint: lem-sf-relative-kunneth-closed-fibre).
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

/-- The absolute compact-support specialization uses ordinary closed restrictions.
It only concerns the point fibre, without coefficient or geometric cube coherence.
Source: current blueprint sec-six-functors/sk-thm-sf-kunneth-relative,
proof step (5) and the final compact-support display
(blueprint: lem-sf-relative-kunneth-closed-fibre).

Proof: the structure maps of Z, W and their product are separated finite type,
as recorded in J. Closed immersions are proper and hence separated. The datum's
pullback-domain preservation therefore puts i*K, j*L and r*(K box L) in the
finite-Tor domains. Choose the normalized presentation of Q' supplied by
relative_product_presentation_exists. Its six isomorphisms, evaluated at i*K
and j*L and composed in order, give support of their exterior product isomorphic
to the tensor of their two support images. Canonical monoidal pullback and
pullback composition identify this exterior product with r*(K box L), using
both projection equations in J. Apply the datum's structural compactification
comparisons to the three specified cz,cw,ct. Apply the geometric-point fibre to
the inverse six-factor isomorphism. The tensorIso of pointFibreDerivedTensor
identifies its source with the tensor of the two fibres; full inclusion and the
tensorClosed/model comparisons identify the datum's tensor with that tensor.
At finite coefficients the fibre is exact point sections; integrally it is the
completed fibre; rationally it is its localization; for common coefficients use
one common finite coefficient field and pointFdQbarRealization. The definitions
of finiteCompactSections, integralCompactSections, rationalCompactSections and
qbarCompactSections identify these fibres with precisely the displayed objects
in relativeKunnethClosedFormula. All restrictions here are ordinary pullbacks;
no exceptional pullback or cohomology with supports is used. The same construction
applies to empty schemes and zero complexes. -/
theorem relativeKunneth_closed_fibre
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
    {Q Q' : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    (R : RelativeProductPresentation S s Q) (J : RelativeKunnethClosedSquare Q Q') :
    relativeKunnethClosedFormula R J := by
  sorry

end WeilConjectures
