module

public import Sheaf.Paper.StrictScalarFiniteEvaluationTransport

/-! # Evaluation of ramified reduction balancing through geometric image

Source: Stacks 03EK, 06YY, 0D6E, 0E8I and 0940.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Ramified reduction transport has the finite tensor normalization. This is an
equality between isomorphisms; it contains neither the proper/open scalar mate
nor finiteTensorMap. Source: Stacks 03EK, 06YY, 0940 (section-derived-limits),
0D6E, and sites-modules.tex 0E8I (lemma-j-shriek-and-tensor).
(blueprint: lem-pur-ramified-image-balancing-evaluation).
Proof: evaluate the universal whole-cochain counit equation characterizing
reductionBalancing on a K-flat diagram representative. Evaluation of its ordinary
balancing sends b tensor (1 tensor x) to the quotient of b tensor (1 tensor x)
at exponent e(n+1). The finiteOrdinaryBalancing pure-tensor equation gives the
same coefficient and section. The reductionEvaluation comparisons and the
completed coefficient tensorSquare identify the remaining scalar-extension
associators; their cochain equations are the successive derived-quotient
normalization. Universal derived counits therefore give equality of the two
local reduction isomorphisms, before applying geometric image. Apply the
constant-coefficient proper/open image to this equation. Its evaluation
comparisons are natural. The ordinary selection squares for direct image and
open extension are identity squares, and their derived comparisons are fixed
by the same derived units. Consequently constantImageEvaluation carries
reindexImage to evaluation at e(n+1)-1. Finally the identity-on-sections
restriction/proper square and the normalized open unit identify supportModel
followed by constantImageEvaluation with the native positiveSupportEvaluation
followed by positiveImageRestriction. Cancel the supportModel and reindexImage
inverse pairs. The factors left on the ramified side are targetEvaluation;
the other side is scalarImageEvaluation. Localization gives the equality on
all derived inputs. Positivity e(n+1)≥1 justifies the retained index even when
e=1 and n=0; the zero and empty-open cases use the same equations. -/
theorem ramifiedImageBalancing_finiteEvaluation
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y n).map
        ((ramifiedImageBalancing l E F i c S S' e he hepos).hom.app M) ≫
        (targetEvaluation l E F i c S' e he hepos n).hom.app M =
      (scalarImageEvaluation l E F i c S e he hepos n).hom.app M := by sorry

end WeilConjectures.PurStrictScalar
