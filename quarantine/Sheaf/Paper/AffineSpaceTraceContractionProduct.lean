module

public import Sheaf.Paper.AffineSpaceTraceSuccessorContraction

/-! # Binary-product evaluation of the last-line contraction

Source: current blueprint sec-smooth-purity/sk-prop-an, Integration paragraph;
Steps 2--3 of lem-pur-affine-space-trace-factorization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineSpaceTrace
open AffineLinePurity AffineSpacePurity VectorIntegrationSite OrderedAffineTranspose

/-- The last-line contraction is the binary product followed by the single line trace.
Source: current blueprint sec-smooth-purity/sk-prop-an, Integration paragraph;
lem-pur-affine-space-trace-factorization, proof Steps 2--3
(blueprint: lem-pur-affine-space-trace-contraction-product).

Proof: put p=p_(d+1), M=T_(d+1). The Tate power M is finite-Tor constructible
by repeated tensor with the locally free Tate line and even shifts. The supplied
three image hypotheses are V, U and the next image. On the literal last-coordinate
Cartesian square, compact-support exchange is invertible; the finite compact
projection formula makes the coefficient-first projection invertible, giving hq.
Apply baseChangedLineTraceEvaluation to p and M using ht. Its hW is the external
Tate source transported through the canonical Tate pullback and unit isomorphisms.
Transport its evaluation equality by externalTateIso and successorSourceIso, and
change from the pulled-back line compactification to the standard one by
originChange. Naturality of projection in the Tate coefficient identifies its
projectionTensorTrace with the lastLineContraction composite; normalizedPulledTrace
contains precisely the same lineCoordinate and compactification comparisons.
The resulting right-hand map is D followed by 1 tensor t_Y and the right unitor.
Apply affineSpace_lastFactor_product: its two product domains and invertibility
conditions follow from the same finite-Tor objects, their pullbacks and tensors.
Its coefficient presentation positiveTate is canonically tate via the coefficient
left unitor. Transport its equality through that unitor, pullTate and appendTate.
The finiteProductChosenForward then equals binaryForward: the copied final
compactification contributes exactly rightDerivedLowerShriekCongr, and the last
coefficient map is externalTateIso. Thus hk identifies D with kappa.hom, since both
are inverse to binaryForward. Substitution proves the displayed equation.
This statement has no exceptional transpose or previous-block integration map.
For d=0 it is the two-line product; empty schemes and zero coefficients require
no extra assumption because all equations are functorial identities. -/
theorem lastLineContraction_product
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] (d : ℕ)
    (hV : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y
      ((compact P Y (d + 1)).obj (tate P Y (d + 1))))
    (hU : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y
      ((compact P Y 1).obj (tate P Y 1)))
    (hNext : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y
      ((compact P Y (d + 2)).obj (tate P Y (d + 2))))
    (ht : UniversalLineBaseChange P Y aY)
    (kappa : (compact P Y (d + 2)).obj (tate P Y (d + 2)) ≅
      ((tensor (Ring P) Y).obj ((compact P Y (d + 1)).obj (tate P Y (d + 1)))).obj
        ((compact P Y 1).obj (tate P Y 1)))
    (h : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (Ring P))
      (iteratedAffineLine Y (d + 2)) (externalTate P Y (d + 1)))
    (hk : kappa.inv = binaryForward P Y aY d h) :
    ∃ hq : ProjectionInvertible (Ring P)
      (affineTraceLineCompactification (iteratedAffineLine Y (d + 1)))
      (coefficient P.coefficients.l P.extension (P.level - 1)
        (iteratedAffineLine Y (d + 1)) P.level (annihilates P)) (tate P Y (d + 1)),
    lastLineContraction P Y aY d h hq = kappa.hom ≫
      ((tensor (Ring P) Y).obj ((compact P Y (d + 1)).obj (tate P Y (d + 1)))).map
        (lineNormalizedIntegration P Y aY) ≫
      (moduleRightUnit (Ring P) Y
        ((compact P Y (d + 1)).obj (tate P Y (d + 1)))).hom := by sorry

end AlgebraicGeometry.ProEtale.AffineSpaceTrace
