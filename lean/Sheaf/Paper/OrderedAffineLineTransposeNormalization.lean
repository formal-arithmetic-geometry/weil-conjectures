module

public import Sheaf.Paper.OrderedAffineTransposeData

/-! # Normalization of the affine-line transpose

Source: the ordered affine transpose proof, Step 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.OrderedAffineTranspose
open AffineLinePurity AffineSpacePurity VectorIntegrationSite

/-- The transpose at the coefficient unit in dimension one is the prescribed trace.
Source: ordered affine transpose proof Step 4, affine-line normalization
(blueprint: lem-pur-ordered-affine-line-transpose-normalization).

Proof: unfold the first successor of the ordered recursion. Its preceding comparison
is the identity. The exceptional identity compositor merely changes the equation
q_0 ≫ id = p_1. Uniqueness of the ordinary right adjoint makes lineExceptionalIso
preserve the counit after the canonical compactification comparison. The defining
Hom-equivalence inverse applied to the affine-line comparison therefore recovers its
augmentation. This is inverse canonical projection followed by tensor of the actual
open-counit restriction of the projective trace, and then the coefficient right
unitor. At the unit coefficient, the projection unit law and the canonical inverse
image of the unit identify this composite with the trace itself. The source transport
is exactly tateSourceIso inverse followed by sourceReassociation at zero and
lineSource_obj_eq; fixedSourceTransport is exactly the same proper/open comparison
used in the counit calculation. These are the factors of lineNormalizedIntegration.
Cancel the unitors and their inverses to obtain the equation, also for empty Y. -/
theorem orderedAffineTranspose_line
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    : integration P Y aY 1 = lineNormalizedIntegration P Y aY := by
  sorry

end AlgebraicGeometry.ProEtale.OrderedAffineTranspose
