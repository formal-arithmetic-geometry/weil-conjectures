module

public import Sheaf.Paper.OrderedAffineTransposeData

/-! # Naturality of the ordered affine comparison

Source: the ordered affine transpose proof, Step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.OrderedAffineTranspose
open AffineLinePurity AffineSpacePurity VectorIntegrationSite

/-- Naturality of the ordered comparison, with arbitrary retained ordinary origins.
Source: ordered affine transpose proof Step 2, naturality before the pasted-counit
calculation (blueprint: lem-pur-ordered-affine-comparison-natural).

Proof: for one line, the compactification projection is natural in the coefficient,
as are tensoring by its fixed integration and the coefficient unitor. Inverting the
projection preserves this naturality. The specified exceptional Hom equivalence is
natural in both variables; its source-origin witnesses affect only applicability.
Thus the affine-line comparison is natural, including between different origins.
Induct on d in the ordered recursion. At zero both functors and comparisons are
identities. At a successor, the pullback compositor, tensor comparison, Tate-line
comparison and tensor associator make sourceReassociation natural. The line comparison
is natural by the preceding calculation. The inverse exceptional compositor is natural:
it is the transpose of the pasted counit, and each counit and the compact-support
compositor is natural. Combining these three squares and the induction hypothesis
proves the displayed equation. The stage applicability theorem supplies each bounded
exceptional input. No exceptional adjunction outside the retained class is used. -/
theorem orderedAffineComparison_natural
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj)
    (L : Plus (Ring P) Y) (Le : Etale.DerivedCategoryModule (Ring P) Y)
    (hLe : etaleFiniteTor (Ring P) Y Le)
    (eL : (comparison (Ring P) Y).obj Le ≅ L.obj) (v : K.obj ⟶ L.obj) (d : ℕ) :
    (orderedSource P Y d).map v ≫ affineSpacePurityComparison P Y aY L Le hLe eL d =
      affineSpacePurityComparison P Y aY K Ke hKe eK d ≫ (exceptional P Y d).map v := by
  sorry

end AlgebraicGeometry.ProEtale.OrderedAffineTranspose
