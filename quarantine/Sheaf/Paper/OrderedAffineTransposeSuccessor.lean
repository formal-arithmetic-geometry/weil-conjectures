module

public import Sheaf.Paper.OrderedAffineTransposeData

/-! # Successor step for the affine transpose coefficient formula

Source: the ordered affine transpose proof, Steps 1 and 3--6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.OrderedAffineTranspose
open AffineLinePurity AffineSpacePurity VectorIntegrationSite

/-- The coefficient formula propagates by one last-coordinate affine line.
The induction hypothesis ranges over every finite-type base, since the last-coordinate
base is itself a stage of the affine tower.
Source: ordered affine transpose proof Steps 1 and 3--6
(blueprint: lem-pur-ordered-affine-transpose-successor).

Proof: all projections and tower bases are separated finite type. The Tate coefficients
are ordered tensor powers of the shifted locally free rank-one etale Tate line; they
are bounded and of finite Tor amplitude. Exact pullback and tensor preserve the class,
and the stage applicability theorem supplies the exceptional inputs. The finite-ring
compact projection formula therefore makes the specified projection invertible.
Put f=q_d and g=p_d. Expand the successor comparison, and transpose its inverse
exceptional compositor through its defining pasted counit. Naturality of the line
comparison and of the counit gives the successive transposes tau_g Rg_!(tau_f).
The transpose of the line comparison is its defining augmentation. Insert this
formula and the induction hypothesis at g. Coefficient associativity of inverse
projection moves the K factor past the Tate factor at f. Projection naturality moves
the tensor of line integration past the projection at g. The normalized composition
projection equation, with the canonical compact-support compositor, identifies the
result with inverse projection at d+1 followed by tensor of a single map J to A_Y.
Evaluate the same calculation at the unit coefficient. The projection unit law
identifies J with the definition of integration at d+1. Substitute this equality
in the preceding formula. At d=0 the normalized identity functors and unitors give
the same calculation with no positive-dimensional compositor. At each occurrence
use only the bounded-below etale-origin adjunction and the specified compactification
comparisons; no change of coordinate order is involved. -/
theorem orderedAffineTranspose_successor
    (P : WeilConjectures.PurityFiniteSetting.{u}) (d : ℕ)
    (ih : ∀ (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
      [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
      (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
      (hKe : etaleFiniteTor (Ring P) Y Ke)
      (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj),
      ∃ h : IsIso (projection P Y K.obj d),
        transpose P Y aY K Ke hKe eK d = projectionInverse P Y K.obj d h ≫
          ((tensor (Ring P) Y).obj K.obj).map (integration P Y aY d) ≫
            (moduleRightUnit (Ring P) Y K.obj).hom)
    (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) :
    ∃ h : IsIso (projection P Y K.obj (d + 1)),
      transpose P Y aY K Ke hKe eK (d + 1) = projectionInverse P Y K.obj (d + 1) h ≫
        ((tensor (Ring P) Y).obj K.obj).map (integration P Y aY (d + 1)) ≫
          (moduleRightUnit (Ring P) Y K.obj).hom := by
  sorry

end AlgebraicGeometry.ProEtale.OrderedAffineTranspose
