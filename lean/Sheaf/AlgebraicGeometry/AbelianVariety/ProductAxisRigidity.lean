module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.DensePoints

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity
import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Rigidity from the two axes of a smooth product

Source: Milne, Abelian Varieties, Chapter I, Theorem 3.4, printed pp. 18–19,
specialized to an algebraically closed field and the identity value
(blueprint: lem-sfb-abelian-product-axis-rigidity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonObj

namespace AlgebraicGeometry

/-- A morphism from a product of smooth separated geometrically integral varieties to an
abelian variety that equals the identity section on both axes is the constant identity morphism.
The factors may be nonproper.

Source: Milne, Abelian Varieties, Chapter I, Theorem 3.4 and Lemmas 3.5–3.6,
printed pp. 18–19 (blueprint: lem-sfb-abelian-product-axis-rigidity).

Proof:
1. By smooth base change and composition (`lem-pc-proper-base-change`,
   `lem-trf-smooth-composition`) and finite-type base change and composition
   (`lem-sfb-finite-type-composition-base-change`), the product is smooth and finite type.
   It is reduced by `lem-trf-smooth-geometrically-normal`. The target is proper, hence
   separated and finite type (`def-sc-abelian-variety`, `def-weil-proper-morphism`).
2. Products of separated schemes are separated: after reordering factors their diagonal
   is the product of the diagonals. Affine-locally its ideal is the sum of the pulled-back
   diagonal ideals, giving a surjection onto the quotient (`def-weil-closed-immersion`).
3. Pull back along a smooth pointed curve mapping to V through v₀. Compactify that curve
   (`lem-sc-compactification`). Its completion is geometrically connected by
   `lem-sbc-connected-rational-point-geometrically-connected`; its product with W is connected
   by `lem-weil-pbc-geometrically-connected-product-components`, and smooth, regular and
   integral by `lem-trf-smooth-geometrically-normal` and `lem-sc-regular-connected-integral`.
   The original curve product is nonempty and dense. Extend its map to the completed product
   by `lem-sfb-weil-extension-to-abelian-variety`.
4. The first axis of the extension is zero by `lem-sfb-relative-separated-dominant-ext`.
   Apply `lem-sc-rigidity` to the proper curve factor. The extension factors through W;
   the second axis makes this factor zero. Thus the map vanishes on every pointed curve.
5. The pointed curves have dense union in V (`lem-sfb-smooth-pointed-curves-dense`). Assemble
   them using `lem-weil-pbc-scheme-coproduct-family`. For each rational point of W, equality
   after this dense map implies equality on V by `lem-sfb-relative-separated-dominant-ext`.
6. Rational points of the smooth product are dense (`lem-pc-rational-points-dense`). Form
   their evaluation coproduct (`lem-weil-pbc-scheme-coproduct-family`). The maps agree after
   evaluation by step 5, hence agree as scheme morphisms by
   `lem-sfb-relative-separated-dominant-ext`, since the product is reduced and A separated.
-/
theorem IsAbelianVariety.eq_identity_of_product_axes
    (k : Type u) [Field k] [IsAlgClosed k]
    (V W : Scheme.{u}) (fV : V ⟶ Spec (.of k)) (fW : W ⟶ Spec (.of k))
    [Smooth fV] [Smooth fW] [IsSeparated fV] [IsSeparated fW]
    [GeometricallyIntegral fV] [GeometricallyIntegral fW]
    [LocallyOfFiniteType fV] [QuasiCompact fV]
    [LocallyOfFiniteType fW] [QuasiCompact fW]
    (v₀ : Spec (.of k) ⟶ V) (w₀ : Spec (.of k) ⟶ W)
    (hv₀ : v₀ ≫ fV = 𝟙 _) (hw₀ : w₀ ≫ fW = 𝟙 _)
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (h : pullback fV fW ⟶ A.left)
    (hh : h ≫ A.hom = pullback.fst fV fW ≫ fV)
    (hV : pullback.lift (𝟙 V) (fV ≫ w₀)
      (by simp only [Category.id_comp, Category.assoc, hw₀, Category.comp_id]) ≫ h =
        fV ≫ η[A].left)
    (hW : pullback.lift (fW ≫ v₀) (𝟙 W)
      (by simp only [Category.id_comp, Category.assoc, hv₀, Category.comp_id]) ≫ h =
        fW ≫ η[A].left) :
    h = pullback.fst fV fW ≫ fV ≫ η[A].left := by
  sorry

end AlgebraicGeometry
