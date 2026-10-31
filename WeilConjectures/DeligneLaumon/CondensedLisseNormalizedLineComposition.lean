/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedLisseDualityDefs

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedLisseDual
variable (ell : ℕ) [Fact ell.Prime] (c : PurityTransport.Coefficient ell)

/-- Normalized comparisons inherit the canonical composition equation.
Source: normalization of each open comparison in Step 2 of
`thm-a1-curve-perverse-heart`.
(blueprint: lem-per-condensed-lisse-open-line-normalized-composition).

Replace each supplied comparison by its normalized coordinate formula and reassociate the
three composites. The result is the canonical coordinate composition equation. -/
theorem normalized_line_composition (k : Type u) [Field k]
    {W V T : Space k} [Nonempty W.scheme]
    (i : W.scheme ⟶ V.scheme) (j : V.scheme ⟶ T.scheme)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hi : ∃ b : Spec (.of k) ≅ Spec (.of k), i ≫ V.map = W.map ≫ b.hom)
    (hj : ∃ b : Spec (.of k) ≅ Spec (.of k), j ≫ T.map = V.map ≫ b.hom)
    (hij : ∃ b : Spec (.of k) ≅ Spec (.of k), (i ≫ j) ≫ T.map = W.map ≫ b.hom)
    (hWV : W.dim = V.dim) (hVT : V.dim = T.dim)
    (qi : PurityTransport.LinePullCoordinates ell c i)
    (qj : PurityTransport.LinePullCoordinates ell c j)
    (rho : ∀ (V T : Space k) (j : V.scheme ⟶ T.scheme) [IsOpenImmersion j],
      (∃ b : Spec (.of k) ≅ Spec (.of k), j ≫ T.map = V.map ≫ b.hom) →
        ((pull ell c j).obj (c.derivedLine ell T.scheme T.dim.val) ≅
          c.derivedLine ell V.scheme V.dim.val))
    (qij : PurityTransport.LinePullCoordinates ell c (i ≫ j))
    (hri : HEq (rho W V i hi).hom
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (c.obj ell) i).inv.app _ ≫
        (qi.derived ell (V.dim.val)).hom))
    (hrj : HEq (rho V T j hj).hom
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (c.obj ell) j).inv.app _ ≫
        (qj.derived ell (T.dim.val)).hom))
    (hrij : HEq (rho W T (i ≫ j) hij).hom
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (c.obj ell) (i ≫ j)).inv.app _ ≫
        (qij.derived ell (T.dim.val)).hom))
    (hcanonical :
      (pullComp ell c i j).hom.app (c.derivedLine ell T.scheme T.dim.val) ≫
          (pull ell c i).map ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (c.obj ell) j).inv.app _ ≫ (qj.derived ell T.dim.val).hom) ≫
          ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (c.obj ell) i).inv.app _ ≫ (qi.derived ell T.dim.val).hom) =
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (c.obj ell) (i ≫ j)).inv.app _ ≫ (qij.derived ell T.dim.val).hom)) :
    (pullComp ell c i j).hom.app (c.derivedLine ell T.scheme T.dim.val) ≫
        (pull ell c i).map (rho V T j hj).hom ≫ (rho W V i hi).hom =
      (rho W T (i ≫ j) hij).hom := by
  cases W
  cases V
  cases T
  dsimp only at hWV hVT
  subst hWV hVT
  rw [eq_of_heq hri, eq_of_heq hrj, eq_of_heq hrij]
  exact hcanonical

end AlgebraicGeometry.ProEtale.CondensedLisseDual
