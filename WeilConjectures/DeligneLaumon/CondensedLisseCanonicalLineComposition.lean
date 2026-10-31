/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedLisseDualityDefs
public import WeilConjectures.DeligneLaumon.CondensedLinePullCoherence
import WeilConjectures.DeligneLaumon.CondensedLisseRootCoordinateComposition
import WeilConjectures.DeligneLaumon.CondensedLisseDerivedCoordinateTransport

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedLisseDual
variable (ell : ℕ) [Fact ell.Prime] (c : PurityTransport.Coefficient ell)

/-- Canonical composition of normalized Tate-line coordinates on a nonempty source.
Source: finite-root projection, scalar normalization, tensor powers, and derived shifts
in Step 2 of `thm-a1-curve-perverse-heart`.
(blueprint: lem-per-condensed-lisse-open-line-canonical-composition).

The finite projections determine the composite integral comparison. Scalar extension and
monoidal tensor powers transport this comparison to the shifted derived Tate line. -/
theorem canonical_line_composition (k : Type u) [Field k] (hEll : IsUnit (ell : k))
    {W V T : Space k} [Nonempty W.scheme]
    (i : W.scheme ⟶ V.scheme) (j : V.scheme ⟶ T.scheme)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (qi : PurityTransport.LinePullCoordinates ell c i)
    (qj : PurityTransport.LinePullCoordinates ell c j) :
    ∃ qij : PurityTransport.LinePullCoordinates ell c (i ≫ j),
      (pullComp ell c i j).hom.app (c.derivedLine ell T.scheme T.dim.val) ≫
          (pull ell c i).map ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (c.obj ell) j).inv.app _ ≫ (qj.derived ell T.dim.val).hom) ≫
          ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (c.obj ell) i).inv.app _ ≫ (qi.derived ell T.dim.val).hom) =
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
          (c.obj ell) (i ≫ j)).inv.app _ ≫ (qij.derived ell T.dim.val).hom) := by
  obtain ⟨qij, hroot⟩ := root_coordinate_composition ell c k hEll i j qi qj
  exact ⟨qij, derived_coordinate_transport ell c k hEll i j qi qj qij hroot⟩

end AlgebraicGeometry.ProEtale.CondensedLisseDual
