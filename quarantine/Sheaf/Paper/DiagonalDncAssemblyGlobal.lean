/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.Paper.DiagonalDncChartNormalization

/-! # Global assembly of the canonical diagonal orientation

Source: smooth-purity chart normalization and its compatibility on affine overlaps.
(blueprint: lem-pur-diagonal-dnc-assembly-global).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The three specified diagonal factors assemble to the specified orientation on
an arbitrary separated finite-type smooth morphism, without an affine hypothesis.
Source: sec-smooth-purity/sk-prop-sp-orientation/
thm-pur-diagonal-dualizing-object.proof.md, Steps 1--2 and combining paragraph;
sk-prop-sp-orientation-charts.proof.md, Steps 3--4 and restriction paragraph.
(blueprint: lem-pur-diagonal-dnc-assembly-global).

Proof: cover Y by affine opens V and their inverse images by affine opens U.
The diagonal base-change comparison restricts to its comparison for U over V,
by diagonal-section pasting. The unique normalized DNC comparison restricts to
the corresponding comparison by its family-trivialization equation on every
finite-type base and by etale localization of the total space. The normal bundle
and its zero section commute with these restrictions. Vector-bundle purity and
its site comparison identify the restricted integration adjunct and Tate
restriction with the ones on the new normal bundle. Thus each factor of the
global assembly restricts to the factor in diagonal_dnc_chart_normalization.
That theorem identifies the two arrows on U. After shifting by -2d, both objects
are identified with a degree-zero Tate line; apply degree-zero derived-map
gluing and use faithfulness of the shift equivalence to conclude globally.
For d=0 the same factors have their identity normalization, and the empty scheme
is covered by the empty-cover clause. -/
theorem diagonalDncAssemblyGlobal (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [IsSeparated aY]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    P.diagonalDualizingObject d f aY = P.chartDiagonalAssembly d f aY t := by
  sorry

end WeilConjectures.PurityFiniteSetting
