/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated

import WeilConjectures.AlgebraicGeometry.SupportedPerfectDetectorAffine
import WeilConjectures.AlgebraicGeometry.SupportedOpenExtension
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh
import Mathlib.CategoryTheory.Localization.LocallySmall
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.AlgebraicGeometry.SupportedDerivedRestrictionZero
import WeilConjectures.AlgebraicGeometry.DerivedRestrictionIsIsoOpenCover

/-! # A supported Koszul relative detector

Source: Stacks Project, Tag 0A9A, induction step.
(blueprint: lem-pc-supported-koszul-relative-detector).
-/

@[expose] public section

set_option autoImplicit false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

end AlgebraicGeometry
