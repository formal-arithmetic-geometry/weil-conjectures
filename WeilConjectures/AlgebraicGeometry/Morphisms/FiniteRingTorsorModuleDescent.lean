/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteRingTorsorAssociatedModule
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RepresentationTheory.Rep.Basic
import WeilConjectures.ConstructibleSheaf.TorsorSectionRepresentation
import WeilConjectures.ConstructibleSheaf.ConstantModuleLocallyConstant
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import WeilConjectures.Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Associated module sheaves for a finite torsor with finite ring coefficients

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 04TR and 04TS
(blueprint: lem-weil-pbc-finite-ring-torsor-module-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
open Etale
namespace Scheme.GaloisCover

end Scheme.GaloisCover

namespace Scheme.GaloisCover

end Scheme.GaloisCover
end AlgebraicGeometry
