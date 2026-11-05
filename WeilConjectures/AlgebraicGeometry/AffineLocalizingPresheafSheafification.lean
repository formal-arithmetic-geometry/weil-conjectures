/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Module.LocalizedModule.Away

import WeilConjectures.AlgebraicGeometry.AffineLocalizingPresheafBasisSheaf
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Sheafification on affine opens of a localizing module presheaf

Source: Stacks Project, Tags 01HV and 009Q, applied to the principal-open basis.
(blueprint: lem-pc-affine-localizing-presheaf-sheafification).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
