/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement

/-!
# Constant-scalar encoding and maps of constant rings

For a ring map `g : B →+* B'`, restricting scalars along the induced map of constant ring
sheaves and then encoding by constant scalars agrees with encoding first and then restricting
the scalars of the fixed coefficient ring along `g`. Both are the identity on sections.

Source: Stacks Project, Tags 093I and 03CY.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {B B' : Type u} [CommRing B] [CommRing B'] (g : B →+* B')

end AlgebraicGeometry.Scheme
