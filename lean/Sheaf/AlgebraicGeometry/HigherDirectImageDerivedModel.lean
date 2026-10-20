/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageDerivedModel

/-! # A global derived model for relatively flat higher direct images

The adopted source module proves
`AlgebraicGeometry.Scheme.Modules.exists_derived_model_higherDirectImage` with the
same properness, finite-presentation, relative-flatness and injective-resolution hypotheses.
This compatibility module re-exports that proof instead of redeclaring its name or loading
an obsolete copy of the derived-pullback construction.

Source: Stacks Project, Tag 0B91(2), and the injective-resolution definition of
higher direct images (blueprint: lem-pc-higher-direct-image-derived-model).
-/

@[expose] public section
