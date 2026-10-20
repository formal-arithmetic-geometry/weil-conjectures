/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictLocalLocalizedHomGerm

/-! # Localized Hom classes and restriction of a complex on the base

The adopted source module supplies the constructions and the proved germ comparison
on `Scheme.strictLocalization`. Re-export it here so that neighbourhood restriction,
the canonical source germ leg, and the complex restriction all use the same scheme.

In particular this preserves the names `sourceLocalizedSectionsIso`,
`strictHenselizationSectionRestriction_naturality`, `strictLocalSectionRestrictionNat`,
`strictLocalComplexSectionRestriction`, and `sourceLocalizedSectionsIso_germ`.
It does not redeclare a second version of any of these constructions.

Source: Stacks Project, Tags 03Q8 and 03Q9, injective-complex computation.
(blueprint: lem-weil-pbc-strict-local-localized-hom-germ).
-/

@[expose] public section
