/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictLocalUnderivedSectionsMate

/-! # The underived mate on pointed neighbourhood sections

The adopted source supplies `strictLocalUnderivedMateSections` and its proved
comparison `strictLocalUnderivedMateSections_eq`. Re-export that implementation
so that the neighbourhood restriction, the base-change square, and the cone legs
all use `Scheme.strictLocalization` and `Scheme.strictLocalizationToBase`.

The construction is restriction on the base, followed by global sections of the
underived exchange map and the direct-image/global-sections comparison. Its
comparison theorem identifies this map with restriction along the cone leg.
Both declarations retain their existing qualified names and mathematical content.

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-underived-sections-mate).
-/

@[expose] public section
