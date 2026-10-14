/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

/-!
# Residue fields under a closed immersion

The former closed-immersion wrapper was a duplicate of
`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap` in
`WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism`.
Use that theorem directly: `IsClosedImmersion` extends `SurjectiveOnStalks`.
(blueprint: lem-weil-pbc-closed-immersion-residue-field-iso)
-/

@[expose] public section
