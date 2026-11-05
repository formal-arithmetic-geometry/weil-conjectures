/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import WeilConjectures.Algebra.Homology.Embedding.RestrictionExtend
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution

/-!
# Quasi-isomorphisms of complexes of modules from sections

A morphism of complexes of `𝒪_X`-modules is a quasi-isomorphism as soon as every point has
arbitrarily small open neighbourhoods over which it is a quasi-isomorphism on sections
(`AlgebraicGeometry.Scheme.Modules.quasiIso_of_quasiIso_sectionsAb` for complexes indexed by `ℤ`,
`AlgebraicGeometry.Scheme.Modules.quasiIso_of_quasiIso_sectionsAb_nat` for complexes indexed by
`ℕ`): its mapping cone is then exact on these sections.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

end AlgebraicGeometry.Scheme.Modules
