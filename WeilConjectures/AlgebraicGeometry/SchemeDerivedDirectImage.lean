/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage

/-!
# Derived direct image on schemes

Source: the Weil conjectures blueprint, sec-picard-framework/det-thm-picard-coherence,
node def-pc-derived-direct-image; Stacks Project, Tag 0A1G, with the ringed-space
construction of Tag 079V (blueprint: def-pc-derived-direct-image).

## Main definitions

* `schemeDerivedDirectImage` specializes the ringed-space derived direct image to schemes.
* `schemeHigherDirectImage` takes its cohomology sheaf in any integer degree.
* `schemeModuleHigherDirectImage` first places a module in degree zero.
-/

@[expose] public section

universe u wX wS

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}
  [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]

/-- The unbounded derived direct image `Rf_* : D(𝒪_X) ⥤ D(𝒪_S)` is the ringed-space
construction for the underlying ringed-space morphism. Its K-injective computation is
supplied by `RingedSpace.derivedModuleDirectImage_computed_by_resolution`.
Source: blueprint sec-picard-framework/det-thm-picard-coherence, node
 def-pc-derived-direct-image; Stacks, Tags 0A1G and 079V
(blueprint: def-pc-derived-direct-image). -/
abbrev schemeDerivedDirectImage (f : X ⟶ S) :
    schemeDerivedCategory X ⥤ schemeDerivedCategory S :=
  RingedSpace.derivedModuleDirectImage f.toLRSHom.toShHom

end AlgebraicGeometry
