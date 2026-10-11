/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Coherent higher direct images with proper support

Source: Stacks Project, Cohomology of Schemes, Tag 08DS,
Lemma `coherent-lemma-support-proper-over-base-pushforward`
(blueprint: lem-pc-coherent-support-proper-higher-direct-image).
-/

universe u wX wS

open CategoryTheory

namespace AlgebraicGeometry

/-- A coherent module whose support is proper over a locally Noetherian base has coherent
higher direct images along a locally finite type morphism in every nonnegative degree.
Source: Stacks Project, Cohomology of Schemes, Tag 08DS
(blueprint: lem-pc-coherent-support-proper-higher-direct-image).

Proof:
1. By `lem-weil-pbc-module-support-proper-over-base` (Tag 0CYS), choose a closed immersion
   i : Z → X and a finite type quasi-coherent module G on Z with i_*G ≅ F, such that
   g = i ≫ f is proper.
2. A closed immersion is affine by `lem-weil-pbc-closed-immersion-integral-separated-uc`.
   Thus `lem-pc-affine-morphism-hi` gives R^q i_*G = 0 for q > 0. Derived direct-image
   composition (`lem-pc-derived-direct-image-composition`) identifies Rf_*F with Rg_*G,
   hence identifies their p-th cohomology sheaves.
3. The proper morphism g is locally of finite type, so Z is locally Noetherian by
   `pqf-lem-locnoeth-lft`. The finite type quasi-coherent G is coherent by
   `pqf-lem-coherent-ft-locnoeth`. Apply `lem-pc-coherent-hi` (Tag 02O5) to g and G,
   and transfer coherence through the isomorphism of step 2. -/
theorem isCoherent_schemeModuleHigherDirectImage_of_support_proper
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hSupport : Scheme.Modules.HasSupportProperOver f F) (p : ℤ) (hp : 0 ≤ p) :
    RingedSpace.IsCoherent S.toRingedSpace ((schemeModuleHigherDirectImage f p).obj F) := by
  sorry

end AlgebraicGeometry
