/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.KrullDimension
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.Topology.OpenModuleCohomology
import Sheaf.Topology.WLocalComponents
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Topology.RestrictInjectiveResolution
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.Topology.PuncturedSpectralNeighborhoodDimension
import Sheaf.Topology.SpectralSpaceCohomologyDimension
import Sheaf.Topology.PuncturedNeighborhoodCohomologyColimit
import Sheaf.AlgebraicGeometry.FilteredColimitElementEventuallyZero
import WeilConjectures.Topology.ModuleMayerVietoris

/-! # Top-degree module cohomology restriction on spectral ringed spaces

Source: Stacks Project, Cohomology, Tag 0A3G, part (2), and Tag 01F1, part (1)
(blueprint: lem-sfb-spectral-module-top-degree-restriction).

The canonical map is the right derived natural transformation of section restriction
in the category of all structure-sheaf modules. No finiteness condition is imposed
on the structure sheaf or the module.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- On a spectral ringed space of dimension at most `d`, degree-`d` module cohomology
restricts surjectively to every quasi-compact open. `RingedSpace` bundles a topological
space with a sheaf of commutative rings. Both cohomology groups are computed by
injective resolutions of modules, and the displayed map derives section restriction.

Source: Stacks Project, Cohomology, Tag 0A3G (2), with Tag 01F1 (1)
(blueprint: lem-sfb-spectral-module-top-degree-restriction).

Proof:
1. If the space or the open is empty, the target is zero. In degree zero, sobriety
and the dimension bound imply every point is closed. The closed-point criterion
`det-pe-wlocal-components` makes the space profinite. A quasi-compact open is then
clopen, so its sections extend by gluing with zero on the complement.
2. For positive degree, compare module cohomology with that of the underlying abelian
sheaf by `lem-sfb-ringed-sections-forget-abelian`, naturally for restriction arrows.
Use `lem-sc-ringed-space-module-sheaves-enough-injectives` to resolve the module,
`lem-weil-pbc-bounded-below-injectives-kinjective` for K-injectivity, and
`lem-sc-ringed-space-restrict-injective-resolution` on every open. This identifies
the comparison with the injective-resolution convention of
`def-sc-ringed-space-module-cohomology` and `def-sc-topological-abelian-cohomology`.
It does not assert that forgetting a module preserves injectivity.
3. Set Z = X \ W and let P consist of points specializing into Z. By
`lem-sfb-punctured-spectral-neighborhood-dimension`, S = P \ Z is spectral and has
dimension at most d - 1. Thus `lem-sfb-spectral-space-cohomology-dimension` makes
its degree-d abelian cohomology zero.
4. The comparison `lem-weil-pbc-punctured-neighborhood-cohomology-colimit` identifies
this group with the filtered colimit over quasi-compact neighborhoods N of Z.
By `lem-sc-filtered-colimit-map-zero`, any given class on W becomes zero on N ∩ W
for some such N. Restriction naturality of step 2 transfers this vanishing to modules.
5. Apply `lem-sc-mayer-vietoris-ringed-space` to X = W ∪ N. The pair consisting of
the given class on W and zero on N lies in the kernel of the difference map.
Exactness lifts it to a global degree-d class, proving surjectivity. -/
theorem surjective_openModuleCohomologyRestriction_of_spectralSpace
    (X : RingedSpace.{u}) [SpectralSpace X]
    (F : ringedSiteModules.{u} (moduleRings X))
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (W : Opens X) (hW : IsCompact (W : Set X)) :
    Function.Surjective
      ((openModuleCohomologyRestriction X d
        (homOfLE (le_top : W ≤ ⊤))).app F) := by
  sorry

end AlgebraicGeometry.RingedSpace
