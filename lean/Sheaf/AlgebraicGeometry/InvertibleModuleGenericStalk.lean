/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.LinearAlgebra.Dimension.Free
import Sheaf.AlgebraicGeometry.FunctionField
import Sheaf.Topology.PresheafModuleStalkFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField

/-!
# Invertible modules and their generic stalk

Source: Stacks Project, Divisors, Tags 01X5 (2) and 02OZ (1)
(blueprint: lem-sc-invertible-module-generic-stalk).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module on an integral scheme embeds into its generic stalk; sections on
any nonempty open are precisely the generic germs lying in all its stalk images.
Source: Stacks Project, Divisors, Tags 01X5 (2) and 02OZ (1)
(blueprint: lem-sc-invertible-module-generic-stalk).

Proof:
1. Local trivializations from `def-sc-invertible-module` identify the module with the
structure sheaf on a neighborhood of each point. Every nonempty open contains the generic
point (`def-sc-generic-point`), so these neighborhoods all contain it.
2. The germ description in `def-weil-pbc-module-stalk` makes specialization well defined:
equal germs agree on a smaller neighborhood, which still contains the generic point.
The map is semilinear over the structure-sheaf specialization and commutes with germs.
3. A trivialization induces mutually inverse linear maps on stalks, commuting with these
specialization maps and with germs of sections.
4. Thus every stalk has a singleton basis. At the generic point the scalar ring is the
field from `def-sc-function-field`, giving dimension one.
5. Under the trivialization, specialization is the injective structure-sheaf map from
`lem-sc-integral-scheme-stalks-in-function-field`. A generator corresponds to a unit,
whose nonzero image is a basis over the function field; semilinearity gives the image formula.
6. A section with zero generic germ has zero germ at every point by step 5. It vanishes by
`lem-weil-pbc-sheaf-sections-determined-by-germs`, giving injectivity on sections.
7. Every section's generic germ belongs to each stalk image by compatibility of germs.
8. Conversely, trivialize on neighborhoods inside the given open. A generic element in all
stalk images corresponds there to a function in every local ring, hence to a section by
`lem-sc-function-field-sections-glue`; transport back through the trivialization.
9. These local sections have the same generic germ, so step 6 makes them agree on overlaps.
The sheaf equalizer condition (`def-weil-pbc-sites-and-cohomology`,
`def-weil-sheaf-of-modules-category`) glues them to the desired section. -/
theorem invertible_module_generic_stalk (X : Scheme.{u}) [IsIntegral X]
    (L : X.Modules) [L.IsInvertible] :
    let η := genericPoint X
    let lam := fun x : X ↦
      TopCat.Presheaf.stalkSpecializes L.val.presheaf
        ((genericPoint_spec X).specializes (Set.mem_univ x))
    let ρ := fun x : X ↦ algebraMap (X.presheaf.stalk x) X.functionField
    (∀ x : X, Nonempty (Module.Basis PUnit.{u + 1} (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk L.val.presheaf x))) ∧
    Module.rank X.functionField ↑(TopCat.Presheaf.stalk L.val.presheaf η) = 1 ∧
    (∀ x : X, Function.Injective (lam x) ∧
      ∀ e : ↑(TopCat.Presheaf.stalk L.val.presheaf x), Submodule.span (X.presheaf.stalk x) {e} = ⊤ →
        (∃ b : Module.Basis PUnit.{u + 1} X.functionField ↑(TopCat.Presheaf.stalk L.val.presheaf η),
          b PUnit.unit.{u + 1} = lam x e) ∧
        Set.range (lam x) = {τ : ↑(TopCat.Presheaf.stalk L.val.presheaf η) |
          ∃ a : X.presheaf.stalk x, τ = ρ x a • lam x e}) ∧
    (∀ (U : X.Opens) (hU : Nonempty U),
      let hη := ((genericPoint_spec X).specializes (Set.mem_univ hU.some.val)).mem_open
        U.isOpen hU.some.property
      let lamU := TopCat.Presheaf.germ L.val.presheaf U η hη
      Function.Injective lamU ∧
        Set.range lamU = {τ : ↑(TopCat.Presheaf.stalk L.val.presheaf η) |
          ∀ x : X, x ∈ U → τ ∈ Set.range (lam x)}) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
