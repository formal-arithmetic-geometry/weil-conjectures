/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.Modules.ModuleSkyscraperStalkAdjunction
import Sheaf.Topology.PresheafModuleStalkFunctor
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Enough injectives for sheaves of modules on a scheme

Source: Stacks Project, Injectives, Lemma 01DI
(blueprint: lem-weil-pbc-scheme-modules-enough-injectives).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Every sheaf of modules on a scheme embeds into an injective sheaf of modules.

Source: Stacks Project, Injectives, Lemma 01DI
(blueprint: lem-weil-pbc-scheme-modules-enough-injectives).

Proof:
1. Embed each stalk of a module sheaf `F` into an injective module `J_x`, using
   `lem-weil-pbc-ring-modules-enough-injectives` and `def-weil-pbc-module-stalk`.
2. The stalk functor is additive and exact (`lem-weil-pbc-module-stalk-exact`). Its right
   adjoint is the skyscraper functor (`lem-weil-pbc-module-skyscraper-stalk-adjunction`).
   Thus each skyscraper of `J_x` is injective by `lem-sp-right-adjoint-preserves-injectives`.
3. Their product exists sectionwise (`lem-weil-pbc-module-sheaves-limits-sectionwise`)
   and is injective (`lem-weil-pbc-product-injectives`). Its sections on `U` are the
   product of the `J_x` for `x` in `U`, with the action through the germs of scalars.
4. The stalk embeddings give a map from `F` to this product by the adjunction and the
   product universal property; on sections it sends a section to its embedded germs.
5. A section in its kernel has zero germ everywhere, since each stalk embedding is
   injective. It is zero by `lem-weil-pbc-sheaf-sections-determined-by-germs`.
   Sectionwise injectivity implies that the map is a categorical monomorphism.
6. This is an injective presentation of arbitrary `F`, giving `EnoughInjectives`
   in the sense of `def-sp-injective-resolutions`. -/
theorem enoughInjectives (X : Scheme.{u}) : EnoughInjectives X.Modules := by
  sorry

end AlgebraicGeometry.Scheme.Modules
