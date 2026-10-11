/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.Paper.DerivedHomMayerVietoris
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Finite presentation of a binary direct sum of module sheaves

Source: Stacks Project, Properties, Lemma 01PJ, proof, and Modules, Definition 01BN
(blueprint: lem-weil-pbc-module-finite-presentation-direct-sum).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSpace

/-- The binary biproduct of two finitely presented module sheaves is finitely presented.
Source: Stacks Project, Properties, Lemma 01PJ, proof; Modules, Definition 01BN
(blueprint: lem-weil-pbc-module-finite-presentation-direct-sum).

Proof (the node's agent-written expansion of the assertion in 01PJ):
1. The free module sheaf of rank `n` is the coproduct of `n` copies of the structure
   sheaf: maps out of it correspond uniquely to the images of the basis sections
   (def-weil-pbc-module-finite-type-presentation, def-weil-pbc-category-colimit).
2. At each point choose finite presentations of `G` and `H` on neighbourhoods `U₁`
   and `U₂`, and pass to their intersection `U` (def-weil-pbc-module-finite-type-presentation).
3. Restriction preserves colimits (lem-weil-pbc-ringed-space-colimit-restriction), hence
   finite free coproducts and cokernels. Restrict both presentations to `U`; transport
   the presentation maps along the canonical isomorphisms of the restricted free modules.
4. A biproduct in an additive category is a coproduct, so restriction also identifies
   `(G ⊞ H)|U` with `G|U ⊞ H|U` (def-weil-additive-category,
   def-weil-sheaf-of-modules-category, def-weil-pbc-category-colimit,
   lem-weil-pbc-ringed-space-colimit-restriction).
5. The block diagonal map of the two presentation maps has as its cokernel the
   biproduct of their cokernels: a map killing the block map factors uniquely through
   each cokernel, and then uniquely through their biproduct (def-weil-additive-category).
6. Combine the two finite free domains and the two finite free codomains using the
   coproduct universal property, obtaining ranks `m₁ + m₂` and `n₁ + n₂`.
   Transporting the block map along these isomorphisms preserves its cokernel
   (def-weil-additive-category, def-weil-pbc-module-finite-type-presentation).
7. The resulting finite presentation has cokernel `(G ⊞ H)|U`. Since the point was
   arbitrary, the biproduct is finitely presented (def-weil-sheaf-of-modules-category,
   def-weil-pbc-module-finite-type-presentation).
-/
theorem isFinitePresentation_biprod (X : RingedSpace.{u})
    (G H : SheafOfModules.{u} (moduleRings X))
    [G.IsFinitePresentation] [H.IsFinitePresentation] :
    (G ⊞ H).IsFinitePresentation := by
  sorry

end AlgebraicGeometry.RingedSpace
