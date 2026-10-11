/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Affineness of a Noetherian finite surjective image

Source: Stacks Project, Cohomology of Schemes, Lemma 01YQ
(blueprint: lem-weil-pbc-finite-surjective-affine-target-noetherian).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A Noetherian (locally Noetherian and quasi-compact) scheme receiving a finite surjective
morphism from an affine scheme is affine. Source: Stacks Project, Lemma 01YQ.
(blueprint: lem-weil-pbc-finite-surjective-affine-target-noetherian).

Proof (the node's eight steps):
1. Finiteness makes f affine and locally of finite type, so Y is locally Noetherian.
   Coherent modules on X and Y are quasi-coherent of finite type
   [def-weil-finite-integral-morphism, lem-weil-pbc-finite-iff-integral-lft,
   pqf-lem-locnoeth-lft, pqf-lem-coherent-ft-locnoeth].
2. For coherent F on X, let P(F) mean H¹(X,F) = 0. The zero module satisfies P.
   The long exact sequence makes P stable under extensions
   [pqf-def-cohomology, lem-weil-pbc-coherent-property-devissage-integral-subschemes].
3. If P holds for a positive finite direct sum of F, inclusion and projection of its
   first summand give a retraction on H¹, proving P(F) [pqf-def-cohomology].
4. For an integral closed subscheme Z with generic point ξ, choose a coherent F on Y
   whose pushforward has support Z and whose stalk at ξ is annihilated by m_ξ.
   Its pushforward G is coherent and supplies devissage conditions (3)(a),(b)
   [lem-weil-pbc-finite-surjective-coherent-generic-support,
   lem-weil-pbc-finite-pushforward-coherent,
   lem-weil-pbc-coherent-property-devissage-integral-subschemes].
5. For a quasi-coherent ideal J with J_ξ = O_X,ξ, the submodule G' = JG is
   quasi-coherent, hence coherent, and G'_ξ = G_ξ
   [lem-weil-pbc-ideal-times-quasi-coherent-affine-sections,
   lem-weil-pbc-coherent-kernel-cokernel-locnoeth,
   lem-weil-pbc-ideal-module-product-stalk].
6. The projection formula identifies G' with f_*(f⁻¹J F), with f⁻¹J F quasi-coherent.
   Affine-morphism cohomology comparison and affine vanishing on Y give H¹(X,G') = 0,
   establishing devissage condition (3)(c)
   [lem-weil-pbc-affine-pushforward-ideal-product,
   lem-weil-pbc-affine-morphism-cohomology-edge, pqf-lem-affine-vanishing,
   lem-weil-pbc-coherent-property-devissage-integral-subschemes].
7. Devissage gives H¹(X,F) = 0 for every coherent F
   [lem-weil-pbc-coherent-property-devissage-integral-subschemes].
8. X is quasi-separated because it is locally Noetherian. Quasi-coherent ideals
   of finite type are coherent, so step 7 and Serre's criterion imply X affine
   [lem-weil-pbc-locally-noetherian-quasi-separated, pqf-lem-coherent-ft-locnoeth,
   pqf-lem-serre-criterion]. -/
theorem isAffine_of_isFinite_surjective_of_isNoetherian
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Surjective f] [IsAffine Y]
    [IsNoetherian X] : IsAffine X := by
  sorry

end AlgebraicGeometry
