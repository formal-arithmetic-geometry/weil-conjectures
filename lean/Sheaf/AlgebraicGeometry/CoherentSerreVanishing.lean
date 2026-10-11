/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.Paper.PQFCohomology
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Serre vanishing over a Noetherian affine base

Source: Stacks Project, Cohomology of Schemes, Tags 02O1 and 0B5T (4);
Morphisms, Tag 01VK (blueprint: lem-weil-pbc-coherent-serre-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module on a proper scheme over a Noetherian ring has zero positive-degree
cohomology after sufficiently large tensor powers of an ample invertible module, with
one nonnegative bound for every positive cohomological degree. Tensor powers include
`L.tensorPow 0 = 𝒪_X`. Cohomology is the right derived functor of module global sections.
Source: Stacks Project, Cohomology of Schemes, Tags 02O1 and 0B5T (4), and Morphisms,
Tag 01VK (blueprint: lem-weil-pbc-coherent-serre-vanishing).

Proof:
1. The affine base is Noetherian: def-weil-pbc-noetherian-ring, pqf-def-locnoeth,
   lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact. Properness gives finite type
   (def-weil-proper-morphism), so lem-weil-pbc-finite-type-over-noetherian makes X
   Noetherian. The standard affine charts of projective space (def-pc-proj) are
   Noetherian by lem-weil-pbc-finite-type-algebra-noetherian.
2. By lem-weil-pbc-ample-very-ample-immersion-affine-base there are d > 0 and an
   immersion i into projective space P over A, over the base, with L^{⊗ d} ≅ i^*O_P(1)
   (def-pc-projective-space-twist). Write M = i^*O_P(1).
3. P is separated over A (lem-weil-pbc-projective-space-proj-separated), so i is proper
   by lem-weil-pbc-proper-over-separated. By lem-weil-pbc-proper-immersion-closed it is
   a closed immersion (def-weil-closed-immersion).
4. For 0 ≤ r < d and t ≥ 0 put G_{r,t} = F ⊗ L^{⊗ r} ⊗ M^{⊗ t} and G_r = F ⊗ L^{⊗ r}.
   Local trivializations of the invertible factors (def-sc-invertible-module) identify
   these modules locally with F. Thus pqf-lem-coherent-ft-locnoeth and pqf-def-coherent
   give coherence. By lem-weil-pbc-closed-immersion-coherent-equivalence their
   pushforwards along i are coherent.
5. The projection formula (lem-pc-closed-immersion-coherent-cohomology) gives
   i_*G_{r,t} ≅ i_*G_r ⊗ O_P(t), inductively using lem-pc-twist-tensor and the
   trivialization O_P(0) ≅ O_P from def-pc-projective-space-twist. All tensor products
   and exponent laws are those of def-pur-sheaf-tensor-product.
6. For n = td + r the tensor exponent laws give F ⊗ L^{⊗ n} ≅ G_{r,t}.
   Functoriality of pqf-def-cohomology and the affine closed immersion comparison
   lem-weil-pbc-affine-morphism-cohomology-edge identify its degree-p cohomology
   with H^p(P, i_*G_r ⊗ O_P(t)).
7. Apply lem-pc-projective-space-serre-vanishing to each coherent i_*G_r, obtaining
   bounds t_r for all p > 0. Let T be their finite maximum and n₀ = dT. For n ≥ n₀,
   division by d gives n = td + r, 0 ≤ r < d, and t ≥ T ≥ t_r. The comparison of
   step 6 therefore gives vanishing simultaneously in every positive degree. -/
theorem exists_isZero_moduleCohomology_tensorPow_of_ample
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (L : X.Modules) [L.IsInvertible] (hL : IsAmple X L) :
    ∃ n₀ : ℕ, ∀ (p n : ℕ), 0 < p → n₀ ≤ n →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj
        (tensorObj F (L.tensorPow n))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
