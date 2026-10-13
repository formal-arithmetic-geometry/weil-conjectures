/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Finite coherent adic chains

Source: Stacks Project, Tag 01YF, irreducible-support ideal-power paragraph,
using Tags 01Y9 and 01J3.
(blueprint: lem-pc-s3-coherent-support-adic-chain)
-/

@[expose] public section

universe u

open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A finite coherent adic chain with generic-residue-field successive quotients.

Source: Stacks Project, Tag 01YF, irreducible-support ideal-power paragraph,
using Tags 01Y9 and 01J3 (https://stacks.math.columbia.edu/tag/01YF).
(blueprint: lem-pc-s3-coherent-support-adic-chain)

Proof: construct the vanishing ideal J of the reduced induced closed subscheme T.
Its zero locus is T. The support-power lemma gives n with J^n F = 0. For k > 0
put P(k) = J^k F, using the image of ideal multiplication, and put P(0) = F
literally. The inclusions J^(k+1) F into J^k F are monomorphisms; at k = 0
compose with the canonical isomorphism J^0 F = F. Take G to be their cokernel
and g the cokernel projection. Quasi-coherence of ideal powers, products and
cokernels, together with coherent submodule and cokernel closure on a Noetherian
scheme, gives all the stated coherence assertions. Stalk exactness shows that
G is supported in T. The stalk J at the generic point is the ambient maximal
ideal: a function with nonunit germ there vanishes on T in its domain, because
its basic open cannot contain any specialization of the generic point. The
stalk of J^k F is J_xi^k F_xi; multiplying a lifted quotient element by J_xi
places it in J_xi^(k+1) F_xi and hence kills its cokernel class. The cokernel
sequence is short exact since the inclusion is monic. Extend P arbitrarily by
zero after n. If n = 0, F is zero and there are no successive quotient obligations.
This statement constructs only the chain; it asserts no integral filtration. -/
theorem coherent_support_adic_chain
    (X : Scheme.{u}) [IsNoetherian X]
    (T : TopologicalSpace.Closeds X) (ξ : X)
    (hξ : IsGenericPoint ξ (T : Set X))
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = (T : Set X)) :
    ∃ (n : ℕ) (P : ℕ → X.Modules), P 0 = F ∧ IsZero (P n) ∧
      (∀ k, k ≤ n → RingedSpace.IsCoherent X.toRingedSpace (P k)) ∧
      ∀ k, k < n → ∃ (G : X.Modules) (f : P (k + 1) ⟶ P k) (g : P k ⟶ G)
        (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact ∧
        RingedSpace.IsCoherent X.toRingedSpace G ∧
        {x : X | ¬ Subsingleton (G.presheaf.stalk x)} ⊆ (T : Set X) ∧
        (∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ),
          ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G, a • m = 0) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
