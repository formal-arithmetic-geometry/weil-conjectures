/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Sheaf.RingTheory.CotangentResolutionCoherence
import Sheaf.AlgebraicTopology.TrivialKanFibration
import Sheaf.Paper.TrivialKanHomotopyEquivalence
import Sheaf.AlgebraicTopology.SimplicialAbelianSetHomotopyQuasiIso

/-!
# Finite polynomial simplicial resolutions

Source: Stacks Project, Cotangent Complex, Tags 08PX (`proposition-polynomial`)
and 08QI (`remark-resolution`)
(blueprint: lem-sfb-finite-polynomial-simplicial-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite Simplicial

namespace Algebra.CotangentResolution

/-- A finite type algebra over a Noetherian ring admits a polynomial simplicial
resolution with finitely many variables in each degree. The coefficient equation
makes each displayed ring isomorphism an isomorphism over the base ring.
`IsPolynomialResolution` includes termwise surjectivity and the quasi-isomorphism
of the alternating additive augmentation to the algebra in degree zero.

Source: Stacks Project, Tags 08PX and 08QI
(blueprint: lem-sfb-finite-polynomial-simplicial-resolution).

Proof:
1. By `def-weil-pbc-finite-type-algebra`, choose a finite polynomial algebra
   surjecting onto the target. This is the initial augmented zero truncation.
   Inductively retain finite sets of nondegenerate polynomial generators and
   the split bases indexed by order-preserving surjections of finite ordinals,
   with all matching maps in the constructed degrees surjective.
2. Apply `lem-sfb-truncated-algebra-matching-finite-type`: the base is Noetherian,
   the target and all lower terms are finite type, and the lower matching maps
   are onto. Choose finitely many algebra generators of the next matching term.
   For the first step this term is the fibre product of the zero term with itself
   over the target. Each generator gives compatible faces over a target element.
3. Apply `lem-sfb-split-polynomial-boundary-attachment` to attach these generators
   and their degeneracies, preserving the old truncation and all identities.
   The next matching map is onto because its image contains the chosen algebra
   generators. The new variable set is finite, since between two fixed finite
   ordinals there are only finitely many order-preserving surjections.
4. Stabilize degree by degree. Every functor identity holds in a common finite
   truncation, yielding the augmented simplicial algebra of
   `def-weil-pbc-simplicial-object`. Degeneracies from degree zero imply that
   every augmentation is onto. Surjective matching maps fill every compatible
   boundary, including dimension zero: this is
   `def-weil-pbc-trivial-kan-fibration`.
5. Apply `lem-weil-pbc-trivial-kan-homotopy-equivalence` and then
   `lem-trf-simplicial-abelian-set-homotopy-quasi-iso`. The alternating complex
   of the constant target has differential zero in odd positive chain degrees
   and the identity in even positive chain degrees; its augmentation to the
   target in degree zero is a quasi-isomorphism. Compose to obtain the additive
   quasi-isomorphism required by `def-trf-cotangent-resolution-data`.
   Reindex each finite variable set by `Fin r`. There is one such finite rank
   in each degree, without a uniform bound or eventual vanishing assertion. -/
theorem exists_finite_polynomial_simplicial_resolution
    (f : Arrow CommRingCat.{u}) [IsNoetherianRing f.left]
    (_hf : RingHom.FiniteType f.hom.hom) :
    ∃ Q : Augmentation f, IsPolynomialResolution Q ∧
      ∀ n : ℕ, ∃ (r : ℕ)
        (e : CommRingCat.of (MvPolynomial (Fin r) f.left) ≅ Q.algebra.obj (op ⦋n⦌)),
        ∀ a : f.left, e.hom (MvPolynomial.C a) = Q.base.app (op ⦋n⦌) a := by
  sorry

end Algebra.CotangentResolution
