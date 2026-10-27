/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.AlgebraicGeometry.CoherentSupportCycleData
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.IntegralIdealGenericStalk
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Generic-length cycle exact sequence

Source: Stacks Project, Chow Homology, Tags 02S8, 02S9, 02QW and 02QX;
Homology, Tag 02MX, part (1)
(blueprint: lem-sfb-coherent-support-cycle-exact-sequence).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Generic lengths define the surjective cycle homomorphism, with kernel the image
of the canonical inclusion from the smaller-support category.

Source: Stacks, Chow Homology, 02S8, 02S9, 02QW, 02QX; Homology, 02MX (1)
(blueprint: lem-sfb-coherent-support-cycle-exact-sequence).

Proof:
1. Chains of irreducible closed subsets show that a proper closed subset of an
   irreducible k-dimensional closed set has dimension at most k-1. Stalk exactness
   gives support(B) = support(A) union support(C), hence support bounds are Serre
   conditions (def-kun-topological-krull-dimension, lem-weil-pbc-module-stalk-exact).
2. Closed-immersion coherent equivalence, coherence under kernels and cokernels,
   and the finite-type coherence criterion show that all sheaves in the argument
   are coherent and have closed support (lem-weil-pbc-closed-immersion-coherent-equivalence,
   lem-weil-pbc-coherent-modules-kernel-cokernel-sum,
   lem-weil-pbc-finite-type-module-support-closed, pqf-lem-coherent-ft-locnoeth).
3. Filter M by pushed-forward nonzero coherent ideals on integral closed subschemes
   (lem-weil-pbc-coherent-filtration-integral-subschemes). Their supports are exactly
   those subschemes, by closed-pushforward stalks and the integral generic-ideal lemma.
4. At a dimension-k generic point only factors on that same closed subscheme
   survive. Reduced induced closed subscheme uniqueness identifies the embeddings.
   Each surviving stalk is the residue field and has length one. Additivity of
   length therefore computes the generic length by counting finitely many factors
   (lem-weil-pbc-closed-pushforward-stalks, lem-weil-pbc-integral-scheme-ideal-generic-stalk,
   lem-weil-pbc-reduced-induced-closed-subscheme, lem-weil-pbc-length-additive-short-exact).
5. Stalk exactness and length additivity make the cycle formula respect all
   presentation relations. Inclusion also respects them. Lower-support classes
   have zero cycle. The pushforward of O_V has cycle [V], proving surjectivity.
6. For a dimension-k factor i_*I, the quotient of i_*O_V by i_*I is coherent with
   closed support missing the generic point, hence has dimension at most k-1.
   Thus its class differs from [i_*O_V] by an inclusion image. Lower-dimensional
   factors already lie in that image; for k=0 the quotient has empty support.
7. Telescope the finite filtration. Sending [V] to [i_*O_V] gives a section s
   modulo lower support, so x-s(c(x)) is in the inclusion image for every x.
   This proves kernel = image and exactness, also for empty X and no k-cycles. -/
theorem coherent_support_cycle_exact_sequence
    (F : Type u) [Field F] (X : Scheme.{u}) [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] [QuasiCompact f]
    (k : ℕ) :
    (∀ M : SupportCoherentObject X (k : ℤ),
      (∀ V : IntegralCycleIndex X k, cycleStalkLength M.val.val V ≠ ⊤) ∧
      {V : IntegralCycleIndex X k |
        ¬ Subsingleton (M.val.val.presheaf.stalk (cycleGenericPoint V))}.Finite) ∧
    ∃ (ι : SupportK0 X ((k : ℤ) - 1) →+ SupportK0 X (k : ℤ))
      (c : SupportK0 X (k : ℤ) →+ IntegralCycles X k),
      IsSupportK0Inclusion X k ι ∧ IsGenericLengthCycleMap X k c ∧
        Function.Surjective c ∧ c.ker = ι.range := by
  sorry

end AlgebraicGeometry.Scheme.Modules
