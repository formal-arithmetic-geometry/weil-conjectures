/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Topology.Homeomorph.Defs
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Finite sums of valuation-ring lattices

Source: Stacks Project, Tag 0AUW(3), and the blueprint main-20261015,
`sk-lem-stratified-lattice-trace.proof.md`, Local computation, second paragraph
(blueprint: lem-sfb-finite-sum-lattice).

All topologies in the statement are explicit: the coefficient field carries the metric
topology of its recorded absolute value, its powers carry product topologies, and the
integer ring and lattice submodules carry induced topologies.
-/

@[expose] public section

universe u v

namespace Padic

/-- A finite nonempty sum of full integral lattices has a full integral basis. Every
full integral basis of the sum or any summand gives a homeomorphism from the power of
the valuation ring to that submodule with its induced topology.

Source: Stacks Project, Tag 0AUW(3), and blueprint main-20261015,
`sk-lem-stratified-lattice-trace.proof.md`, Local computation, second paragraph
(blueprint: lem-sfb-finite-sum-lattice).

Proof: By `lem-weil-l-adic-extension-integers-dvr`, the coefficient ring is a DVR with
fraction field E. The finite union of the summand bases generates the sum, which is
torsion-free as a submodule of E^r. Nonemptiness supplies one summand, whose field basis
shows that the sum spans E^r. Apply `lem-sc-dvr-fg-torsionfree-free` to obtain a finite
integral basis. It spans over E, and clearing denominators in a field-linear relation
proves its field-linear independence. Equality of basis cardinalities from
`def-weil-vector-space-dimension` gives exactly r basis vectors.

For any full integral basis of the sum or a summand, its field basis defines an
E-linear automorphism of E^r. The recorded absolute value makes E complete and
nontrivially normed. By `lem-weil-pbc-finite-dimensional-linear-homeomorphism`, this
automorphism and its inverse are continuous. Restrict them to A^r and the lattice;
the basis property identifies the image with the lattice. The product of the subspace
topologies on A is the subspace topology on A^r in E^r, so both restrictions are continuous.
For r = 0, all modules and coordinate spaces are one-point spaces and the bases are empty. -/
theorem finite_sum_lattice
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (r : ℕ) (J : Type v) [Finite J] [Nonempty J]
    (Λ : J → Submodule (coefficientExtensionIntegers l E) (Fin r → E))
    (hΛ : ∀ j : J,
      ∃ b : Module.Basis (Fin r) (coefficientExtensionIntegers l E) (Λ j),
        ∃ c : Module.Basis (Fin r) E (Fin r → E),
          ∀ i : Fin r, (b i : Fin r → E) = c i) :
    (∃ b : Module.Basis (Fin r) (coefficientExtensionIntegers l E) ↥(⨆ j : J, Λ j),
      ∃ c : Module.Basis (Fin r) E (Fin r → E),
        ∀ i : Fin r, (b i : Fin r → E) = c i) ∧
    ∀ N : Submodule (coefficientExtensionIntegers l E) (Fin r → E),
      (N = (⨆ j : J, Λ j) ∨ ∃ j : J, N = Λ j) →
      ∀ b : Module.Basis (Fin r) (coefficientExtensionIntegers l E) N,
        (∃ c : Module.Basis (Fin r) E (Fin r → E),
          ∀ i : Fin r, (b i : Fin r → E) = c i) →
        @IsHomeomorph (Fin r → coefficientExtensionIntegers l E) N
          (@Pi.topologicalSpace (Fin r) (fun _ ↦ coefficientExtensionIntegers l E)
            (fun _ ↦ TopologicalSpace.induced
              (fun a : coefficientExtensionIntegers l E ↦ (a : E))
              (@UniformSpace.toTopologicalSpace E
                (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace)))
          (TopologicalSpace.induced (fun x : N ↦ (x : Fin r → E))
            (@Pi.topologicalSpace (Fin r) (fun _ ↦ E)
              (fun _ ↦ @UniformSpace.toTopologicalSpace E
                (coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace)))
          b.equivFun.symm := by
  sorry

end Padic
