/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Algebra.DirectSum.Module

import Mathlib.LinearAlgebra.Eigenspace.Pi
import Sheaf.LinearAlgebra.CommutingEndomorphismsCommonEigenvector

/-!
# Induction from a character stabilizer

Source: the auxiliary finite-group argument in the DAG, motivated by Travaux de Gabber,
Exposé X, Proposition 1.2, printed p.138, before equation (5)
(blueprint: lem-per-normal-commuting-weight-induction).
The representation-theoretic argument is supplied by the agent; Gabber supplies context only.
The requested Serre reference is still unavailable, as recorded in the node.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Representation

open scoped Classical in
/-- Character spaces for an irreducible representation with commuting normal-subgroup image
form one finite orbit and induce the representation from each weight stabilizer.

Source: the agent-written auxiliary representation argument attached to Travaux de Gabber,
Exposé X, Proposition 1.2, printed p.138, before equation (5), context only
(blueprint: lem-per-normal-commuting-weight-induction).

The family `E` is specified by equality with intersections of Mathlib eigenspaces. The action
is on precisely the characters with nonzero space, and its values are specified pointwise.
The subgroup and its restricted representation are likewise specified by their membership
and action formulas. Thus none of these existentially bound objects is arbitrary.
Mathlib's `IndV.mk h` denotes the node's tensor `[h⁻¹] ⊗ w`: its induction uses simultaneous
left-translation coinvariants and right-inverse translation by the ambient group. Accordingly
`IndV.mk g⁻¹` denotes `[g] ⊗ w` and the last equation specifies the exact canonical map.

Proof:
1. Apply `lem-sfb-commuting-endomorphisms-common-eigenvector` to the operators indexed by A.
A nonzero common eigenvector has nonzero eigenvalues because the operators are invertible.
The equations for 1 and ab make these eigenvalues a character, so a nonzero weight exists.
2. Normality defines conjugation on characters. Compute the identity and multiplication
laws and the equation rho(a)rho(g)w = rho(g)rho(g⁻¹ag)w to obtain the asserted transport
of eigenspaces; applying g⁻¹ gives equality and preserves nonzero spaces.
3. Commutativity makes every operator preserve all generalized eigenspaces of every other.
Apply `lem-per-compatible-generalized-weight-independence`, namely
`Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`, and restrict to ordinary
character eigenspaces. Distinct characters have distinct scalar-valued functions, giving
independence, equivalently the finite-sum criterion
in `iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero`.
4. Sum the eigenspaces over the finite orbit of the character from step 1. The sum is
nonzero and G-invariant, so irreducibility makes it V. Independence rules out any additional
nonzero weight, proving finiteness, transitivity and the internal direct-sum assertion.
5. The character stabilizer is a subgroup. For a,b in A, chi(a⁻¹ba) = chi(b), because Fˣ
is commutative. Hence A lies in the stabilizer T, and step 2 restricts the action to E chi.
6. For a nonzero T-invariant subspace U of E chi, sum rho(r)U over representatives r of G/T.
This is nonzero and G-invariant, hence V. Independence from step 3 makes its intersection
with E chi equal to U, so U = E chi. The restricted representation is irreducible.
7. The map [g] ⊗ w ↦ rho(g)w respects [gt] ⊗ w = [g] ⊗ rho(t)w and is G-equivariant.
Its image contains every translated weight space, so step 4 makes it surjective.
8. Decompose x uniquely as the sum of x_r in E(r chi) over the coset representatives and
send x to the sum of [r] ⊗ rho(r⁻¹)x_r. The uniqueness from step 3 makes this linear.
Its composite with the canonical map is x; on [g] ⊗ w, write g = rt and use the defining
induction relation to check the other composite. This gives the specified equivariant iso. -/
theorem normal_commuting_weight_induction
    {F : Type u} [Field F] [IsAlgClosed F] [CharZero F]
    {G : Type v} [Group G] [Finite G]
    {V : Type w} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]
    (ρ : Representation F G V) [IsIrreducible ρ]
    (A : Subgroup G) [A.Normal]
    (hcomm : ∀ a b : A, Commute (ρ a.val) (ρ b.val)) :
    ∃ E : (A →* Fˣ) → Submodule F V,
      (∀ χ : A →* Fˣ, E χ = ⨅ a : A, Module.End.eigenspace (ρ a.val) (χ a : F)) ∧
      {χ : A →* Fˣ | E χ ≠ ⊥}.Finite ∧
      {χ : A →* Fˣ | E χ ≠ ⊥}.Nonempty ∧
      DirectSum.IsInternal (fun χ : {χ : A →* Fˣ | E χ ≠ ⊥} ↦ E χ.val) ∧
      ∃ α : MulAction G {χ : A →* Fˣ | E χ ≠ ⊥},
        (∀ (g : G) (χ : {χ : A →* Fˣ | E χ ≠ ⊥}) (a : A),
          (α.smul g χ).val a = χ.val (MulAut.conjNormal g⁻¹ a)) ∧
        (∀ χ ψ : {χ : A →* Fˣ | E χ ≠ ⊥}, ∃ g : G, α.smul g χ = ψ) ∧
        (∀ (g : G) (χ : {χ : A →* Fˣ | E χ ≠ ⊥}),
          (E χ.val).map (ρ g) = E (α.smul g χ).val) ∧
        ∀ χ : {χ : A →* Fˣ | E χ ≠ ⊥},
          ∃ T : Subgroup G,
            (∀ g : G, g ∈ T ↔ α.smul g χ = χ) ∧ A ≤ T ∧
            ∃ σ : Representation F T (E χ.val),
              (∀ (t : T) (x : E χ.val), (σ t x : V) = ρ t.val (x : V)) ∧
              IsIrreducible σ ∧
              ∃ e : Equiv (ind T.subtype σ) ρ,
                ∀ (g : G) (x : E χ.val),
                  e (IndV.mk T.subtype σ g⁻¹ x) = ρ g (x : V) := by
  sorry

end Representation
