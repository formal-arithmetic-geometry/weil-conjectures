/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Compatible tame roots and the product of adic integers

Source: Stacks Project, fields.tex Tag 09HW, algebra.tex Tags 00DT and 00M9;
blueprint main-20261015, proof of `lem-exc-dvr-galois`, second paragraph
(blueprint: lem-exc-tame-roots-product).

The subgroup is constructed using Mathlib's product, inverse-image and equalizer subgroups.
Its topology is the initial topology of its coordinates in discrete unit groups. This is
the subspace topology of the product of the discrete finite root groups. The coordinate
formula uses the canonical residues of Mathlib's valuation-ring `PadicInt`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace TameRoots

/-- The positive orders prime to `p`, ordered by divisibility in the compatibility equations.
Source: Stacks Project, Tag 09HW; blueprint proof of `lem-exc-dvr-galois`, tame quotient
(blueprint: lem-exc-tame-roots-product). -/
abbrev Order (p : ℕ) := {m : ℕ // 0 < m ∧ m.Coprime p}

/-- The prime-to-`p` root limit, as the subgroup of unit-valued families satisfying the root
equations and all power-transition equations. The defining subgroups are Mathlib's actual
`rootsOfUnity`, not a replacement notion of a root group.
Source: Stacks Project, Tag 09HW, and blueprint proof of `lem-exc-dvr-galois`, tame quotient
(blueprint: lem-exc-tame-roots-product). -/
def limitSubgroup (k : Type u) [Field k] (p : ℕ) : Subgroup (Order p → kˣ) :=
  Subgroup.pi Set.univ (fun m : Order p ↦ rootsOfUnity m.1 k) ⊓
    ⨅ (m : Order p) (n : Order p) (_ : m.1 ∣ n.1),
      ((powMonoidHom (n.1 / m.1)).comp (Pi.evalMonoidHom (fun _ : Order p ↦ kˣ) n)).eqLocus
        (Pi.evalMonoidHom (fun _ : Order p ↦ kˣ) m)

/-- The inverse-limit topology: the coarsest topology making each coordinate continuous
into the discrete unit group. Restricting each coordinate to `rootsOfUnity` gives precisely
the usual subspace topology in the product of discrete root groups.
Source: Stacks Project, Tag 00M9, and blueprint proof of `lem-exc-dvr-galois`, tame quotient
(blueprint: lem-exc-tame-roots-product). -/
@[instance_reducible]
def limitTopology (k : Type u) [Field k] (p : ℕ) : TopologicalSpace (limitSubgroup k p) :=
  ⨅ m : Order p, TopologicalSpace.induced (fun x : limitSubgroup k p ↦ x.1 m) ⊥

/-- A primitive root at every positive prime-to-`p` order, normalized at order one and
compatible with every divisibility power map.
Source: Stacks Project, Tag 09HW, and blueprint proof of `lem-exc-dvr-galois`, tame quotient
(blueprint: lem-exc-tame-roots-product). -/
def IsCompatiblePrimitiveFamily {k : Type u} [Field k] (p : ℕ) (ζ : Order p → kˣ) : Prop :=
  (∀ m : Order p, IsPrimitiveRoot (ζ m) m.1) ∧
    (∀ m : Order p, m.1 = 1 → ζ m = 1) ∧
    ∀ m n : Order p, m.1 ∣ n.1 → ζ n ^ (n.1 / m.1) = ζ m

/-- The product of the additive valuation rings at all primes different from `p`.
`Multiplicative` only changes notation for the group law and retains the product topology.
Source: blueprint proof of `lem-exc-dvr-galois`, displayed tame quotient; Stacks Tag 00M9
(blueprint: lem-exc-tame-roots-product). -/
abbrev AdicProduct (p : ℕ) :=
  Multiplicative (∀ r : {r : Nat.Primes // (r : ℕ) ≠ p},
    @PadicInt r.1 (Fact.mk r.1.2))

/-- Compatible primitive tame roots exist, and every such family induces the topological
group identification with the product of additive adic integers. Its normalization says
that the `r^a` coordinate is the chosen root raised to the canonical residue modulo `r^a`.
Prime-power coordinates determine all coordinates by Chinese remainders, so this specifies
the identification induced by `[b] ↦ ζ_m^b` at every level.

Source: Stacks Project, fields.tex Tag 09HW, algebra.tex Tags 00DT and 00M9; blueprint
main-20261015 proof of `lem-exc-dvr-galois`, second paragraph
(blueprint: lem-exc-tame-roots-product).

Proof:
1. Given orders n dividing N, lift a primitive n-th root to a primitive N-th root.
   Choose a primitive N-th root by `lem-sc-primitive-root`. Express the prescribed root
   as the (N/n)-th power of a power with exponent b coprime to n. Use
   `lem-pc-crt-ideal-quotient-product` over the integers to choose an exponent congruent
   to b modulo n and to 1 modulo every prime dividing N but not n. It is coprime to N.
   The resulting power is primitive and lifts the prescribed root; order one is harmless.
2. Put N_0 = 1 and N_j equal to the product of the integers i between 1 and j prime to p.
   These orders form a divisibility chain cofinal among tame orders. Starting at 1,
   recursively apply step 1 to choose compatible primitive roots at these orders.
3. For m dividing N_j define ζ_m as the (N_j/m)-th power of that root. Comparing with
   a common later index proves independence, primitivity, normalization and compatibility.
4. For any compatible primitive family, `[b] ↦ ζ_m^b` is an isomorphism from ZMod m to
   the m-th roots, by exact order m and their cardinality (`lem-sc-primitive-root`).
   It intertwines reductions with the power transitions. Applying these maps coordinatewise
   gives inverse continuous maps between the residue limit and the root limit: cylinders
   in the discrete factors pull back to cylinders in either direction.
5. Apply `lem-pc-crt-ideal-quotient-product` to the ideals r^v_r(m) in the integers.
   Their intersection is mZ and distinct prime-power ideals are coprime. The resulting
   finite residue decompositions commute with all reductions; m = 1 is the empty product.
6. Restrict a compatible residue family to all prime-power coordinates. Reconstruct its
   m-th residue from the finitely many r^v_r(m) residues by step 5. CRT uniqueness proves
   compatibility and that the maps are inverse. Restriction is continuous coordinatewise;
   reconstruction is continuous because each output uses only finitely many discrete inputs.
7. For each prime r, append the unique coordinate modulo r^0 = 1 to its residue limit.
   Apply `lem-exc-padic-residue-universal-property`: `PadicInt.lift` gives its map to
   the valuation ring, and `PadicInt.toZModPow` gives the inverse. The lift specifications
   and separation by all residues show that these ring maps are mutual inverses.
8. The kernel of the a-th residue is r^a Z_r, exactly the norm ball of radius r^(-a).
   Open smaller norm balls lie in residue fibres, so residue maps to discrete factors
   are continuous. Conversely, agreement at a sufficiently large a bounds the difference
   in norm by r^(-a), proving continuity of the inverse residue-limit identification.
9. Compose step 4 with step 6 and the product of step 8. This is the required topological
   group equivalence. Its prime-power coordinates give precisely the displayed formula;
   only the compatible primitive-root family is a noncanonical choice. -/
theorem compatible_roots_product (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    (∃ ζ : Order p → kˣ, IsCompatiblePrimitiveFamily p ζ) ∧
    ∀ ζ : Order p → kˣ, IsCompatiblePrimitiveFamily p ζ →
      ∃ e : @ContinuousMulEquiv (limitSubgroup k p) (limitTopology k p)
          (AdicProduct p) inferInstance inferInstance inferInstance,
        ∀ (x : limitSubgroup k p) (r : {r : Nat.Primes // (r : ℕ) ≠ p})
          (a : ℕ) (m : Order p), m.1 = (r : ℕ) ^ a →
            x.1 m = ζ m ^
              ((@PadicInt.toZModPow r.1 (Fact.mk r.1.2) a)
                (Multiplicative.toAdd (e x) r)).val := by
  sorry

end TameRoots
