/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V7
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Connected.Clopen
import Sheaf.AlgebraicGeometry.SteinFactorizationAffine
import Sheaf.AlgebraicGeometry.IntegralFibreEtaleSplitting
import Sheaf.AlgebraicGeometry.SteinFiniteFibresResidueFields

/-!
# Extending geometric fibre components to an étale clopen partition

Source: Stacks Project, More on Morphisms, Tag 0BUI, proof via Tags 03H2, 0E0M, 0BSR.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper family admits, étale locally at a chosen base point, a finite clopen
partition whose traces on that geometric fibre are connected and nonempty.
No flatness is needed for this extension statement.

Source: Stacks Project, More on Morphisms, Tag 0BUI, proof, from affine Stein
factorization (03H2), finite Stein fibres (0E0M), and integral étale splitting (0BSR).
(blueprint: lem-weil-pbc-etale-geometric-fibre-clopen-partition)

Proof: First restrict to an affine open neighbourhood of the base point. Apply the
canonical affine Stein factorization X → T → S. Its first map is proper with
geometrically connected fibres, and its second map is integral with finite point
fibre and finite residue extensions. Integral étale splitting gives a pointed affine
étale neighbourhood U and a finite disjoint clopen partition V_i of T_U. Each V_i
has a unique point over u, with purely inseparable residue field over κ(u).
Pull this partition back to X_U. After extension to an algebraic closure of κ(u),
each V_i has exactly one point: its ordinary fibre is radicial, and nonemptiness
survives field extension. The base change of X → T still has connected nonempty
fibres, so the inverse image of that point is connected and nonempty. These are
exactly the traces of the pulled-back partition on the geometric fibre.
Compose U → S with the initial affine open immersion. Pullback associativity
transports the clopen partition and its fibre traces to the original family.
The empty partition is permitted when the chosen fibre is empty. -/
theorem Scheme.Hom.exists_etale_geometricFiber_clopen_partition
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : S) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U), Etale g ∧ g u = s ∧
      ∃ (m : ℕ) (V : Fin m → (pullback f g).Opens),
        (∀ i, IsClosed (V i : Set ↥(pullback f g))) ∧
        Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧ (⨆ i, V i) = ⊤ ∧
        ∀ i, _root_.IsConnected
          (pullback.fst (pullback.snd f g)
            (Spec.map (CommRingCat.ofHom (algebraMap (U.residueField u)
              (AlgebraicClosure (U.residueField u)))) ≫ U.fromSpecResidueField u) ⁻¹'
            (V i : Set ↥(pullback f g))) := by
  sorry

end AlgebraicGeometry
