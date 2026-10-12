/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.RingTheory.FlatPermanence
import WeilConjectures.Mathlib.RingTheory.Filtration

/-!
# The Noetherian fibre criterion for flatness

Source: Stacks Project, Algebra, Tag 00MP, lemma-criterion-flatness-fibre-Noetherian
(blueprint: lem-weil-pbc-criterion-flatness-fibre-noetherian).
-/

@[expose] public section

open scoped TensorProduct
set_option autoImplicit false
universe u v w z

namespace Module

/-- The Noetherian fibre criterion, Stacks Project, Algebra, Tag 00MP
(blueprint: lem-weil-pbc-criterion-flatness-fibre-noetherian).

The scalar towers express restriction along the local maps `R → S → S'`.
The tensor fibre is canonically isomorphic to `M / mM`, not definitionally equal to it.

Proof following the seven steps of the node:
1. Put `I = mS`. Locality gives `I ⊆ m_S`, so `I` is proper. Scalar compatibility
   gives `IM = mM`, and hence the fibre hypothesis says `M/IM` is flat over `S/I`.
2. The map `m ⊗[R] M → I ⊗[S] M`, sending `a ⊗ x` to `φ(a) ⊗ x`, is surjective:
   write `b ∈ I` as a sum of `φ(a_j)s_j`, and move each `s_j` onto the module factor.
   Its composite with multiplication `I ⊗[S] M → M` is multiplication over `R`.
3. Flatness over `R` makes `m ⊗[R] M → M` injective. The surjection of step 2
   therefore makes `I ⊗[S] M → M` injective (Tag 00M6 identifies its kernel with Tor).
4. Apply `lem-weil-pbc-flat-variant-local-criterion` (Tag 00ML) to `S → S'`,
   the proper ideal `I`, finite `M`, step 3 and fibre flatness. Thus `M` is flat over `S`.
5. By `lem-weil-pbc-nakayama-jacobson` (Tag 00DV), finiteness and nonzero `M` give
   `m_{S'}M ≠ M`. Locality gives `m_S M ⊆ m_{S'}M`, hence `M/m_S M ≠ 0`.
6. By `lem-weil-pbc-flat-module-faithfully-flat-maximal-ideals` (Tag 00HP), step 4
   and step 5 make `M` faithfully flat over `S`.
7. Apply `lem-weil-pbc-flat-permanence` (Tag 039V) to `M`, flat over `R` and
   faithfully flat over `S`, to deduce that `S` is flat over `R`. This is the node's
   descent version of the second paragraph of Tag 00MP. Together with step 4 it
   gives both conclusions.
-/
theorem flat_and_flat_of_flat_fibre_noetherian
    (R : Type u) (S : Type v) (S' : Type w) (M : Type z)
    [CommRing R] [CommRing S] [CommRing S']
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [AddCommGroup M] [Module S' M] [Module S M] [Module R M]
    [IsScalarTower S S' M] [IsScalarTower R S M]
    [Module.Finite S' M] [Nontrivial M]
    (h_fibre : Module.Flat
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] M))
    [Module.Flat R M] : Module.Flat R S ∧ Module.Flat S M := by
  sorry

end Module
