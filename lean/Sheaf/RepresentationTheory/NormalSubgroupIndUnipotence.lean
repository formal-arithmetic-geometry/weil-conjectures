/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.RepresentationTheory.SubgroupUnipotence
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Separation.Profinite
import WeilConjectures.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct
import Sheaf.AlgebraicGeometry.EtaleFieldGsets

/-!
# Ind-unipotence for a closed normal subgroup

Source: ILO, Expose XVII, Definitions 11.1.1–11.1.2, Proposition 11.2.1 and
Propositions 11.3.1–11.3.4, pp. 327–330
(blueprint: lem-per-normal-subgroup-ind-unipotence).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

variable {R : Type u} [CommRing R] {G : Type v} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- Closure properties and augmentation criteria for normal-subgroup ind-unipotence.
Source: ILO XVII 11.1–11.3, especially 11.2.1(ii),(iii),(vii),(ix)–(xi) and 11.3.4,
pp. 327–330 (blueprint: lem-per-normal-subgroup-ind-unipotence).

Proof: (1) Expand the augmentation ideal into words in [h]-1. Its q-th annihilator F_q
is increasing, starts at zero, and is G-stable by normality. Multiplication by the ideal
sends F_(q+1) into F_q. (2) A length-q filtration gives I^q M = 0; conversely the F_i
provide the required filtration. Submodules and quotients retain open stabilizers.
(3) Local annihilation passes to submodules, quotients and direct sums by finite support.
(4) A small colimit is the direct sum modulo the equivariant relation submodule; this
also proves continuity and includes the empty diagram. (5) Filtered colimits of unipotents
are locally annihilated; conversely the increasing F_q exhaust a locally annihilated M
and present it as their filtered colimit. (6) For finite R-generators take the maximum
of their exponents, using def-weil-finitely-generated-module.
(7) For an extension and b in its middle term, the finite-orbit theorem
lem-exc-discrete-continuous-action-finite-orbit-coproduct gives a finite G-orbit S.
The integral span N of S has action through a finite permutation group. A single exponent
a kills the image of S in the quotient. (8) The integral augmentation power J^a N has
a finite list of generators: all length-a words in the finite H-image applied to S.
(9) Their finitely many annihilation exponents have a common bound c; thus J^(a+c)b=0.
Integral and R-coefficient annihilation coincide by the word description. This proves
extension closure without a Noetherian assumption on R. (10) Ordinary module kernels
and quotient cokernels are discrete and retain ind-unipotence. Their universal module
factorizations are equivariant and remain universal in the full subcategory, proving
preservation. The zero module is killed by the zeroth power. -/
theorem normal_subgroup_ind_unipotence
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) [H.Normal] (hH : IsClosed (H : Set G)) :
    (subgroupIndUnipotent.{u, v, w} (R := R) H).IsClosedUnderSubobjects ∧
    (subgroupIndUnipotent.{u, v, w} (R := R) H).IsClosedUnderQuotients ∧
    (subgroupIndUnipotent.{u, v, w} (R := R) H).IsClosedUnderExtensions ∧
    HasColimitsOfSize.{w, w} (DiscreteContinuousRep.{u, v, w} R G) ∧
    (∀ (J : Type w) [SmallCategory J],
      (subgroupIndUnipotent.{u, v, w} (R := R) H).IsClosedUnderColimitsOfShape J) ∧
    (∀ (X Y : (subgroupIndUnipotent.{u, v, w} (R := R) H).FullSubcategory) (f : X ⟶ Y),
      HasKernel f ∧ HasCokernel f ∧
      PreservesLimit (parallelPair f 0) (subgroupIndUnipotent.{u, v, w} (R := R) H).ι ∧
      PreservesColimit (parallelPair f 0) (subgroupIndUnipotent.{u, v, w} (R := R) H).ι) ∧
    (∀ M : DiscreteContinuousRep.{u, v, w} R G,
      subgroupIndUnipotent H M ↔ ∀ m : M.obj.V, ∃ q : ℕ,
        SubgroupAugmentationKills H M q m) ∧
    (∀ (M : DiscreteContinuousRep.{u, v, w} R G) [Module.Finite R M.obj.V],
      (subgroupIndUnipotent H M ↔ IsSubgroupUnipotent H M) ∧
      (IsSubgroupUnipotent H M ↔ ∃ q : ℕ,
        ∀ m : M.obj.V, SubgroupAugmentationKills H M q m)) ∧
    (∀ M : DiscreteContinuousRep.{u, v, w} R G,
      Subsingleton M.obj.V → subgroupIndUnipotent H M) := by
  sorry

end Rep
