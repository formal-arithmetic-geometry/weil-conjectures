/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.RingTheory.Smooth.IntegralClosure
import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise
import WeilConjectures.RingTheory.IntegralElementsColimitDescent

/-! # Integral closure commutes with ind-etale base change

Source: Stacks Project, Algebra, Tag 0CBF, lemma-integral-closure-commutes-colim-smooth,
specialized to ind-etale algebras.
(blueprint: lem-sfb-integral-closure-ind-etale-base-change).
-/

@[expose] public section
set_option autoImplicit false

universe u v w

namespace TensorProduct

/-- The canonical comparison from the scalar extension of the integral closure to the
integral closure after scalar extension is bijective for an ind-etale ring map.
Its underlying formula is `s ⊗ c ↦ s ⊗ c`, by `TensorProduct.toIntegralClosure`.
Source: Stacks Project, Algebra, Tag 0CBF, lemma-integral-closure-commutes-colim-smooth,
specialized to etale stages (Tag 03GE).
(blueprint: lem-sfb-integral-closure-ind-etale-base-change).

Proof:
1. Transport the rings to a common universe using the canonical ULift equivalences in
   `RingHom.IndEtaleAcrossUniverses`. Choose the filtered etale presentation, and use
   `lem-weil-pbc-filtered-category-directed-cofinal` to reindex by a nonempty directed set.
   Put C = integralClosure R B, E_i = S_i tensor C and D_i = S_i tensor B.
   By `lem-sfb-integral-closure-etale-base-change`, the comparison at every stage is
   bijective, and the induced map f_i : E_i to D_i is injective.
2. By `lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise`, applied to C and B,
   elements lift to stages and elements mapping to zero vanish at a later stage.
   Tensor transition maps commute with f_i, as checked on pure tensors. Integrality
   at a stage maps to integrality at the colimit by mapping a monic equation, so the
   resulting map lands in integralClosure S (S tensor B). It is the canonical comparison.
3. If a tensor t maps to zero, lift it to t_i. Its image f_i(t_i) vanishes at a later
   stage j. Compatibility and injectivity of f_j imply that the transition image of
   t_i is zero, and hence t is zero. Apply this to differences to get injectivity.
4. Lift an integral element x to x_i in D_i. Restrict to the directed upper tail of i,
   which has the same colimit. This algebra colimit is also a ring colimit: the maps
   of any ring cocone induce a common R-algebra structure, independently of the stage
   by directedness. Cancel iterated tensor base changes by the mutually inverse formulas
   t tensor (s tensor b) maps to ts tensor b and t tensor b maps to t tensor (1 tensor b).
   Apply `lem-weil-pbc-integral-tensor-generators-colimit-descent` with B_0 = S_i,
   C_0 = D_i, its structure map, and the singleton containing x_i. Integrality of x
   then descends to a stage j above i.
5. The stage comparison is surjective, so the integral image x_j has a preimage in E_j.
   Its image at the colimit maps to x by compatibility. This proves surjectivity.
   Transport back along the canonical ULift equivalences; the comparison is preserved
   since its pure-tensor formula is preserved. Bijectivity of this S-algebra map is
   exactly the claimed isomorphism, via AlgEquiv.ofBijective. Zero rings and
   noninjective ring maps or transition maps require no additional hypothesis.
-/
theorem toIntegralClosure_bijective_of_indEtale
    (R : Type u) (S : Type v) (B : Type w)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    (hS : RingHom.IndEtaleAcrossUniverses (algebraMap R S)) :
    Function.Bijective (TensorProduct.toIntegralClosure R S B) := by
  sorry

end TensorProduct
