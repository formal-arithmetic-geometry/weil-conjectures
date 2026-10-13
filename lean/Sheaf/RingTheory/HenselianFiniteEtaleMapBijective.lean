/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.Finite

import Sheaf.RingTheory.EtaleRetractionFiniteProductLocal
import Sheaf.RingTheory.HenselianEtaleRetraction

/-!
# Morphisms of finite étale algebras over a henselian local ring

Source: Stacks Project, Algebra, Tag 04GK, the full-faithfulness argument.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CommAlgCat.FiniteEtale

/-- Reduction induces a bijection on morphisms between finite étale algebras.
Source: Stacks Project, Algebra, Tag 04GK, proof of full faithfulness.
(blueprint: lem-weil-pbc-henselian-finite-etale-map-bijective).

Proof: Decompose each finite étale algebra into local factors using henselian étale
retractions and the finite-product-local theorem (04GG). Their reductions are finite
separable fields: finiteness makes each maximal ideal lie over the maximal ideal of R,
and the étale prime-generation theorem (00U4) identifies that ideal with its extension.
A map from a finite product to a nonzero local ring selects exactly one factor, because
the standard orthogonal idempotents map to idempotents summing to one. Thus it suffices
to compare maps between two local factors S and T. Decompose S ⊗[R] T into local finite
étale factors Aᵢ. A map S → T gives a surjection S ⊗[R] T → T and hence selects a factor
Aᵢ. The projection Aᵢ → T retracts jᵢ : T → Aᵢ; its kernel is a finite direct summand.
Reduction makes the projection a surjection of fields, so the kernel has zero reduction
and vanishes by Nakayama. Conversely, an invertible jᵢ gives the map S → Aᵢ → T.
These constructions are inverse. Over the residue field, maps select exactly the indices
for which the reduced jᵢ is invertible. Such a jᵢ is invertible precisely when its
reduction is: Nakayama first gives surjectivity; the finite flat R-module Aᵢ is free,
so the surjection splits R-linearly, and Nakayama kills its finite kernel. Reduction
preserves the selected index, proving bijectivity for local factors and then products.
The zero algebra is the empty product; maps to it are unique, and maps from it to a
nonzero algebra do not exist, so these cases obey the same product formula. -/
theorem bijective_baseChange_residueField_map_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S T : CommAlgCat.FiniteEtale.{max u v} R) :
    Function.Bijective
      ((baseChange.{max u v} R (IsLocalRing.ResidueField R)).map :
        (S ⟶ T) →
          ((baseChange.{max u v} R (IsLocalRing.ResidueField R)).obj S ⟶
            (baseChange.{max u v} R (IsLocalRing.ResidueField R)).obj T)) := by
  sorry

end CommAlgCat.FiniteEtale
