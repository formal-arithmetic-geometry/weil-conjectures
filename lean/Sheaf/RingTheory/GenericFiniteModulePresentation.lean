/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.FinitePresentation

import Mathlib.RingTheory.Noetherian.Basic

/-!
# Generic finite presentation of finite modules

Source: Stacks Project, Tag 051T, Lemma `algebra-lemma-generic-flatness`, conclusion (b)
for the module (blueprint: lem-pur-generic-finite-module-presentation).
-/

@[expose] public section

universe u v w

namespace Module.Finite

/-- A finite module over a finite type algebra over a domain becomes finitely presented
when a nonzero element of the base is inverted. The localization is taken at the image
of that element in the algebra, with the standard module-of-fractions construction.

Source: Stacks Project, Tag 051T, conclusion (b) for the module.
(blueprint: lem-pur-generic-finite-module-presentation)

Proof:
1. Choose a surjection P = R[x₁,...,xₙ] → B by
`def-weil-pbc-finite-type-algebra`. A finite generating family of M over B also generates
it over P by lifting coefficients. Let q : Pᵗ → M be the resulting surjection and N its
kernel.
2. Let K be the fraction field of R. Clearing denominators identifies P localized at the
nonzero base elements with K[x₁,...,xₙ]. Localizing q preserves surjectivity and identifies
its kernel with N localized: if q(v)/s = 0, some nonzero h kills q(v), so hv belongs to N.
3. K is Noetherian. By `lem-weil-pbc-finite-type-algebra-noetherian`, P_K is Noetherian;
by `lem-weil-pbc-noetherian-submodule-finite`, N_K has finitely many generators. Lift their
numerators to nᵢ in N; the nᵢ/1 still generate N_K since their denominators are units.
4. Put H = ∑ᵢ Pnᵢ and L = Pᵗ/H. The relation columns give a finite presentation of L.
The induced surjection L → M has torsion kernel over R: an expression for v/1 in N_K,
a common denominator s, and a further nonzero factor h witnessing equality of fractions
give hsv in H for every v in N.
5. By `lem-pur-fp-algebra-module-generic-freeness` applied to the polynomial algebra P
and L, choose nonzero a with L_a free over R_a. The map L_a → M_a is surjective. An element
of its kernel is killed by a nonzero s in R by step 4. The image of s in R_a is nonzero,
since R_a embeds into K. Multiplication by it is injective on a free R_a-module, so the
kernel vanishes and L_a → M_a is an isomorphism.
6. The finite presentation of L localizes to P_aᵘ → P_aᵗ → L_a → 0: if v/aʲ maps to
zero, some aᵏv belongs to H, so the localized relation columns generate the kernel.
Surjectivity follows by lifting numerators. Replace L_a by M_a using step 5.
7. The map P_a → B_a is surjective. Lift a vector in the kernel of B_aᵗ → M_a
coefficientwise to P_aᵗ, express it using the finitely many relation columns from step 6,
and reduce the coefficients to B_a. Their images therefore generate the kernel and give
B_aᵘ → B_aᵗ → M_a → 0. This also covers zero ranks, the zero algebra, and zero generic fibre.
-/
theorem exists_finitePresentation_localizedModule_powers
    (R : Type u) (B : Type v) (M : Type w)
    [CommRing R] [IsDomain R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [AddCommGroup M] [Module B M] [Module.Finite B M] :
    ∃ a : R, a ≠ 0 ∧
      Module.FinitePresentation (Localization.Away (algebraMap R B a))
        (LocalizedModule.Away (algebraMap R B a) M) := by
  sorry

end Module.Finite
