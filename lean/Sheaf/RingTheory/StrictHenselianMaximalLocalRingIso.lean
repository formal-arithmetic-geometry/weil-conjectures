/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.RingTheory.ProEtale.HenselianLocalRing

/-! # Local rings above a strictly henselian maximal point

Source: blueprint, proetale coefficients, "Local rings of a weakly etale algebra over a
strictly henselian point"; Stacks Project, More on Algebra, Tag 092Z
(blueprint: det-pe-wc-rings-local-iso).
-/

@[expose] public section

universe u v

namespace Algebra.WeaklyEtale

/-- The canonical local-ring map above a strictly henselian maximal point is an isomorphism.
Source: blueprint, proetale coefficients, `det-pe-wc-rings-local-iso`; Stacks Project,
More on Algebra, Tag 092Z, Theorem Olivier (blueprint: det-pe-wc-rings-local-iso).

Proof:
1. In the ind-etale example, `lem-weil-pbc-ind-etale-stability` gives weak etaleness.
   Base change along `R -> R_m` preserves weak etaleness by that same node.
2. The map `B tensor_R R_m -> B_n` is a localization, since `n` contracts to `m`.
   Express it as the filtered colimit of principal localizations. It is ind-Zariski,
   hence weakly etale, again by `lem-weil-pbc-ind-etale-stability`.
3. Composition gives a weakly etale map `R_m -> B_n`. The contraction equality
   makes it a local homomorphism of local rings.
4. Apply Olivier's theorem `thm-weil-pbc-weak-etale-strict-local` to this local map
   with strictly henselian source. Its bijectivity says precisely that the canonical
   ring homomorphism is an isomorphism. -/
theorem bijective_localRingHom_of_isMaximal_of_isStrictlyHenselianLocalRing
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.WeaklyEtale R B] (m : Ideal R) [m.IsMaximal]
    [IsStrictlyHenselianLocalRing (Localization.AtPrime m)]
    (n : Ideal B) [n.IsPrime] (hmn : m = n.comap (algebraMap R B)) :
    Function.Bijective (Localization.localRingHom m n (algebraMap R B) hmn) := by
  sorry

end Algebra.WeaklyEtale
