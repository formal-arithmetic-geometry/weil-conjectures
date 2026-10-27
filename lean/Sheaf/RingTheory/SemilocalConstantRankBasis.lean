module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs

import Sheaf.RingTheory.LocalTrivializationResidueRank
import Sheaf.RingTheory.BasisOfMaximalResidueBases

/-! # Constant-rank bases over semilocal rings

Source: Stacks Project, Algebra, Tag 02M9, lemma-locally-free-semi-local-free
(blueprint: lem-sfb-semilocal-constant-rank-basis).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Module

/-- A module which is free of a fixed rank on a finite principal cover of a semilocal
ring is free of that rank.

Source: Stacks Project, Algebra, Tag 02M9, lemma-locally-free-semi-local-free;
the finite principal-open formulation is the node's statement
(blueprint: lem-sfb-semilocal-constant-rank-basis).

Proof:
1. If `R` is the zero ring, each `x : M` satisfies `x = 1 • x = 0 • x = 0`.
   The unique map from the coordinate module to `M` is bijective and yields a basis
   of every size (`def-weil-pbc-free-module`). This includes an empty cover.
2. Otherwise enumerate the distinct maximal ideals `q₁, ..., qₛ`. At each `qₐ`,
   some `t i` avoids `qₐ`, since otherwise their unit-ideal linear combination
   would put `1` in `qₐ`. Apply `lem-a1-local-trivialization-residue-rank`
   (`local_trivialization_residue_rank`) with `E = R`, `P = M`, and `r = n`.
   It gives a rank-`n` basis at `qₐ` and dimension `n` for `M / qₐM` over `R / qₐ`.
   Choose a basis of each residue module and lift its vectors to `xₐₖ : M`.
3. For distinct maximal ideals, `qₐ + qᵦ = R`: their sum strictly contains `qₐ`.
   Choose `uₐᵦ ∈ qᵦ` and `vₐᵦ ∈ qₐ` with `uₐᵦ + vₐᵦ = 1`, and put
   `eₐ = ∏ (b ≠ a), uₐᵦ`. Each factor is `1` modulo `qₐ`, while for `b ≠ a`
   the product has a factor in `qᵦ`. Thus `eₐ` is `1` modulo `qₐ` and `0` modulo
   the other maximal ideals. For one maximal ideal, the empty product is `1`.
   The weights need not be idempotent.
4. Put `xₖ = ∑ a, eₐ • xₐₖ`. Modulo each `qᵦM`, its image equals the chosen
   `k`-th basis vector, so this single family gives a basis in every residue module.
   For `n = 0` these are empty families and the same computation is vacuous.
5. Apply `lem-a1-basis-of-maximal-residue-bases`
   (`bijective_linearCombination_of_maximal_residue_bases`) to this family,
   the maximal-localization bases of step 2, and the residue bases of step 4.
   The coordinate map is bijective, which is exactly the required basis property
   (`def-weil-pbc-free-module`), including rank zero.
-/
theorem semilocal_constant_rank_basis
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Finite (MaximalSpectrum R)] (n m : ℕ) (t : Fin m → R)
    (ht : Ideal.span (Set.range t) = ⊤)
    (hfree : ∀ i : Fin m,
      Nonempty (Module.Basis (Fin n) (Localization.Away (t i))
        (LocalizedModule.Away (t i) M))) :
    Nonempty (Module.Basis (Fin n) R M) := by
  sorry

end Module
