/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.Algebra.Homology.KFlat

/-!
# Bounded-above flat complexes on a ringed site are K-flat

Source: Stacks Project, Cohomology on Sites, Lemma 21.17.8 (Tag 06YQ), also used in the
proof of Lemma 06YS (blueprint: lem-pc-bounded-above-flat-kflat-site).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- (blueprint: lem-pc-bounded-above-flat-kflat-site) A bounded-above cochain complex of
flat sheaves of modules over a sheaf of commutative rings on a site is K-flat.
Source: Stacks Project, Cohomology on Sites, Lemma 21.17.8 (Tag 06YQ), used in Tag 06YS.

Proof:
1. Given an acyclic complex `A`, its good truncations `τ≤m A` are acyclic and bounded above:
   the cohomology agrees with that of `A` below and at `m`, and vanishes above `m`
   (`def-pc-acyclic-complex-modules`). Their filtered termwise colimit is `A`.
   Tensor products and totalization commute with these colimits
   (`lem-pc-module-filtered-colimits-tensor`, `def-pc-tensor-complex-sheaves`). Exactness of
   filtered colimits implies that a filtered colimit of acyclic complexes is acyclic.
2. For each bounded-above acyclic truncation, its total tensor complex with `P` is acyclic
   by `lem-pc-bounded-above-flat-tensor-acyclic`, since every term of `P` is flat
   (`def-pc-flat-sheaf-modules`). Thus the total tensor complex with the original `A` is acyclic.
3. Since `A` was arbitrary, `def-pc-kflat-complex` gives K-flatness of `P`. -/
theorem isKFlat_of_boundedAbove_flat
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    {R : Sheaf J CommRingCat.{u}}
    (P : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) : P.IsKFlat := by
  sorry

end CochainComplex
