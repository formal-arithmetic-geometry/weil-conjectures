/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-! # Global generation after a sufficiently positive ample twist

Source: EGA II, Proposition 4.5.5, implication ample ⇒ d); Stacks Project,
Properties, Proposition 01Q3, (1) ⇒ (7)
(blueprint: lem-weil-pbc-coherent-twist-global-generation).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite type quasi-coherent module twisted by sufficiently large powers of an
absolutely ample invertible module has a finite family of generating global sections.
Here `σ.IsFiniteType` says that the index type of the generating sections is finite;
the evaluation map from the free module on that family is an epimorphism by `σ.epi`.
The exponent is a natural number, since the node uses nonnegative tensor powers.

Source: EGA II, Proposition 4.5.5, last paragraph of the proof; Stacks Project,
Properties, Proposition 01Q3, (1) ⇒ (7)
(blueprint: lem-weil-pbc-coherent-twist-global-generation).

Proof following the six steps of the node:
1. Absolute ampleness gives quasi-compactness. The lemma
   `lem-weil-pbc-ample-scheme-separated` gives separatedness, so
   `lem-pc-section-clearing-denominators` applies.
2. Choose a finite affine cover by nonvanishing loci of sections of positive powers of L.
   Replace the sections by powers to put them all in one degree m > 0; their nonvanishing
   loci do not change, since the maximal ideals in the stalks are prime.
3. For any finite type quasi-coherent G, choose finite generators on each affine of this
   cover by `lem-weil-pbc-affine-finite-type-generating-sections`.
4. Extend each local generator after twisting by a suitable power of L^m, using
   `lem-pc-section-clearing-denominators`. Multiplication by further powers of the
   covering section extends these generators for every sufficiently large multiple of m.
5. By `lem-weil-pbc-nonvanishing-section-trivializes`, the covering section trivializes
   the twisting module on its nonvanishing locus. The extended generators therefore
   generate on every affine in the cover. Their finite union gives a sheaf epimorphism
   from the free module, as in `def-weil-pbc-generating-sections`.
6. Apply steps 3–5 to G = F tensor L^p for each 0 ≤ p < m. These modules remain
   quasi-coherent of finite type, since L is locally trivial. Take the maximum K of the
   finitely many bounds. For d ≥ mK, write d = mk + p with 0 ≤ p < m and k ≥ K;
   the resulting finite generating family gives the assertion. -/
theorem exists_finite_generatingSections_tensorPow_of_isAmple
    (X : Scheme.{u}) (L F : X.Modules) [L.IsInvertible]
    (hL : IsAmple X L) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ d₀ : ℤ, ∀ d : ℕ, d₀ ≤ (d : ℤ) →
      ∃ σ : (tensorObj F (L.tensorPow d)).GeneratingSections, σ.IsFiniteType := by
  sorry

end AlgebraicGeometry.Scheme.Modules
