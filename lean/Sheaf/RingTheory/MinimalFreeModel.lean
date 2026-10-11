/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Sheaf.RingTheory.RingPseudoCoherent
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Minimal finite free models over local rings

Source: Stacks Project, More on Algebra, Tag 0BCC, lemma-lift-pseudo-coherent-from-residue-field
(blueprint: lem-sc-perfect-local-pseudocoherent-free-model).
-/

universe u v w

open CategoryTheory

namespace DerivedCategory

/-- A pseudo-coherent object over a local ring has a bounded above finite free model with
ranks equal to the dimensions of its derived residue cohomology, unique as a complex.
Source: Stacks Project, More on Algebra, Tag 0BCC
(blueprint: lem-sc-perfect-local-pseudocoherent-free-model).
The finite free representative chosen from `hK` is bounded above, hence K-flat; its
termwise extension of scalars computes `K ⊗ᴸ κ`. Thus `hd` specifies the intrinsic ranks,
independently of the representative chosen by classical choice.

Proof:
1. Choose an upper bound for the nonzero `d i`. Split the residue complex over the field
   by choosing complements to boundaries in cycles and to cycles in terms. Its derived
   object is represented by the zero-differential complex with terms `κ^(d i)`.
2. Apply `lem-sc-pseudo-coherent-lift-stably-free-complex` (Tag 0BCB) with the maximal ideal.
   Every element of one plus that ideal is a unit. This lifts the residue complex to a
   bounded above finite free complex representing `K` with the prescribed reduction.
3. Reduction preserves finite free ranks, so the lifted term in degree `i` has rank `d i`.
   Transport the differentials along termwise isomorphisms to the displayed free modules.
4. For uniqueness, `lem-pc-ring-derived-map-representative` represents a derived isomorphism
   and its inverse by chain maps, whose composites are homotopic to the identities.
   `lem-pc-module-bounded-flat-kflat` identifies termwise reduction with derived reduction.
   The formula dim H^i = dim C^i - rank d^i - rank d^(i-1) forces both reduced differentials
   to vanish. The reduced comparison is therefore a termwise isomorphism. Nakayama
   (`lem-weil-pbc-nakayama-local-generators`) makes each comparison surjective; splitting
   onto its free target and applying Nakayama to the finite kernel makes it injective.
   Consequently the comparison is an isomorphism of complexes. -/
theorem exists_unique_minimalFreeModel
    {R : Type u} [CommRing R] [IsLocalRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : IsPseudoCoherent K)
    (d : ℤ → ℕ)
    (hfinite : ∀ i : ℤ, Module.Finite (IsLocalRing.ResidueField R)
      ((((ModuleCat.extendScalars (IsLocalRing.residue R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (Classical.choose hK)).homology i))
    (hd : ∀ i : ℤ, d i = Module.finrank (IsLocalRing.ResidueField R)
      ((((ModuleCat.extendScalars (IsLocalRing.residue R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (Classical.choose hK)).homology i))
    (hbound : ∃ b : ℤ, ∀ i : ℤ, b < i → d i = 0) :
    ∃ F : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∃ b : ℤ, F.IsStrictlyLE b) ∧ Nonempty (Q.obj F ≅ K) ∧
      (∀ i : ℤ, Nonempty (F.X i ≅ ModuleCat.of R (ULift.{v} (Fin (d i) → R)))) ∧
      (∀ G : CochainComplex (ModuleCat.{max u v} R) ℤ,
        (∃ b : ℤ, G.IsStrictlyLE b) → Nonempty (Q.obj G ≅ K) →
        (∀ i : ℤ, Nonempty (G.X i ≅ ModuleCat.of R (ULift.{v} (Fin (d i) → R)))) →
        Nonempty (F ≅ G)) := by
  sorry

end DerivedCategory
