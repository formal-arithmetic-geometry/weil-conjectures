/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
import Sheaf.RingTheory.RingPseudoCoherent
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Homology.Additive
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Lifting finite stably free complexes modulo an ideal

Source: Stacks Project, More on Algebra, Tag 0BCB, lemma-lift-complex-stably-frees
(blueprint: lem-sc-pseudo-coherent-lift-stably-free-complex).
-/

universe u v w w'

open CategoryTheory

namespace DerivedCategory

/-- A bounded above finite stably free complex representing the derived reduction of a
pseudo-coherent object lifts to such a complex over the original ring. Terms whose reductions
are free are free simultaneously.
Source: Stacks Project, More on Algebra, Tag 0BCB, lemma-lift-complex-stably-frees
(blueprint: lem-sc-pseudo-coherent-lift-stably-free-complex).

The representative `Classical.choose hK` is bounded above and finite free, hence K-flat.
Consequently its termwise extension of scalars computes `K ⊗ᴸ R/I`; `hE` says precisely that
`E` represents this derived reduction. `Module.Finite` together with `Module.IsStablyFree`
means finite stably free, equivalently a finite free stabilization of finite rank.

Proof:
1. Apply `lem-sc-complex-lift-class-projective` to the finite stably free modules. They are
   projective. Finite direct sums stay in the class, and in a split exact sequence the
   class satisfies the two-out-of-three condition with its first and middle terms fixed
   (Stacks Tag 0BC3). This is the class condition required by the general lifting lemma.
2. A map in the class surjective modulo `I` is surjective: its finite cokernel vanishes
   modulo `I`, so Nakayama and the one-plus-ideal unit hypothesis kill that cokernel.
3. Lift each finite stably free quotient module using its stable presentation and a lifted
   split projection (Stacks Tag 0BC4). Pseudo-coherence supplies a bounded above finite free
   representative of `K`. The general lemma then gives `P` representing `K`, with reduction
   isomorphic to `E` as a complex, including all differentials.
4. If `E.X i` is free of rank `n`, lift its basis to a map `R^n → P.X i`. Nakayama makes
   this map surjective, and projectivity splits it. The finite kernel has zero reduction
   since the reduced map is an isomorphism, so Nakayama kills the kernel. Hence `P.X i`
   is free, for every such `i` (Stacks Tag 0BC6). -/
theorem exists_stablyFree_lift_mod_ideal
    {R : Type u} [CommRing R] (I : Ideal R)
    (hunits : ∀ x : I, IsUnit (1 + (x : R)))
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{max u v} (R ⧸ I))]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : IsPseudoCoherent K)
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (hEbound : ∃ b : ℤ, E.IsStrictlyLE b)
    (hEterms : ∀ i : ℤ,
      Module.Finite (R ⧸ I) (E.X i) ∧ Module.IsStablyFree (R ⧸ I) (E.X i))
    (hE : Nonempty (Q.obj
      (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (Classical.choose hK)) ≅ Q.obj E)) :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∃ b : ℤ, P.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Finite R (P.X i) ∧ Module.IsStablyFree R (P.X i)) ∧
      Nonempty (Q.obj P ≅ K) ∧
      Nonempty (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ≅ E) ∧
      (∀ i : ℤ, Module.Free (R ⧸ I) (E.X i) → Module.Free R (P.X i)) := by
  sorry

end DerivedCategory
