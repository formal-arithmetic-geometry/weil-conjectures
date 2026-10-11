/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.RingTheory.HenselianTerminology
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Finite algebras over henselian local rings

Source: Stacks Project, Algebra, Lemma 10.153.4, Tag 04GH, parts (1) and (2)
(blueprint: lem-weil-pbc-finite-over-henselian-local-product).
-/

universe u v

namespace HenselianLocalRing

/-- A module-finite algebra over a henselian local ring is a finite product of henselian
local algebras, with local structure maps and finite residue-field extensions.
Source: Stacks Project, Algebra, Lemma 10.153.4 (Tag 04GH), parts (1) and (2)
(blueprint: lem-weil-pbc-finite-over-henselian-local-product).

Proof:
1. The henselian étale retraction property (lem-weil-pbc-henselian-etale-retraction) and
   lem-weil-pbc-etale-retraction-finite-product-local decompose B into finitely many local
   factors. Each factor is finite over R because its projection is surjective.
2. By lem-weil-pbc-finite-algebra-local-radical, each factor's maximal ideal pulls back to
   the maximal ideal of R, so the structure map is local. Reducing finite module generators
   modulo the factor's maximal ideal gives generators over the residue field of R. This
   gives a finite field extension in the sense of def-pc-field-extension.
3. Any finite algebra C over a factor is finite over R, hence is again a product of local
   rings by the same two lemmas from Step 1. Each local component is finite over the factor,
   so lem-weil-pbc-finite-algebra-local-radical shows its structure map is local. Its quotient
   by the factor's maximal ideal is local too. Thus idempotents of this quotient product
   are precisely componentwise zero-one vectors, which lift uniquely to the same vectors
   in C. This is the henselian criterion of def-weil-pbc-henselian-terminology.
4. Combine these properties with the product isomorphism. For the zero algebra use r = 0;
   the product over Fin 0 is the zero ring and there are no factor conditions to check. -/
theorem finite_over_henselian_exists_algEquiv_pi
    (R : Type u) (B : Type v) [CommRing R] [CommRing B]
    [HenselianLocalRing R] [Algebra R B] [Module.Finite R B] :
    ∃ (r : ℕ) (A : Fin r → Type v) (rings : ∀ i, CommRing (A i)),
      letI := rings
      ∃ (algebras : ∀ i, Algebra R (A i)),
        letI := algebras
        ∃ (henselian : ∀ i, HenselianLocalRing (A i)),
          letI := henselian
          ∃ (localMaps : ∀ i, IsLocalHom (algebraMap R (A i))),
            letI := localMaps
            Nonempty (B ≃ₐ[R] (∀ i, A i)) ∧
              (∀ i, Module.Finite R (A i)) ∧
              (∀ i, Module.Finite (IsLocalRing.ResidueField R)
                (IsLocalRing.ResidueField (A i))) := by
  sorry

end HenselianLocalRing
