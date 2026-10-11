/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.AlgebraicGeometry.SimplicialHomObject
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Local lifting along finite simplicial inclusions in a hypercover

Source: Stacks Project, Tag 01GN (Lemma 25.8.2), using Tag 01GM and unpacking Tag 01G3
(blueprint: lem-weil-pbc-hypercover-finite-simplex-lifting).
-/

universe u w t

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.Scheme

/-- Restriction along a finite simplicial inclusion is a covering and admits local lifts
of every étale test object's point. The Hom objects are arbitrary representing pairs for
`simplicialHomFamilyFunctor`, so the assertion applies to the fixed choices of those pairs.
Source: Stacks Project, Tag 01GN, with the local-lifting clause unpacked from Tag 01G3
(blueprint: lem-weil-pbc-hypercover-finite-simplex-lifting).

Proof:
1. By lem-weil-pbc-simplicial-set-add-simplices (Stacks 018S), insert finitely many
   nondegenerate simplices one at a time between `A` and `B`. Every intermediate subset
   has finite nonempty degrees, since it lies between `A` and `B`. Its nondegenerate
   simplices remain nondegenerate in `B`: a degeneracy of a simplex in the subset has
   its ancestor in that subset by applying an order-preserving section of the surjection
   in the epi-mono factorization. Thus each intermediate subset is finite.
2. Apply lem-weil-pbc-hypercover-one-more-simplex (01GM) to each extension. Its
   restriction map is a covering by the matching-cover condition on `K`.
3. The universal property in def-weil-pbc-simplicial-hom-object identifies the full
   restriction with the composite of those maps. Coverings are closed under composition
   by lem-weil-pbc-semi-representable-covering-permanence (01G4). For a chain of length
   zero it is the identity, which is a covering in def-weil-pbc-etale-site.
4. Write a test point as `(j, a : T → H_A.obj j)` using
   def-weil-pbc-semi-representable-object. Pull back the covering components over `j`
   along `a`. By lem-weil-pbc-etale-covering-base-change the projections form an étale
   covering of `T`; the other projections are points of `H_B`, and the pullback equation
   says their restrictions are the pullbacks of `a`. -/
theorem hypercover_finite_simplex_lifting (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale))
    (hK : IsSemiRepresentableHypercover K) (B : SSet.{t}) (A : B.Subcomplex)
    [B.Finite] [A.toSSet.Finite]
    (hBfinite : ∀ n : ℕ, Finite (B.obj (op ⦋n⦌)))
    (hBnonempty : ∀ n : ℕ, Nonempty (B.obj (op ⦋n⦌)))
    (hAfinite : ∀ n : ℕ, Finite (A.toSSet.obj (op ⦋n⦌)))
    (hAnonempty : ∀ n : ℕ, Nonempty (A.toSSet.obj (op ⦋n⦌)))
    (H_B H_A : FormalCoproduct.{w} X.Etale)
    (uB : SimplicialHomFamily K B H_B)
    (uA : SimplicialHomFamily K A.toSSet H_A)
    (huB : (simplicialHomFamilyFunctor K B).IsRepresentedBy uB)
    (huA : (simplicialHomFamilyFunctor K A.toSSet).IsRepresentedBy uA) :
    IsSemiRepresentableCovering (simplicialHomRestriction A uB huA) ∧
      ∀ (T : X.Etale) (a : semiRepresentablePoints T H_A),
        ∃ (ι : Type w) (Tc : ι → X.Etale) (p : ∀ c : ι, Tc c ⟶ T),
          Sieve.ofArrows Tc p ∈ X.smallEtaleTopology T ∧
            ∃ b : ∀ c : ι, semiRepresentablePoints (Tc c) H_B,
              ∀ c : ι, b c ≫ simplicialHomRestriction A uB huA =
                (FormalCoproduct.incl X.Etale).map (p c) ≫ a := sorry

end AlgebraicGeometry.Scheme
