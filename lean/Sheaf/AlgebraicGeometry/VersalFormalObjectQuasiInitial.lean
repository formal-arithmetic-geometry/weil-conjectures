module

public import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Versal formal objects map to every formal object

Source: Stacks Project, Formal Deformation Theory, Tag 06HT
(lemma-versal-object-quasi-initial), with Tags 06HN and 06HS
(blueprint: lem-sfb-versal-formal-object-quasi-initial).

## Main definitions and statements

* `FormalObjectMap`: a morphism over a marked local map of complete algebras.
* `exists_formalObjectMap_of_isVersal`: a versal formal object is weakly initial.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

variable {R k : Type u} [CommRing R] [IsNoetherianRing R] [Field k]
  [Algebra R k] [Module.Finite R k]

/-- A morphism of formal objects over possibly different complete local algebras.
Source: Stacks Project, Formal Deformation Theory, Tag 06HT, and the completed
category of Tag 06H3 (blueprint: lem-sfb-versal-formal-object-quasi-initial).

The `atLevel` maps are the actual composites of `hom` with the target quotient
maps, as required by `atLevel_hom`; they are retained as marked local maps so that
we can use the dependency's evaluation and restriction constructions directly.
The equation `atLevel_comm` records the quotient-map identity needed to type the
restriction comparison. Thus these fields introduce no independent ring maps.
The isomorphisms `app` commute with every transition, including equal levels.
Level `n` means exponent `n + 1`, so the residue-field level is included.
-/
structure FormalObjectMap {F : CofibredGroupoids.{u, v, w} R k}
    {C D : CompleteLocalAlgebra R k} (ξ : FormalObject F C) (η : FormalObject F D) where
  hom : C.ring →ₐ[R] D.ring
  localHom : IsLocalHom hom
  marked : ∀ c : C.ring,
    D.residueEquiv (IsLocalRing.residue D.ring (hom c)) =
      C.residueEquiv (IsLocalRing.residue C.ring c)
  atLevel : ∀ n : ℕ, LocalMap C (levelTest D n)
  atLevel_hom : ∀ n : ℕ,
    (atLevel n).hom =
      (Ideal.Quotient.mkₐ R (IsLocalRing.maximalIdeal D.ring ^ (n + 1))).comp hom
  atLevel_comm : ∀ {m n : ℕ} (h : n ≤ m),
    (map (levelMap D h)).comp (atLevel m).hom = (atLevel n).hom
  app : ∀ n : ℕ, evaluate ξ (atLevel n) ≅ η.obj n
  comm : ∀ {m n : ℕ} (h : n ≤ m),
    (push F (levelMap D h)).map (app m).hom ≫ (η.transition h).hom =
      (evaluationRestriction ξ (levelMap D h) (atLevel n) (atLevel m)
        (atLevel_comm h)).hom ≫ (app n).hom

/-- A versal formal object maps to every formal object, over a local
residue-preserving R-algebra homomorphism.
Source: Stacks Project, Formal Deformation Theory, Tag 06HT
(blueprint: lem-sfb-versal-formal-object-quasi-initial).

Proof (the node's five steps):
1. Put D_n = D/m_D^(n+1). The Noetherian-local Artinian-quotient criterion
   `lem-weil-pbc-noetherian-local-quotient-artinian-local` makes these test algebras;
   their quotient maps are surjective and preserve the specified residue field.
2. Begin at the residue field using C → k ≅ D/m_D. The predeformation condition
   supplies the unique isomorphism between the evaluated source and the target.
3. Recursively apply `IsVersal` to D_(n+1) → D_n and the target's transition,
   retaining the specified isomorphism at level n. Invert the lifted isomorphism
   to get source-to-target isomorphisms compatible with all adjacent transitions.
4. The compatible algebra maps C → D_n define a map C → D by maximal-ideal
   completeness (`def-weil-pbc-adic-completion`). Ring operations and R-linearity
   are checked on each quotient. Its residue map is the identity; the inverse
   image of m_D is therefore m_C, proving locality.
5. The maps to the truncations are exactly the reductions of this ring map.
   The recursive isomorphisms give `app`. Their adjacent compatibility and the
   pseudofunctor associativity imply `comm` for every pair of levels, with the
   fixed evaluation comparisons from `def-sfb-artin-deformation-test-category`.
-/
theorem exists_formalObjectMap_of_isVersal
    (F : CofibredGroupoids.{u, v, w} R k) (hpre : IsPredeformation F)
    (C : CompleteLocalAlgebra R k) (ξ : FormalObject F C) (hξ : IsVersal ξ)
    (D : CompleteLocalAlgebra R k) (η : FormalObject F D) :
    Nonempty (FormalObjectMap ξ η) := by
  sorry

end AlgebraicGeometry.ArtinDeformation
