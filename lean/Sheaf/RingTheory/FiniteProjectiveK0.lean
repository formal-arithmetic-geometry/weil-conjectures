/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q112
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Presentation.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Quot

/-!
# The Grothendieck group of finite projective modules

Source: Stacks Project, More on Algebra, Section Determinants, the recall immediately
before Tag 0AFX; Algebra, Tag 00JC (blueprint: def-trf-k0-group).

The generators form a set: projective quotients of finite free modules, modulo linear
isomorphism. Direct sum is represented using the standard coordinate decomposition of
`S^(n + m)`. The integer-module presentation imposes exactly the direct-sum relations.
-/

-- Q15 stage-2 delivery revalidates the recorded statement against the current DAG.

@[expose] public noncomputable section

universe u v

namespace Module

namespace FiniteProjectiveK0

variable (S : Type u) [CommRing S]

/-- A projective quotient of a finite free module, as in the set-sized construction of
Stacks Tag 00JC (blueprint: def-trf-k0-group). Finiteness follows from being such a quotient. -/
structure Presentation where
  /-- The number of coordinates in the finite free module (Stacks Tag 00JC). -/
  n : ℕ
  /-- The submodule by which to quotient (Stacks Tag 00JC). -/
  relations : Submodule S (Fin n → S)
  /-- The quotient is projective (Stacks Tag 00JC). -/
  projective : Module.Projective S ((Fin n → S) ⧸ relations)

attribute [instance] Presentation.projective

/-- The quotient module of a presentation (Stacks Tag 00JC;
blueprint: def-trf-k0-group). -/
abbrev Presentation.Carrier (P : Presentation S) : Type u :=
  (Fin P.n → S) ⧸ P.relations

/-- The set `I_S` of isomorphism classes of projective finite-free quotients.
`Quot` identifies presentations exactly under linear isomorphism, an equivalence relation.
Source: Stacks Tag 00JC (blueprint: def-trf-k0-group). -/
def Classes : Type u :=
  Quot (fun P Q : Presentation S ↦ Nonempty (P.Carrier ≃ₗ[S] Q.Carrier))

/-- The standard decomposition of coordinates in `S^(n+m)` into `S^n × S^m`.
Source: the direct-sum presentation before Stacks Tag 0AFX (blueprint: def-trf-k0-group). -/
def coordinates (n m : ℕ) : (Fin (n + m) → S) ≃ₗ[S] (Fin n → S) × (Fin m → S) :=
  (LinearEquiv.piCongrLeft' S (fun _ : Fin (n + m) ↦ S) finSumFinEquiv.symm).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) S S)

/-- The coordinatewise quotient onto the direct sum of two quotient modules.
Its kernel is `N ⊕ N'` under `coordinates`.
Source: the recall before Stacks Tag 0AFX (blueprint: def-trf-k0-group). -/
def sumMap (P Q : Presentation S) :
    (Fin (P.n + Q.n) → S) →ₗ[S] P.Carrier × Q.Carrier :=
  (P.relations.mkQ.prodMap Q.relations.mkQ).comp (coordinates S P.n Q.n).toLinearMap

/-- The first-isomorphism equivalence for the direct-sum quotient: the quotient by
`N ⊕ N'` is the direct sum of the two quotients. Source: the recall before Stacks Tag 0AFX
(blueprint: def-trf-k0-group). -/
def sumEquiv (P Q : Presentation S) :
    ((Fin (P.n + Q.n) → S) ⧸ LinearMap.ker (sumMap S P Q)) ≃ₗ[S]
      P.Carrier × Q.Carrier :=
  LinearMap.quotKerEquivOfSurjective (sumMap S P Q)
    ((Prod.map_surjective.mpr
      ⟨P.relations.mkQ_surjective, Q.relations.mkQ_surjective⟩).comp
        (coordinates S P.n Q.n).surjective)

/-- The projective quotient presentation of a direct sum, using `n+m` coordinates and
`N ⊕ N'`. Projectivity is transported from the product of the projective quotients.
Source: the recall before Stacks Tag 0AFX (blueprint: def-trf-k0-group). -/
def sumPresentation (P Q : Presentation S) : Presentation S :=
  ⟨P.n + Q.n, LinearMap.ker (sumMap S P Q),
    Module.Projective.of_equiv' (sumEquiv S P Q).symm⟩

/-- Direct sum on isomorphism classes, formed from quotient representatives. Different
representatives give isomorphic direct sums and thus the same class; `Quot.out` only selects
representatives of the already specified classes.
Source: the recall before Stacks Tag 0AFX (blueprint: def-trf-k0-group). -/
def sumClass (a b : Classes S) : Classes S :=
  Quot.mk _ (sumPresentation S a.out b.out)

open Classical in
/-- The abelian-group presentation with generators `I_S` and relations
`e_a + e_b - e_(a⊕b)` indexed by `I_S × I_S`.
Source: the recall before Stacks Tag 0AFX (blueprint: def-trf-k0-group). -/
def relations : Module.Relations ℤ where
  G := Classes S
  R := Classes S × Classes S
  relation p := Finsupp.single p.1 1 + Finsupp.single p.2 1 -
    Finsupp.single (sumClass S p.1 p.2) 1

/-- The projective finite-free quotient representing a finite projective module `M`,
in any universe. Mathlib supplies its genuine quotient construction and linear equivalence;
only the representative is chosen, and its isomorphism class is prescribed by `M`.
Source: Stacks Tag 00JC (blueprint: def-trf-k0-group). -/
def presentationOf (M : Type v) [AddCommGroup M] [Module S M]
    [Module.Finite S M] [Module.Projective S M] : Presentation S :=
  ⟨(Module.Finite.exists_fin' S M).choose, Module.Finite.kerRepr S M,
    Module.Projective.of_equiv' (Module.Finite.reprEquiv S M).symm⟩

end FiniteProjectiveK0

/-- The Grothendieck abelian group `K₀(S)` of finite projective modules over a commutative
ring `S`: the free abelian group on their set of isomorphism classes, modulo precisely
`[P] + [Q] = [P ⊕ Q]`. Source: Stacks Project, recall immediately before Tag 0AFX and
Algebra Tag 00JC (blueprint: def-trf-k0-group). -/
def FiniteProjectiveK0 (S : Type u) [CommRing S] : Type u :=
  (FiniteProjectiveK0.relations S).Quotient
  deriving AddCommGroup

namespace FiniteProjectiveK0

variable (S : Type u) [CommRing S]

open Classical in
/-- The class `[M]` of any finite projective module, the coset of its isomorphism-class
 generator in the presented group. Source: Stacks Tag 00JC and the recall before Tag 0AFX
(blueprint: def-trf-k0-group). -/
def mk (M : Type v) [AddCommGroup M] [Module S M]
    [Module.Finite S M] [Module.Projective S M] : Module.FiniteProjectiveK0 S :=
  (relations S).toQuotient (Finsupp.single (Quot.mk _ (presentationOf S M)) 1)

end FiniteProjectiveK0

end Module
