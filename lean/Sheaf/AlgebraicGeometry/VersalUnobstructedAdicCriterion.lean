module

public import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory
public import WeilConjectures.RingTheory.FormallySmoothAdic
import Sheaf.RingTheory.AdicSmoothFixedResidueLifting

/-! # Versal formal objects detect unobstructedness

Source: Stacks Project, Formal Deformation Theory, Tag 0DZK,
lemma-smooth-power-series-classical, equivalence (1) and (2); Tags 06GC, 06GS and 06HR
(blueprint: lem-sfb-versal-unobstructed-adic-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

/-- A predeformation category with a versal formal object is unobstructed precisely when
its complete local base algebra is formally smooth for its maximal-ideal-adic topology.
Here unobstructedness means lifting every object, up to isomorphism, across every
surjection of marked Artinian local test algebras.

Source: Stacks Project, Formal Deformation Theory, Tag 0DZK, (1) iff (2), with
Tags 06GC, 06GS and 06HR.
(blueprint: lem-sfb-versal-unobstructed-adic-criterion)

Proof: First every object eta over A is induced by a marked local map C -> A.
The marked residue map C -> k is continuous. The predeformation condition gives
an isomorphism between eta restricted to k and the evaluation of xi at this map.
Versality for A -> k supplies the desired map and isomorphism (the Artinian case
of Tag 06HT). Next, if F is unobstructed, lift the evaluation xi_u across any
surjection A' -> A. Apply versality to the resulting lift and its specified
isomorphism to obtain a local marked lift u' of u. Local maps to Artinian rings
are continuous by nilpotence of the target maximal ideal. The reverse implication
of lem-sfb-adic-smooth-fixed-residue-lifting now gives adic formal smoothness.
Conversely, represent eta by xi_u using the first step. Adic formal smoothness
and lem-sfb-adic-smooth-fixed-residue-lifting lift u to u'. Take xi_{u'} as the
lift of eta; evaluationRestriction, built from the transition isomorphisms and
the pseudofunctor composition constraints, gives the required special-fibre
isomorphism. No uniqueness or algebraization is asserted. -/
theorem unobstructed_iff_formallySmoothAdic_of_versal
    (R k : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field k] [Algebra R k] [Algebra (IsLocalRing.ResidueField R) k]
    [IsScalarTower R (IsLocalRing.ResidueField R) k]
    [Module.Finite R k]
    (F : CofibredGroupoids.{u, v, w} R k) (hF : IsPredeformation F)
    (C : CompleteLocalAlgebra R k) (ξ : FormalObject F C) (hξ : IsVersal ξ) :
    (∀ (A' A : TestCategory R k) (p : A' ⟶ A), Function.Surjective (map p) →
      ∀ η : fibre F A, ∃ η' : fibre F A', Nonempty ((push F p).obj η' ≅ η)) ↔
      Algebra.FormallySmoothAdic R C.ring (IsLocalRing.maximalIdeal C.ring) := by
  sorry

end AlgebraicGeometry.ArtinDeformation
