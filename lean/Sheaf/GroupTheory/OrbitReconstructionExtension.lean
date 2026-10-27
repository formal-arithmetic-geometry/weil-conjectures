/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.GroupTheory.OpenOrbitFunctor
public import Sheaf.CategoryTheory.Galois.AutProfinite
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Extension of orbit reconstruction to discrete continuous actions

Source: Bhatt--Scholze, Proposition 7.1.5, printed p. 64, injectivity paragraph.
(blueprint: lem-sfb-orbit-reconstruction-extension)
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory

namespace TopologicalGroup

/-- Bijective reconstruction on open orbits extends to all discrete continuous actions.
The homomorphism `Φ` is specified by its translation formula. The equivalence `r` is actual
restriction. For each point, `U` is exactly its stabilizer, and `q` is the equivariant map
specified on every coset by `h U ↦ h s`. Its evaluation formula describes the inverse of
restriction and exhibits every extension coordinate as a continuous composite.

Source: Bhatt--Scholze, Proposition 7.1.5, printed p. 64, injectivity paragraph.
(blueprint: lem-sfb-orbit-reconstruction-extension)

Proof:
1. Restriction is left whiskering by the full orbit inclusion, so naturality and the group
   laws hold componentwise (`def-sfb-open-orbit-functor`).
2. The stabilizer of `s` is a subgroup and is open, being the inverse image of the open
   singleton `{s}` under the continuous orbit map. The formula `h U ↦ h s` is well-defined
   since equal cosets differ by an element fixing `s`; it is equivariant and sends `U` to `s`.
3. Translation by `g` defines a natural automorphism on every action, inverse to translation
   by `g⁻¹`; equivariance of every arrow proves naturality. These translations multiply as
   the elements of `G` do, and restriction of translation by `g` equals `Φ g`.
4. Bijectivity of `Φ` therefore defines a multiplicative right inverse to restriction:
   extend `α = Φ g` by translation by its unique `g`.
5. Naturality at the arrow `q` gives `β_S(s) = q ((r β)_U(U))`. Thus restriction is injective,
   the right inverse is also a left inverse, and its coordinate and translation formulas hold.
6. In the pointwise topology (`def-sfb-set-functor-aut-pointwise-topology`), multiplication
   is continuous by prescribing two evaluations: at `s` for the second factor and at its
   image for the first. For inversion, prescribe the value at the inverse image of `s`.
   Finite intersections prove that both automorphism groups are topological groups.
7. Restriction is continuous because each of its coordinate evaluations is an evaluation
   on the corresponding orbit in the full action category.
8. The inverse's coordinate at `s` factors as evaluation at `U` followed by the map `q`
   between discrete sets. The inverse image of a value is a union of orbit-coordinate
   neighbourhoods. Finite intersections prove continuity of the inverse.
-/
theorem orbitReconstruction_extension
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Φ : G →* Aut (openOrbitForget G))
    (hΦ : ∀ (g : G) (U : OpenOrbitCategory G) (x : G ⧸ U.toSubgroup),
      ((Φ g).hom.app U) x = g • x)
    (hbij : Function.Bijective Φ) :
    IsTopologicalGroup (Aut (discreteActionForget G)) ∧
      IsTopologicalGroup (Aut (openOrbitForget G)) ∧
      ∃ r : Aut (discreteActionForget G) ≃ₜ* Aut (openOrbitForget G),
        (∀ β : Aut (discreteActionForget G),
          r β = (((Functor.whiskeringLeft (OpenOrbitCategory G)
            (DiscreteContAction TopCat.{u} G) (Type u)).obj
              (openOrbitInclusion G)).mapAut (discreteActionForget G) β)) ∧
        (∀ (g : G) (S : DiscreteContAction TopCat.{u} G)
            (s : (discreteActionForget G).obj S),
          ((r.symm (Φ g)).hom.app S) s = (S.obj.obj.ρ g).hom s) ∧
        (∀ (S : DiscreteContAction TopCat.{u} G) (s : (discreteActionForget G).obj S),
          ∃ U : OpenSubgroup G, ∃ q : openOrbitAction G U ⟶ S,
            (∀ h : G, h ∈ U ↔ (S.obj.obj.ρ h).hom s = s) ∧
            (∀ h : G, (discreteActionForget G).map q (QuotientGroup.mk h) =
              (S.obj.obj.ρ h).hom s) ∧
            (∀ α : Aut (openOrbitForget G),
              ((r.symm α).hom.app S) s =
                (discreteActionForget G).map q (α.hom.app U (QuotientGroup.mk 1))) ∧
            @Continuous (Aut (openOrbitForget G)) S.obj.obj.V
              (SetFunctorAut.functorTopology (openOrbitForget G)) S.obj.obj.V.str
              (fun α ↦ (discreteActionForget G).map q
                (α.hom.app U (QuotientGroup.mk 1)))) := by
  sorry

end TopologicalGroup
