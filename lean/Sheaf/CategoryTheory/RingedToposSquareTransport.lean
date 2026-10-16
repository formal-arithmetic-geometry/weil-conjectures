/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.CategoryTheory.Equivalence
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
import Sheaf.CategoryTheory.Adjunction.FiniteProductRingFunctor

/-!
# Transporting a ringed geometric square across equivalences

Source: Stacks Project, Modules on Sites, Tag 03CR, ring-sheaf details in the proof
(blueprint: lem-weil-pbc-ringed-topos-square-transport).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Lift a fixed geometric square to transported commutative ring sheaves.

Source: Stacks Project, Modules on Sites, Tag 03CR, proof; Sites, Section 00YR
(blueprint: lem-weil-pbc-ringed-topos-square-transport).

Proof:
1. Choose g.inverse = G.inverse and e.inverse = E.inverse, with their equivalence
   adjunctions and direct functors G.functor and E.functor. These functors preserve
   finite products. Transport the operations of A and B through them, using inverse
   product comparisons for binary operations and the terminal comparison for zero
   and one. Ring equations are equations of maps from finite powers, so functoriality
   preserves them. The internal-ring/sheaf correspondence produces A', B', a and b.
   Set r_g = G.inverse.map a.hom followed by the G counit, and define r_e similarly.
   Naturality of the counits at the operation maps proves that r_g and r_e preserve
   ring operations. Both are isomorphisms because the equivalences' counits are.
2. Write t = f.inverse.map r_e followed by f.ringMap. The map
   alpha.inv.app B' followed by t followed by r_g.inv has source G.inverse(H(B'))
   and target G.inverse(A'). Full faithfulness of G.inverse lifts it uniquely to a
   map r_h : H(B') --> A'. Naturality of alpha with the projections and operation
   maps shows that alpha preserves transported operations. Thus its composite with
   t and r_g.inv preserves them; faithfulness of G.inverse reflects these equalities,
   proving all four ring-map fields for h. Set h.inverse = H, h.direct = R and
   h.adj = adjH. Multiplying the defining equation of r_h by alpha.hom and r_g gives
   exactly the last equation in the statement. No compatibility of alpha with adjH
   beyond the given natural isomorphism is needed for this construction.
3. For any of these adjunctions L dashv V with structural ring map r, and any module
   M, construct its direct image on the set sheaf V(M). Addition, zero and negation
   are V of the original operations, composed with inverse product comparisons.
   For scalar multiplication first take the adjunct s : B --> V(A) of r and use
   B times V(M) --(s,id)--> V(A) times V(M) --> V(A times M) --> V(M).
   Right adjoints preserve products, so all these comparisons are invertible.
   The adjunction's unit and counit commute with product projections; hence s
   preserves ring operations. This proves the module laws for the displayed action.
   Evaluate the operations on site objects: naturality makes restrictions linear,
   and the underlying set sheaf V(M) proves the sheaf condition. Apply V to module
   maps to obtain an additive functor with the required underlying natural isomorphism.
   Under the Hom adjunction, the above action sends (a,x) to r(L(a)) acting on
   the adjunct of x. Addition has the same compatibility by the product comparisons.
   Combining these two identities is precisely module_linear for z = a*x+y.
   Apply this construction to g, e and h to supply their module fields.
The rings and modules here are constructed from operations on specified set sheaves;
no arbitrary object is chosen from a bare existence assertion. All arguments use
finite products and remain valid for empty sites and zero rings. -/
theorem ringedTopos_squareTransport
    {C D C' D' : Type u}
    [SmallCategory C] [SmallCategory D] [SmallCategory C'] [SmallCategory D']
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {J' : GrothendieckTopology C'} {K' : GrothendieckTopology D'}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (G : Sheaf J (Type u) ≌ Sheaf J' (Type u))
    (E : Sheaf K (Type u) ≌ Sheaf K' (Type u))
    (H : Sheaf K' (Type u) ⥤ Sheaf J' (Type u))
    (R : Sheaf J' (Type u) ⥤ Sheaf K' (Type u))
    (adjH : H ⊣ R) (hH : PreservesFiniteLimits H)
    (α : E.inverse ⋙ f.inverse ≅ H ⋙ G.inverse) :
    ∃ (A' : Sheaf J' CommRingCat.{u}) (B' : Sheaf K' CommRingCat.{u})
      (g : RingedToposMorphism
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
        ((sheafCompose J' (forget₂ CommRingCat RingCat)).obj A'))
      (e : RingedToposMorphism
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)
        ((sheafCompose K' (forget₂ CommRingCat RingCat)).obj B'))
      (h : RingedToposMorphism
        ((sheafCompose J' (forget₂ CommRingCat RingCat)).obj A')
        ((sheafCompose K' (forget₂ CommRingCat RingCat)).obj B'))
      (a : (sheafCompose J' (forget CommRingCat)).obj A' ≅
        g.direct.obj ((sheafCompose J (forget CommRingCat)).obj A))
      (b : (sheafCompose K' (forget CommRingCat)).obj B' ≅
        e.direct.obj ((sheafCompose K (forget CommRingCat)).obj B))
      (alpha : e.inverse ⋙ f.inverse ≅ h.inverse ⋙ g.inverse),
      g.direct = G.functor ∧ e.direct = E.functor ∧ h.direct = R ∧
      g.ringMap = g.inverse.map a.hom ≫
        g.adj.counit.app ((sheafCompose J (forget CommRingCat)).obj A) ∧
      e.ringMap = e.inverse.map b.hom ≫
        e.adj.counit.app ((sheafCompose K (forget CommRingCat)).obj B) ∧
      f.inverse.map e.ringMap ≫ f.ringMap =
        alpha.hom.app ((sheafCompose K' (forget CommRingCat)).obj B') ≫
          g.inverse.map h.ringMap ≫ g.ringMap := by
  sorry

end CategoryTheory
