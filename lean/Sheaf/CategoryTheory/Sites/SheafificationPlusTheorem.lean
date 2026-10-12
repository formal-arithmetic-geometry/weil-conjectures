/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.SitePlusSeparated
import Sheaf.CategoryTheory.Sites.SitePlusConstructionPresheaf
import Sheaf.Paper.PlusConstructionFunctorial
import Sheaf.Paper.SitePlusOfSeparatedIsSheaf
import Sheaf.Paper.SitePlusOfSheafIso

/-!
# The plus construction computes sheafification

Source: Stacks Project, Sites, Theorem 00WB and Proposition 00WH.
(blueprint: lem-weil-pbc-sheafification-plus-theorem)
-/

@[expose] public section

universe u w

open CategoryTheory Opposite

namespace CategoryTheory.GrothendieckTopology

/-- The first plus is separated and injects into the double plus; the double plus is a sheaf
and has the universal property of sheafification. Any other sheafification is uniquely
isomorphic to it compatibly with the unit.

Source: Stacks Project, Sites, Theorem 00WB, Definition 00WG and Proposition 00WH.
(blueprint: lem-weil-pbc-sheafification-plus-theorem)

Proof, following the node's five steps:
1. Apply lem-weil-pbc-sheafification-plus-separated to P for separatedness of P-plus and
objectwise injectivity of its unit into P-double-plus.
2. Apply lem-weil-pbc-site-plus-of-separated-is-sheaf to P-plus. It is a presheaf by
lem-weil-pbc-site-plus-construction-presheaf, so its plus is a sheaf.
3. For a sheaf G, both G -> G-plus and G-plus -> G-double-plus are isomorphisms by
lem-weil-pbc-site-plus-of-sheaf-iso. The naturality from
lem-weil-pbc-site-plus-construction-functorial gives phi followed by the double unit equal
to the double unit followed by phi-double-plus. Compose phi-double-plus with the inverse
of the double unit of G to obtain the required factorization.
4. By lem-weil-pbc-site-plus-construction-presheaf, every section of P-double-plus locally
comes from P-plus, and each of these sections locally comes from P. Compose the two
coverings by the site composition axiom (def-weil-pbc-sites-and-cohomology). Two proposed
factorizations agree there because they agree on P. Since G is separated, they agree
on every section, hence as natural transformations.
5. The universal property of def-weil-pbc-sheafification gives maps in both directions
between P-double-plus and any other sheafification Q. Their composites agree with the
identities after the corresponding units, so uniqueness makes them identities. This gives
an isomorphism; uniqueness of the forward map gives uniqueness of the isomorphism.

The dependency's recorded `plusObj`/`toPlus` presentation is used throughout. The final
conjunct quantifies over any sheaf with the sheafification universal property, including
`presheafToSheaf` with its adjunction unit, without choosing a second sheafification. -/
theorem plus_sheafification_theorem
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (P : Cᵒᵖ ⥤ Type (max u w)) :
    (∀ (U : C) (E : Precoverage.ZeroHypercover.{max u w} J U)
      (s s' : (J.toGrothendieck.plusObj P).obj (op U)),
      (∀ i : E.I₀,
        (J.toGrothendieck.plusObj P).map (E.f i).op s =
          (J.toGrothendieck.plusObj P).map (E.f i).op s') → s = s') ∧
    (∀ U : C, Function.Injective
      ((J.toGrothendieck.toPlus (J.toGrothendieck.plusObj P)).app (op U))) ∧
    Presheaf.IsSheaf J.toGrothendieck
      (J.toGrothendieck.plusObj (J.toGrothendieck.plusObj P)) ∧
    (∀ (G : Sheaf J.toGrothendieck (Type (max u w))) (φ : P ⟶ G.obj),
      ∃! φ' : J.toGrothendieck.plusObj (J.toGrothendieck.plusObj P) ⟶ G.obj,
        (J.toGrothendieck.toPlus P ≫
          J.toGrothendieck.toPlus (J.toGrothendieck.plusObj P)) ≫ φ' = φ) ∧
    (∀ (Q : Sheaf J.toGrothendieck (Type (max u w))) (θ : P ⟶ Q.obj),
      (∀ (G : Sheaf J.toGrothendieck (Type (max u w))) (φ : P ⟶ G.obj),
        ∃! ψ : Q.obj ⟶ G.obj, θ ≫ ψ = φ) →
      ∃! e : J.toGrothendieck.plusObj (J.toGrothendieck.plusObj P) ≅ Q.obj,
        (J.toGrothendieck.toPlus P ≫
          J.toGrothendieck.toPlus (J.toGrothendieck.plusObj P)) ≫ e.hom = θ) := by
  sorry

end CategoryTheory.GrothendieckTopology
