/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Sheaf.CategoryTheory.SiteCechComplex

/-!
# The cocycle lifting step for injective module presheaves

Source: Stacks Project, Cohomology on Sites, proof of Tag 03FC after Tag 03FB,
using Tags 03AS, 03F5 and 03AT. No topology or covering condition enters this step.
-/

@[expose] public section

universe u v w r s

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Every positive-degree cocycle with values in an injective module presheaf is a
coboundary. Unlike the ringed-site theorem, this concerns presheaf injectivity and
an arbitrary family admitting the specified fibre products, without sheafification.
Source: Stacks Project, Cohomology on Sites, proof of Tag 03FC after the application
of Tag 03FB; Tags 03AS, 03F5 and 03AT.
(blueprint: lem-weil-pbc-injective-presheaf-module-cech-cocycle-lift)

Proof: form the chain complex K of coproducts of free representable R-module
presheaves on the chosen products. Its boundary deletes factors with alternating
signs. At each object W, group its basis by the composite W -> U. The universal
property identifies each group with tuples in the set of lifts of that composite.
The empty lift set gives zero; inserting a chosen lift contracts every nonempty
summand in positive degrees. Hence K is exact there (03F5 and 03AT).
Free Yoneda and the coproduct universal property identify maps K_n -> M with
cochains of M.presheaf (03AS). Precomposition by the boundary is exactly
`differentialValue`: Yoneda sends each deletion projection to its restriction map.
A cocycle in degree q+1 is thus a map K_(q+1) -> M killing the incoming boundary.
Exactness factors it through the image of K_(q+1) -> K_q. Injectivity extends
that map along the image inclusion into K_q. The resulting map K_q -> M
corresponds to the desired cochain b, and its precomposition is the original
cocycle. This argument includes q=0, since exactness is used at q+1, not at q. -/
-- STATEMENT-DISPUTED: independent universes permit small-valued injective presheaves
-- on Type 1 with nonzero Cech H^1 for the three edges of a triangle. See report.md.
-- The free representables used in the planned proof need not lie in PMod.{s} R.
theorem injective_presheaf_module_cech_cocycle_lift
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{r})
    (M : PresheafOfModules.{s} R) [Injective M]
    {T : Type w} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (S : SiteCechComplex f hom) (q : ℕ)
    (c : S.cochains M.presheaf (q + 1))
    (hc : S.differentialValue M.presheaf (q + 1) c = 0) :
    ∃ b : S.cochains M.presheaf q, S.differentialValue M.presheaf q b = c := by
  sorry

end CategoryTheory
