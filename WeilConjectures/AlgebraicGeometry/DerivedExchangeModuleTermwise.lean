/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedExactMate

/-!
# The unbounded module exchange on K-injective representatives

Source: Stacks Project, sites-cohomology.tex, Tags 0736 and 07A7; derived.tex,
Tags 070I, 070K and 0DVC. Blueprint main-20261015, sk-def-exchange, final paragraph.
(auxiliary; not a blueprint node).

The comparison below is the agent-formulated unbounded representative statement,
using the exact inverse-image mate of `def-kun-unbounded-exchange`.
The three auxiliary definitions spell out its canonical maps, without additional choices.
-/

@[expose] public section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar lowerStar squareUpperStarIso
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit Functor.rightDerivedFunctorUnitQ
  Functor.rightDerivedFunctorObjQIso
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso

private theorem square_factors
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    (G : C ⥤ C') (L : C ⥤ D) (L' : C' ⥤ D') (H : D ⥤ D')
    [G.Additive] [L.Additive] [L'.Additive] [H.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    [CategoryTheory.Limits.PreservesFiniteLimits L]
    [CategoryTheory.Limits.PreservesFiniteColimits L]
    [CategoryTheory.Limits.PreservesFiniteLimits L']
    [CategoryTheory.Limits.PreservesFiniteColimits L']
    [CategoryTheory.Limits.PreservesFiniteLimits H]
    [CategoryTheory.Limits.PreservesFiniteColimits H]
    (e : G ⋙ L' ≅ L ⋙ H) (N : HomotopyCategory C (.up ℤ)) :
    ((Functor.mapDerivedCategoryCompIso G L').inv ≫
      (Functor.mapDerivedCategoryNatIso e).hom ≫
      (Functor.mapDerivedCategoryCompIso L H).hom).app (DerivedCategory.Qh.obj N) ≫
      H.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app N) ≫
      H.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj N) =
    L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app N) ≫
      L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj N) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app N) := by
  have h₁ := Functor.mapDerivedCategoryCompIso_hom_app_factorsh G L' N
  have h₂ := Functor.mapDerivedCategoryCompIso_hom_app_factorsh L H N
  have h₃ := Functor.mapDerivedCategoryNatIso_fach e N
  simp only [NatTrans.comp_app, Category.assoc]
  erw [h₂, h₃, ← h₁]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]

/-- The exact derived adjunction mate satisfies the right-derived unit identity on complexes.
Source: Stacks Project, derived.tex, Tag 0DVC; exact-derived mate factorization
(auxiliary; not a blueprint node). -/
/-- The canonical direct-image comparison on a specified K-injective representative:
`Q(u_*I) ≅ Ru_*(QI) ≅ Ru_*K`, with the second arrow induced by `s.symm`.
Source: Stacks Project, derived.tex, Tags 070K and 070Y
(auxiliary; not a blueprint node). -/
/-- The isomorphism `t = g'⁻¹(s) ≫ φ ≫ Q(j)` associated to the replacement `j`.
Source: Stacks Project, sites-cohomology.tex, Tag 07A7, and derived.tex, Tag 070I
(auxiliary; not a blueprint node). -/
/-- The complex map `e = Ex⁰_I ≫ f'_*(j)`, using the termwise module mate.
Naturality of the sheaf mate supplies the chain-map condition in every degree.
Source: Stacks Project, sites-cohomology.tex, Tags 0736 and 07A7
(auxiliary; not a blueprint node). -/
/-- The specified unbounded module exchange is computed on any K-injective representative
and any K-injective replacement of its inverse image. The two sides are respectively
`σsrc ≫ Ex_K` and `Q(e) ≫ χ_(J,t)`, with `χ_(I,s)`, `t`, and `e` explicitly defined above.
Consequently conjugating `Q(e)` by the displayed comparison isomorphisms always yields
this fixed exchange mate. This includes bounded below injective representatives, and
requires no K-injectivity of the inverse image of `I`.

Source: Stacks Project, sites-cohomology.tex, Tags 0736 and 07A7; derived.tex,
Tags 070I, 070K, 08BJ and 0DVC; blueprint main-20261015, sk-def-exchange, final paragraph
(auxiliary; not a blueprint node).

Proof: the composition and natural-isomorphism factorization identities normalize the
exact derived inverse-image square. Apply the general exact-derived mate identity on
homotopy complexes and identify its factors with the complex-level comparisons.
Naturality in `s.inv` transports this identity from `Q(I)` to `K`. Naturality of the
right-derived unit along `j`, and cancellation in the explicit definition of `t`,
identify the resulting right side with `Q(e) ≫ χ_(J,t)`. -/
end AlgebraicGeometry.Etale
