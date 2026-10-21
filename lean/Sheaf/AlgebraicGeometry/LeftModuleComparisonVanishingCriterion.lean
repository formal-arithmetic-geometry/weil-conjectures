/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Objectwise derived evaluation detects comparison direct-image vanishing

Source: Stacks Project, Tag 099V (lemma-relative-comparison), first paragraph,
and Tag 03DA (lemma-abelian)
(blueprint: lem-pe-left-module-comparison-vanishing-criterion).

We use fixed-ring module-valued sheaves, the scalar-action encoding of modules over
`(constantSheaf J RingCat).obj (RingCat.of Λ)`. A constant-ring section acts locally
by its scalar representatives; conversely restriction to constant scalars recovers
this fixed-ring action. Neither construction needs commutativity. The comparison
is the existing restriction along `Scheme.toProEt X`, retaining these actions.
Derived abelian evaluation below is derived in the module-sheaf category: forgetting
scalars occurs inside the functor to which `rightDerived` is applied.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- If positive derived abelian evaluation vanishes at every etale object, the
comparison higher direct image vanishes as a module sheaf. The coefficient ring is
associative and unital, with no finiteness or commutativity assumption. The module
sheaf is arbitrary, and need not be an inverse image or injective.

Source: Stacks Project, Tag 099V (lemma-relative-comparison), first paragraph;
Tag 03DA (lemma-abelian)
(blueprint: lem-pe-left-module-comparison-vanishing-criterion).

Proof:
1. The module category is Grothendieck by lem-weil-pbc-ring-sheaves-grothendieck
and has enough injectives by lem-sp-grothendieck-enough-injectives. Embed M into an
injective, then successively embed the cokernels into injectives. Quotient maps
followed by these embeddings give an injective resolution I in nonnegative degrees.
2. Apply comparison direct image to I, giving J. By def-sp-left-exact-additive,
its q-th cohomology is R^q nu_* M. The same resolution computes derived abelian
evaluation. Since direct image is restriction, J(W) = I(W), including differentials.
Thus the hypothesis gives zero q-th cohomology of J(W) for every etale W.
3. Kernels of module sheaves are sectionwise by def-weil-sheaf-of-modules-category.
Put Z = ker(d^q). The preceding differential factors through Z. The sectionwise
cohomology vanishing says that J^(q-1)(W) -> Z(W) is surjective for every W.
Positivity of q puts this preceding degree in the nonnegative resolution.
4. A sectionwise surjection is an epimorphism: two maps out of Z agreeing after
it agree on every section, hence agree. Its cokernel, the q-th cohomology module
sheaf of J, is therefore zero. This is the asserted higher direct image. -/
theorem isZero_rightDerived_comparisonLowerStar_of_evaluation
    (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (q : ℕ) (hq : 0 < q)
    (h : ∀ W : X.Etale,
      IsZero (((sheafToPresheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⋙
        (evaluation X.ProEtᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op ((Scheme.toProEt X).obj W)) ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).rightDerived q).obj M)) :
    IsZero (((comparisonLowerStar (ModuleCat.{u + 1} Λ) X).rightDerived q).obj M) := by
  sorry

end AlgebraicGeometry.ProEtale
