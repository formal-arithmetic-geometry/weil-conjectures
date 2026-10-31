/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.Topology.ContinuousMapCondensedRingSupplement
public import WeilConjectures.SixFunctors.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.CategoryTheory.ConstantModuleFiniteTypeReflection
import WeilConjectures.Algebra.Homology.SingleConeKernel
import WeilConjectures.AlgebraicGeometry.ConstantKernelRealization
import WeilConjectures.RingTheory.NonFiniteMultiplicationKernel
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed

/-!
# Bounded constructible complexes and failure of cone closure for general coefficients

Source: latest Weil blueprint, `sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/`
`det-def-sfb-bounded-constructible.md` and its proof
(blueprint: det-def-sfb-bounded-constructible).

The imported `AlgebraicGeometry.ProEtale.boundedConstructible` and `BoundedConstructible`
are the required predicate and full category in the ordinary unbounded derived category.
`mem_boundedConstructible_iff` gives precisely bounded constructible cohomology. There is
no completeness condition. The three imported padic instances and the finite-discrete
instance give triangulatedness for exactly the four listed coefficient families on a
topologically Noetherian scheme. The additional assertion here records the final clause:
for general commutative ring objects this full subcategory need not be closed under cones.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Bounded constructible complexes need not be closed under cones for a general
commutative coefficient ring object, even with abelian-group coefficients.

Source: latest Weil blueprint, `det-def-sfb-bounded-constructible.md`, final sentence,
and `det-def-sfb-bounded-constructible.proof.md`
(blueprint: det-def-sfb-bounded-constructible).

Proof plan, following the four steps of this node:
1. Use the existing `boundedConstructible`, `BoundedConstructible` and
`mem_boundedConstructible_iff` from `def-sfb-bounded-constructible-complexes` and
`lem-sfb-bounded-constructible-iff`. Their ambient category is the ordinary unbounded
localization of integer cochain complexes, as in `det-def-sfb-derived-categories` and
`def-weil-abstract-derived-category`. Morphisms are the ambient morphisms.
2. The separate positive clause uses
`lem-sfb-bounded-constructible-triangulated-finiteness`: on a topologically Noetherian
scheme the E, integers-of-E, finite-subextension-valued algebraic closure, and finite
ell-primary coefficient categories are triangulated. This imposes no condition on the
general definition and is not used to establish the counterexample.
3. Take a field k and B = k[x,y_1,y_2,...]/(x*y_1,x*y_2,...). Every element is uniquely
f(x)+g(y_1,y_2,...), with g of zero constant term. Thus ann(x) is I = (y_1,y_2,...).
For m = (x,y_1,y_2,...), I/mI has all y_i as a linearly independent basis; hence I is
not finitely generated.
4. On X = Spec of an algebraic closure of k, use the constant commutative ring object
B_X and the cone triangle of x : B_X[0] --> B_X[0]. The additive exact constant
realization of `def-sfb-site-derived-constant-module-functor` gives cohomology I_X
in degree -1 and (B/xB)_X in degree 0, zero otherwise. Both vertices B_X[0] are bounded
constructible, since regular and zero modules have finite presentations
(`def-sfb-finitely-presented-module`). On this one-point reduced scheme every nonempty
stratum immersion is an isomorphism. Constructibility of I_X would therefore imply
local finite presentation (`def-sfb-constructible-module`, `def-sfb-locally-finitely-presented`),
hence local finite generation. The identity geometric point makes the topos nonempty.
By `lem-sfb-constant-module-finite-type-reflection` local finite generation of I_X would
make I finitely generated, contradicting step 3. Thus the third vertex fails the
bounded constructible predicate, while the first two satisfy it. The usual equivalence
between internal modules in abelian sheaves and sectionwise ring-sheaf modules identifies
the constant realization with these module objects and preserves the cone triangle. -/
theorem exists_distinguishedTriangle_not_boundedConstructible :
    ∃ (X : Scheme.{u})
      (R : CommMon (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}))
      (T : Pretriangulated.Triangle
        (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R.X))),
      T ∈ distTriang _ ∧ boundedConstructible R.X T.obj₁ ∧
        boundedConstructible R.X T.obj₂ ∧ ¬ boundedConstructible R.X T.obj₃ := by
  obtain ⟨X, R, M, N, f, hM, hN, hforce⟩ := exists_constant_kernel_realization
  obtain ⟨T, hT, h₁, h₂, ⟨e⟩⟩ := DerivedCategory.exists_single_cone_kernel f
  refine ⟨X, R, T, hT, ?_, ?_, ?_⟩
  · rw [h₁]
    exact hM
  · rw [h₂]
    exact hN
  · intro hT3
    have hC := (mem_boundedConstructible_iff R.X T.obj₃).1 hT3
    have hK := hC.2 (-1)
    exact hforce (IsConstructibleModuleObject.of_iso e hK)

end AlgebraicGeometry.ProEtale
