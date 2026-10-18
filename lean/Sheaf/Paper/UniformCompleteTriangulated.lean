/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Paper.BoundedConstructibleTower
import Sheaf.Paper.IntrinsicCompletionCompleted
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Paper.ProEtaleConstructibleSheaf
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback


/-!
# Triangulation of the compatible uniformly constructible complete category

Source: Weil blueprint, proper base change, cor-weil-pbc-constructible-complete,
restriction to ordinary triangulated functors; agent supplement
(blueprint: lem-weil-pbc-uniform-complete-triangulated).

The predicate retains intrinsic completion, common bounded adic-lisse local models,
and compatible etale origins over the actual completed coefficient sheaf.
Mathlib's full-subcategory instances give the inherited triangulation and exact inclusion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The compatible uniform complete objects form a strictly full triangulated subcategory.
Source: Weil blueprint, cor-weil-pbc-constructible-complete, constructible restriction;
agent supplement (blueprint: lem-weil-pbc-uniform-complete-triangulated).

Proof:
1. The specified Koszul completion and its unit are functorial: finite free tensor
preserves quasi-isomorphisms, and exact countable products preserve acyclic complexes
(lem-weil-proetale-countable-products-exact). The equation product(f)(1-s)=(1-s')product(f)
gives naturality. Transport the normalized reduction and witness isomorphisms along an
ambient isomorphism. Zero has zero local models and etale origins; use the empty partition
on the empty scheme. This proves zero membership and isomorphism closure.
2. The nonzero uniformizer gives the length-one free resolution of A/I^n. Exact constant
sheaves and lem-weil-pbc-constant-completion-equivalence give the corresponding resolution
of the quotient sheaf over A_T. Inverse image preserves it on local covering members.
A local model with terms in [d0,d1] therefore has reductions in [d0-1,d1], with finite
lisse cohomology. Etale witnesses, finite-level comparison, comparison-pullback and
geometric stalk conservativity give the same global bounds for every quotient.
3. Exact coefficient reduction commutes with every integer shift. Shift local models,
normalizations and witnesses. The Koszul mapping-fiber comparison multiplies the second
coordinate by (-1)^m; its differential and unit show that completeness is shift-stable.
4. For any ambient distinguished triangle K to L to C to K[1], Koszul completion is
exact. Tensor and products distribute over the two cone summands; on mapping fibers
((l,k),(l',k')) maps to ((l,l'),(k,-k')). This is a chain isomorphism, compatible with
the unit. The two-isomorphism lemma (lem-sf-triangle-morphism-iso) proves completeness of C.
5. Exact reduction and lem-weil-proetale-dbc-triangulated give constructible cohomology
for C_n. The long exact sequence bounds it in [a-1,b], for one interval [a,b] bounding
both input towers. The canonical reduction tower retains its quotient normalization
and cocycle (def-weil-pbc-adic-coefficient-datum).
6. Bounded-below finite-level comparison lifts the arbitrary ambient morphisms uniquely
to the retained etale origins. Cone triangles give bounded-below origins of C_n and their
comparison isomorphisms, by exact inverse image, TR3 and the two-isomorphism lemma.
Tensor-pullback comparison identifies reductions of these origins with C_a. Exact inverse
image detects zero cohomology, so these reductions are bounded below before full
faithfulness is applied. Lift the normalizations and their inverses uniquely. Faithfulness
and the quotient cocycle give the compatibility equation and all three-index cocycles;
no functorial choice of cones is assumed (thm-weil-pbc-site-comparison).
7. Apply lem-weil-pbc-normalized-constructible-local-effectivity to the normalized tower
with the single bound [a-1,b]. It supplies the common finite stratification, pro-etale
covers, bounded adic-lisse finite-type local complexes and compatible reduction maps.
Together with steps 4 and 6 this gives all three membership clauses for every cone.
8. Rotate and shift to obtain every two-of-three triangle closure, including the
middle-vertex criterion. The cone of zero K[-1] to L gives L plus K, so finite biproducts
and zero are inherited. Apply def-weil-triangulated-subcategory: the full subcategory
inherits shifts and precisely the ambient distinguished triangles, is triangulated,
and its inclusion is exact with its identity shift comparison. -/
theorem pbcUniformComplete_isTriangulated
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [IsNoetherian T] (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (_hl : IsUnit (l : Γ(T, ⊤))) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsPbcBoundedConstructibleComplete T l E) ∧
      ObjectProperty.IsTriangulated (IsPbcBoundedConstructibleComplete T l E) := by
  sorry

end AlgebraicGeometry.Scheme
