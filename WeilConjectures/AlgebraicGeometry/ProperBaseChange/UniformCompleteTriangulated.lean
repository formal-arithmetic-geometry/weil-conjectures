/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
import all WeilConjectures.AlgebraicGeometry.Standard.StandardQuotientsPerfectSupplement
import WeilConjectures.AlgebraicGeometry.Pbc.PbcPrincipalUniformReductionCriterion

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

private theorem uniformizer_ne_zero_local (l : ℕ) [Fact l.Prime] (E : Type (u + 1))
    [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Padic.coefficientExtensionUniformizer l E ≠ 0 := by
  let h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hm : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
    h.2.2.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  intro h0
  apply hm
  rw [← hgen, h0, Ideal.span_singleton_eq_bot]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
  let d := pbcPadicCoefficientDatum l E
  obtain ⟨F, η, hAdd, hShift, hExact, hUnitShift, hComplete⟩ := pbcExactCompletionData T d
  have := hAdd
  let := hShift
  have := hExact
  have := hUnitShift
  have hCompleteEq : PbcIsIntrinsicallyComplete T d = fun K ↦ IsIso (η.app K) := by
    funext K
    exact propext (hComplete K)
  have hc : ObjectProperty.IsClosedUnderIsomorphisms (PbcIsIntrinsicallyComplete T d) ∧
      ObjectProperty.IsTriangulated (PbcIsIntrinsicallyComplete T d) := by
    rw [hCompleteEq]
    exact exactUnitLocus F η
  have := hc.1
  have := hc.2
  have hred (n : ℕ) : ∃ (_ : (pbcCompletedReduction T d n).CommShift ℤ),
      (pbcCompletedReduction T d n).IsTriangulated :=
    (reductionDerivedExistence T (pbcAdicProjection T d n)).choose_spec.choose_spec.2.1
  let (n : ℕ) : (pbcCompletedReduction T d n).CommShift ℤ := (hred n).choose
  let (n : ℕ) : (pbcCompletedReduction T d n).IsTriangulated := (hred n).choose_spec
  let (n : ℕ) : (pbcDerivedRestrict (pbcLevelConstantComparison T d n).hom).CommShift ℤ := by
    dsimp [pbcDerivedRestrict]
    infer_instance
  let (n : ℕ) : (pbcDerivedRestrict (pbcLevelConstantComparison T d n).hom).IsTriangulated := by
    dsimp [pbcDerivedRestrict]
    infer_instance
  let : ∀ n : ℕ, (pbcConstantReduction T d n).CommShift ℤ := fun n ↦ by
    dsimp [pbcConstantReduction]
    infer_instance
  let : ∀ n : ℕ, (pbcConstantReduction T d n).IsTriangulated := fun n ↦ by
    dsimp [pbcConstantReduction]
    infer_instance
  let Q (n : ℕ) := DerivedCategory.homologyProperty
    (@IsConstructibleProEtaleCoefficientModuleSheaf T (ProEtale.PbcQuotient d n) _
      (d.quotientFinite n))
  let (n : ℕ) : (Q n).IsClosedUnderIsomorphisms :=
    (constructibleCoefficientHomology_isTriangulated T (ProEtale.PbcQuotient d n)).1
  let (n : ℕ) : (Q n).IsTriangulated :=
    (constructibleCoefficientHomology_isTriangulated T (ProEtale.PbcQuotient d n)).2
  have hp := uniformProfileLocus
    (fun n : ℕ ↦ DerivedCategory
      (pbcModules T (adicLisseConstantRing T (ProEtale.PbcQuotient d n))))
    (pbcConstantReduction T d) (fun _ ↦ DerivedCategory.TStructure.t) Q
  change ObjectProperty.IsClosedUnderIsomorphisms (PbcUniformReductionProfile T d) ∧
    ObjectProperty.IsTriangulated (PbcUniformReductionProfile T d) at hp
  have := hp.1
  have := hp.2
  have hPredicate : PbcIsBoundedConstructibleComplete T d =
      (PbcIsIntrinsicallyComplete T d ⊓ PbcUniformReductionProfile T d) := by
    funext K
    exact propext (and_congr_right (fun _ ↦ pbcPrincipalUniformReductionCriterion T d
      (Padic.coefficientExtensionUniformizer l E) rfl
      (uniformizer_ne_zero_local l E) K))
  change ObjectProperty.IsClosedUnderIsomorphisms (PbcIsBoundedConstructibleComplete T d) ∧
    ObjectProperty.IsTriangulated (PbcIsBoundedConstructibleComplete T d)
  rw [hPredicate]
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
