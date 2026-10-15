/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.CategoryTheory.ScalarLocalization
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Localization.Triangulated
import Sheaf.CategoryTheory.LinearScalarLocalization

/-! # Triangulation of scalar localization

Source: Stacks Project, Derived Categories, Tags 05R2 and 05R6, applied to the scalar
localization in the blueprint `sec-smooth-purity/sk-def-sf-operations`,
`def-weil-rationalization-karoubi`
(blueprint: lem-weil-linear-scalar-localization-triangulated).
-/

@[expose] public section

universe r u v

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory
namespace ScalarLocalization

/-- Scalar localization with its induced shift and image triangles is triangulated, and
localization is exact. Source: Stacks Project, Tags 05R2 and 05R6; blueprint rationalization
of `def-weil-rationalization-karoubi`
(blueprint: lem-weil-linear-scalar-localization-triangulated).

Proof plan:
1. Use `lem-weil-linear-scalar-localization-category` for composition, Q, and the induced
shift. The zero object and biproduct diagrams survive. By
`lem-weil-pbc-localization-module-tensor` and `def-weil-pbc-module-localization-away`,
morphisms are fractions f/p^n, with equality after multiplying by a further power of p.
2. Let S consist of arrows inverted by Q. An inverse fraction can be cleared to give
h s = p^N id and s h = p^N id in C. Identity/composition closure, saturation, and shift
invariance follow, giving MS1, MS4, MS5 of `def-pur-saturated-triangulated-localization`.
3. The cleared inverse gives both Ore squares: use p^N id as the new denominator.
For cancellation, Q(f) = Q(g) means p^k(f-g) = 0, giving both equalizing denominators.
This proves MS2 and MS3.
4. Apply `lem-weil-pbc-hom-into-triangle-exact` to triangles and their rotations. Localize
the resulting five-term R-linear exact Hom rows. If b(y)/p^n = 0, then b(p^k y) = 0
for some k; lift p^k y along the preceding map to prove exactness after localization.
5. Complete a square of distinguished triangles by TR3. Four vertical Hom maps are
invertible, so `lem-weil-pbc-five-lemma` in the abelian category of additive groups
(`def-sp-abelian`) makes the middle Hom map invertible. Testing all sources proves the
third triangle map is inverted by Q, establishing MS6.
6. Verify Q's localization universal property for arbitrary functors F inverting S:
send f/p^n to F(f) F(p id)^(-n). Scalar naturality gives well-definedness and composition;
the same identity extends natural transformations uniquely. No additivity of F is needed.
7. Apply `lem-pur-localization-triangles-05r6`. Its shift agrees with the tensor-induced
shift, its distinguished triangles are exactly the isomorphic Q-images, and it supplies
TR4 and exactness of Q. There is no idempotent completion.

The existential instances supply structures on the fixed raw scalar category. The equality
of shift functors specifies the induced shift on objects and tensor morphisms. The HEq
normalization specifies the canonical identity comparison with Q, rather than a twisted
shift comparison. Only the shift by one is assumed R-linear. -/
theorem exists_triangulated_scalarLocalization
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [(shiftFunctor C (1 : ℤ)).Linear R] (p : R) :
    ∃ z : HasZeroObject (ScalarLocalization R C p),
      (fun [zeroInst : HasZeroObject (ScalarLocalization R C p)] ↦
        ∃ s : HasShift (ScalarLocalization R C p) ℤ,
          (fun [shiftInst : HasShift (ScalarLocalization R C p) ℤ] ↦
            shiftFunctor (ScalarLocalization R C p) (1 : ℤ) =
                map R C p (shiftFunctor C (1 : ℤ)) ∧
            ∃ a : ∀ n : ℤ, (shiftFunctor (ScalarLocalization R C p) n).Additive,
              (fun [addInst : ∀ n : ℤ,
                  (shiftFunctor (ScalarLocalization R C p) n).Additive] ↦
                ∃ q : (localization R C p).CommShift ℤ,
                  (fun [commInst : (localization R C p).CommShift ℤ] ↦
                    (∀ X : C,
                      HEq (((localization R C p).commShiftIso (1 : ℤ)).hom.app X)
                        (𝟙 ((localization R C p).obj ((shiftFunctor C (1 : ℤ)).obj X)))) ∧
                    ∃ t : Pretriangulated (ScalarLocalization R C p),
                      (fun [triInst : Pretriangulated (ScalarLocalization R C p)] ↦
                        IsTriangulated (ScalarLocalization R C p) ∧
                        (localization R C p).IsTriangulated ∧
                        ∀ T : Triangle (ScalarLocalization R C p),
                          T ∈ distTriang (ScalarLocalization R C p) ↔
                            ∃ T' : Triangle C, T' ∈ distTriang C ∧
                              Nonempty (T ≅ (localization R C p).mapTriangle.obj T'))
                        (triInst := t)) (commInst := q)) (addInst := a)) (shiftInst := s))
        (zeroInst := z) := by
  sorry

end ScalarLocalization
end CategoryTheory
