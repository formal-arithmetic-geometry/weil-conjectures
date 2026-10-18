import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Counit cones from ordinary complementary triangles

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
  sk-prop-sf-localization/_section.md, place "Hom(-,L) argument: complete the exceptional
  counit and identify its cone by closed and open Hom tests"
(blueprint: lem-sf-ordinary-triangle-counit-cone)

This module states the abstract counit-cone comparison for a complementary pair of
triangulated categories. The proof is supplied in the DAG proof record.
-/

open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Pretriangulated
open CategoryTheory.Limits

universe vT uT vZ uZ vU uU

namespace CategoryTheory

variable {T : Type uT} [Category.{vT} T] [HasZeroObject T] [Preadditive T]
  [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] [IsTriangulated T]
variable {TZ : Type uZ} [Category.{vZ} TZ] [HasZeroObject TZ] [Preadditive TZ]
  [HasShift TZ ℤ]
  [∀ n : ℤ, (shiftFunctor TZ n).Additive]
  [Pretriangulated TZ] [IsTriangulated TZ]
variable {TU : Type uU} [Category.{vU} TU] [HasZeroObject TU] [Preadditive TU]
  [HasShift TU ℤ]
  [∀ n : ℤ, (shiftFunctor TU n).Additive]
  [Pretriangulated TU] [IsTriangulated TU]

/-- Identification of a counit cone from an ordinary complementary triangle.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
  sk-prop-sf-localization/_section.md, place "Hom(-,L) argument: complete the exceptional
  counit and identify its cone by closed and open Hom tests"
(blueprint: lem-sf-ordinary-triangle-counit-cone).

Here `iStar, iLeft, iRight, jBang, jStar, jRight` are `i_*, i^*, i^!, j_!, j^*, j_*`; write
`A = i_* i^! K`, `B = j_* j^* K`, `e : A ⟶ K` the counit of `adjRight`, `u : K ⟶ B` the unit of
`adjOpen`.

Proof (DAG proof record, after prop-sf-localization-all-stages.proof.md Step 3 and
sk-prop-sf-localization.proof.md, Existence):
1. `Hom(i_* P⟦m⟧, j_* Q) ≅ Hom(j^* i_* P⟦m⟧, Q) = 0` by `j^* ⊣ j_*`, `j^* i_* = 0` and
   exactness; the triangle identity of `j^* ⊣ j_*` factors the adjunct of `e ≫ u` through
   `j^* A = 0`, so `e ≫ u = 0`.
2. (TR1) complete `e` to a distinguished triangle `A ⟶ K ⟶ C ⟶ A⟦1⟧` with maps `e, v, w`.
3. Exactness of `Hom(-, B)` on it (lem-weil-pbc-hom-out-of-triangle-exact) and `e ≫ u = 0` give
   `β` with `v ≫ β = u`; for another `β'`, `β - β'` factors through `w` by some `h : A⟦1⟧ ⟶ B`,
   and `h = 0` by Step 1, so `β' = β`.
4. Closed orthogonality: `i_*` is fully faithful (lem-weil-pbc-adjunction-counit-iso-right-
   fully-faithful, from `hClosed`), so postcomposition with `e`, `Hom(i_* Q, A) → Hom(i_* Q, K)`, is
   bijective, and its shift is injective; with lem-weil-pbc-hom-into-triangle-exact and TR2
   rotations, `Hom(i_* Q, C) = 0`; also `Hom(i_* Q, B) = 0` by Step 1. For any such `X` the
   ordinary triangle `j_! j^* M ⟶ M ⟶ i_* i^* M ⟶` of `hOrdinary` and Hom-out exactness make
   precomposition with the counit `j_! j^* M ⟶ M` a bijection `Hom(M, X) ≅ Hom(j_! j^* M, X)`,
   natural in `X`.
5. Through `j_! ⊣ j^*`, `Hom(M, β)` becomes `Hom(j^* M, j^* β)`. `j^*` maps the cone triangle to
   a distinguished triangle with `j^* A = 0`, so `j^* v` is invertible (Hom-into exactness and
   lem-coef-joyal-homset-iso-detection); the triangle identity and `hOpen` make `j^* u`
   invertible; hence `j^* β` is, and `Hom(M, β)` is bijective for every `M`.
6. By the Yoneda criterion lem-coef-joyal-homset-iso-detection, `β` is an isomorphism.
-/
theorem ordinaryTriangleCounitCone
    (iStar : TZ ⥤ T) (iLeft : T ⥤ TZ) (iRight : T ⥤ TZ)
    (jBang : TU ⥤ T) (jStar : T ⥤ TU) (jRight : TU ⥤ T)
    [iStar.CommShift ℤ] [iLeft.CommShift ℤ] [iRight.CommShift ℤ]
    [jBang.CommShift ℤ] [jStar.CommShift ℤ] [jRight.CommShift ℤ]
    [iStar.IsTriangulated] [iLeft.IsTriangulated] [iRight.IsTriangulated]
    [jBang.IsTriangulated] [jStar.IsTriangulated] [jRight.IsTriangulated]
    (adjLeft : iLeft ⊣ iStar) (adjRight : iStar ⊣ iRight)
    (adjBang : jBang ⊣ jStar) (adjOpen : jStar ⊣ jRight)
    (hClosed : ∀ P : TZ, IsIso (adjLeft.counit.app P))
    (hOpen : ∀ Q : TU, IsIso (adjOpen.counit.app Q))
    (hDisjoint : ∀ P : TZ, IsZero (jStar.obj (iStar.obj P)))
    (hOrdinary : ∀ M : T,
      ∃ δ : iStar.obj (iLeft.obj M) ⟶ (jBang.obj (jStar.obj M))⟦(1 : ℤ)⟧,
        Triangle.mk (adjBang.counit.app M) (adjLeft.unit.app M) δ ∈ distTriang T) :
    ∀ K : T,
      (∀ (C : T) (v : K ⟶ C)
        (w : C ⟶ (shiftFunctor T (1 : ℤ)).obj (iStar.obj (iRight.obj K))),
        Triangle.mk (adjRight.counit.app K) v w ∈ distTriang T →
        ∃ β : C ⟶ jRight.obj (jStar.obj K),
          v ≫ β = adjOpen.unit.app K ∧ IsIso β ∧
            ∀ β' : C ⟶ jRight.obj (jStar.obj K),
              v ≫ β' = adjOpen.unit.app K → β' = β) ∧
      ∀ (P : TZ) (Q : TU) (m : ℤ),
        Subsingleton ((shiftFunctor T m).obj (iStar.obj P) ⟶ jRight.obj Q) := by
  sorry

end CategoryTheory
