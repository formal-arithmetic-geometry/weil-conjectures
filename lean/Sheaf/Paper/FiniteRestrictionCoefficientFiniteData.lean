/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.FiniteRestrictionCoefficientCore
public import Mathlib.CategoryTheory.Triangulated.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Finite coefficient-stage data and exactness descent

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; the finite-stalk
step of the blueprint finite pushforward proof (blueprint: def-zl-finite-restriction-finite-data).

## Main definitions

- `WeilConjectures.FiniteRestrictionCoefficient.FiniteData`: finite coefficient-stage data and
exactness descent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
namespace WeilConjectures.FiniteRestrictionCoefficient
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage stageSystem inclusion stageTransition)
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})

/-- A finite diagram, finitely many distinguished triangles, and finitely many
specified equality witnesses, all represented at one coefficient field. Repeated
vertices allow arbitrary finite diagrams; the arrow and triangle isomorphisms
are part of the data, not only existence of isomorphic individual objects.
Source: Bhatt--Scholze 6.8.14 and the common-stage Hom quotient
(blueprint: def-zl-finite-restriction-finite-data). -/
def FiniteData : Prop :=
  ∀ (n m t e : ℕ)
    (K : Fin n → generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (a b : Fin m → Fin n) (f : ∀ j, K (a j) ⟶ K (b j))
    (T : Fin t → Triangle (generalAlgebraicallyClosedConstructibleCategory l Ω W))
    (_hT : ∀ j, T j ∈ distTriang _)
    (A : Fin e → Index l Ω)
    (M N : ∀ j, Stage l Ω W (A j))
    (r s : ∀ j, M j ⟶ N j)
    (_eqs : ∀ j, (inclusion (A j)).map (r j) = (inclusion (A j)).map (s j)),
    ∃ (B : Index l Ω) (hA : ∀ j, A j ≤ B)
      (KB : Fin n → Stage l Ω W B)
      (iK : ∀ j, (inclusion B).obj (KB j) ≅ K j)
      (fB : ∀ j, KB (a j) ⟶ KB (b j))
      (TB : Fin t → Triangle (Stage l Ω W B)),
      (∀ j, (inclusion B).map (fB j) ≫ (iK (b j)).hom =
        (iK (a j)).hom ≫ f j) ∧
      (∀ j, TB j ∈ distTriang _ ∧
        Nonempty ((inclusion B).mapTriangle.obj (TB j) ≅ T j)) ∧
      (∀ j, (stageTransition l Ω W (A j) B (hA j)).map (r j) =
        (stageTransition l Ω W (A j) B (hA j)).map (s j))

/-- The conditional t-exactness clause uses exactly the standard classes of the
recorded intrinsic categories, in every degree and for both halves.
Source: Bhatt--Scholze 6.8.14; standard common-stage pair
(blueprint: def-zl-finite-restriction-finite-data). -/
def TExactDescent {Z : Scheme.{u}}
    (F : (stageSystem l Ω W).Morphism (stageSystem l Ω Z)) : Prop :=
  (∀ (A : Index l Ω) (b : Bool) (n : ℤ) (K : Stage l Ω W A),
    sfRationalStandardClass l (Coefficient.{u} l Ω A) W b n K →
      sfRationalStandardClass l (Coefficient.{u} l Ω A) Z b n ((F.Φ A).obj K)) →
    ∀ (b : Bool) (n : ℤ) (K : generalAlgebraicallyClosedConstructibleCategory l Ω W),
      sfCommonStageStandardClass l W Ω b n K →
        sfCommonStageStandardClass l Z Ω b n (F.functor.obj K)


/-- The exact heart restriction of a stagewise t-exact direct image remains exact.
The object and arrow formulas fix its inclusion in the common-stage category.
Source: BBD 1.3.6, 1.3.16; Bhatt--Scholze 6.8.14
(blueprint: def-zl-finite-restriction-finite-data). -/
def HeartExactDescent {Z : Scheme.{u}}
    (F : (stageSystem l Ω W).Morphism (stageSystem l Ω Z)) : Prop :=
  (∀ (A : Index l Ω) (b : Bool) (n : ℤ) (K : Stage l Ω W A),
    sfRationalStandardClass l (Coefficient.{u} l Ω A) W b n K →
      sfRationalStandardClass l (Coefficient.{u} l Ω A) Z b n ((F.Φ A).obj K)) →
    ∃ (H : sfCommonStageHeart l W Ω ⥤ sfCommonStageHeart l Z Ω)
      (_hH : H.Additive),
      (∀ K, (H.obj K).obj = F.functor.obj K.obj) ∧
      (∀ {K M} (g : K ⟶ M), HEq (H.map g).hom (F.functor.map g.hom)) ∧
      ∀ C : ShortComplex (sfCommonStageHeart l W Ω), C.ShortExact →
        (C.map H).ShortExact

end WeilConjectures.FiniteRestrictionCoefficient
