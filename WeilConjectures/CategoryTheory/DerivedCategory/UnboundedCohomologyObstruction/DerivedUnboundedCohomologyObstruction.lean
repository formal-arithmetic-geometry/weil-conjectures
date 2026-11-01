/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.DirectSum.Module
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.Products
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.InjectiveCoseparator
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.GrothendieckDerivedCoproductsColimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.DerivedHomologyInjective
import Mathlib.CategoryTheory.Generator.Abelian

/-!
# Unbounded cohomology obstructs right adjoints

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/
sec-sbc-uniform/sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md,
consequences (ii) and (iii) (blueprint: lem-sf-derived-unbounded-cohomology-obstruction).
The natural number `n` indexes the strictly positive integer `n + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory Limits

open scoped DirectSum

universe uA vA dA uB vB dB r m dM

namespace DerivedCategory.UnboundedCohomologyObstruction

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{dA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{dB} B]
  {R : Type r} [CommRing R] [HasDerivedCategory.{dM} (ModuleCat.{max r m} R)]

/-- The family `K_n = F[0][n]`, with `n ≥ 1` indexed by `ℕ`.
Source: scope remark, consequence (ii)
(blueprint: lem-sf-derived-unbounded-cohomology-obstruction). -/
abbrev shifts (F : A) (n : ℕ) : DerivedCategory A :=
  ((DerivedCategory.singleFunctor A 0).obj F)⟦((n + 1 : ℕ) : ℤ)⟧

variable (e : B ⥤ ModuleCat.{max r m} R) [e.Additive]
  [PreservesFiniteLimits e] [PreservesFiniteColimits e]
  (T : DerivedCategory A ⥤ DerivedCategory B)

/-- Evaluation of degree-zero cohomology after the exact termwise functor `e`.
Source: scope remark, consequence (ii)
(blueprint: lem-sf-derived-unbounded-cohomology-obstruction). -/
abbrev evaluation : DerivedCategory B ⥤ ModuleCat.{max r m} R :=
  e.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor (ModuleCat.{max r m} R) 0

/-- The modules `H^(n+1)(eT(F[0]))`.
Source: scope remark, consequence (ii)
(blueprint: lem-sf-derived-unbounded-cohomology-obstruction). -/
abbrev cohomology (F : A) (n : ℕ) : ModuleCat.{max r m} R :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max r m} R) ((n + 1 : ℕ) : ℤ)).obj
    (e.mapDerivedCategory.obj (T.obj ((DerivedCategory.singleFunctor A 0).obj F)))

/-- The canonical shift identification `H⁰(eT(K_n)) ≅ H^(n+1)(eT(F[0]))`.
Source: scope remark, consequence (ii), exact functor and shift compatibility
(blueprint: lem-sf-derived-unbounded-cohomology-obstruction). -/
def shiftIdentification [T.CommShift ℤ] (F : A) (n : ℕ) :
    (evaluation e).obj (T.obj (shifts F n)) ≅ cohomology e T F n :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max r m} R) 0).mapIso
      (((T ⋙ e.mapDerivedCategory).commShiftIso ((n + 1 : ℕ) : ℤ)).app
        ((DerivedCategory.singleFunctor A 0).obj F)) ≪≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{max r m} R) 0).isoShift
      ((n + 1 : ℕ) : ℤ)).app
        (e.mapDerivedCategory.obj (T.obj ((DerivedCategory.singleFunctor A 0).obj F)))

/-- The canonical map `Hom(T(K_n), v(J)[0]) → Hom_R(H^(n+1)(eT(F[0])), J)`: apply `e`
termwise and degree-zero cohomology, identify `H⁰(eT(K_n))` by `shiftIdentification` and
`H⁰(e(v(J))[0])` with `e(v(J))`, then compose with the counit `e(v(J)) → J`. This is the
derived adjunction isomorphism followed by the injective-target `H⁰` bijection.
Source: scope remark, consequence (iii), injective-cogenerator Hom calculation
(blueprint: lem-sf-derived-unbounded-cohomology-obstruction). -/
def injectiveHomMap [T.CommShift ℤ] {v : ModuleCat.{max r m} R ⥤ B} (a : e ⊣ v)
    (F : A) (n : ℕ) (J : ModuleCat.{max r m} R) :
    (T.obj (shifts F n) ⟶ (DerivedCategory.singleFunctor B 0).obj (v.obj J)) →
      (cohomology e T F n ⟶ J) :=
  fun g => (shiftIdentification e T F n).inv ≫ (evaluation e).map g ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{max r m} R) 0).map
      ((e.mapDerivedCategorySingleFunctor 0).hom.app (v.obj J)) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max r m} R) 0).hom.app
      (e.obj (v.obj J)) ≫ a.counit.app J

/-- Unbounded positive cohomology prevents coproduct preservation and either right adjoint.

Source: scope remark, consequences (ii) and (iii)
(blueprint: lem-sf-derived-unbounded-cohomology-obstruction).

Proof: In each degree the family of shifted single complexes has only one nonzero term,
so its direct sum and product coincide. The Grothendieck derived coproduct theorem and
exact-product localization identify them in the derived category. Exactness and shift
compatibility give `shiftIdentification`. Applying degree-zero evaluated cohomology to
the coproduct comparison gives the canonical inclusion of the direct sum into the product:
the two characterizations below check this on every summand and coordinate. Choose a
nonzero element in each cohomology module; the resulting infinite-support tuple proves
that inclusion is not surjective. Thus `T` cannot preserve countable coproducts, and cannot
be a left adjoint. For any injective cogenerator `J`, its image under the exact right
adjoint `v` is injective. Localizing the exact adjunction and computing derived Hom into
an injective single complex shows that the canonical map `injectiveHomMap` from the displayed
derived Hom group to module Hom into `J` is bijective.
They are nonzero by cogeneration. If the restriction to `D⁺` had a right adjoint `G`, these
same groups would equal `Hom(F[n+1],G(v(J)[0]))`; bounded-below t-structure orthogonality
makes these vanish for all sufficiently large `n`, a contradiction.
-/
theorem obstruction
    [IsGrothendieckAbelian.{vA} A] [IsGrothendieckAbelian.{vB} B]
    [HasExactLimitsOfShape (Discrete ℕ) A] [HasExactLimitsOfShape (Discrete ℕ) B]
    [Nontrivial R]
    (he : ∀ I : Type vB, PreservesColimitsOfShape (Discrete I) e)
    [PreservesLimitsOfShape (Discrete ℕ) e]
    (v : ModuleCat.{max r m} R ⥤ B) [v.Additive]
    [PreservesFiniteLimits v] [PreservesFiniteColimits v] (a : e ⊣ v)
    [T.Additive] [T.CommShift ℤ] [T.IsTriangulated]
    [PreservesLimitsOfShape (Discrete ℕ) T]
    (Tplus : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (compatibility : Tplus ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ T)
    (F : A) (hF : ∀ n : ℕ, ¬ IsZero (cohomology e T F n)) :
    Nonempty (IsLimit (Fan.mk (∐ shifts F) (Sigma.π (shifts F)))) ∧
    (∃ (α : ModuleCat.of R (⨁ n : ℕ, cohomology e T F n) ≅
          (evaluation e).obj (∐ fun n : ℕ => T.obj (shifts F n)))
    (β : (evaluation e).obj (T.obj (∐ shifts F)) ≅
          ModuleCat.of R (∀ n : ℕ, cohomology e T F n)),
      (∀ n : ℕ, ModuleCat.ofHom (DirectSum.lof R ℕ
          (fun j : ℕ => cohomology e T F j) n) ≫ α.hom =
        (shiftIdentification e T F n).inv ≫
          (evaluation e).map (Sigma.ι (fun j : ℕ => T.obj (shifts F j)) n)) ∧
      (∀ n : ℕ, β.hom ≫ ModuleCat.ofHom (LinearMap.proj n) =
        (evaluation e).map (T.map (Sigma.π (shifts F) n)) ≫
          (shiftIdentification e T F n).hom) ∧
      α.hom ≫ (evaluation e).map (sigmaComparison T (shifts F)) ≫ β.hom =
        ModuleCat.ofHom (DirectSum.coeFnLinearMap R)) ∧
    ¬ Function.Surjective
      (DirectSum.coeFnLinearMap R (M := fun n : ℕ => cohomology e T F n)) ∧
    ¬ PreservesColimitsOfShape (Discrete ℕ) T ∧
    ¬ T.IsLeftAdjoint ∧ ¬ Tplus.IsLeftAdjoint ∧
    ∀ (J : ModuleCat.{max r m} R), Injective J → IsCoseparator J →
      Injective (v.obj J) ∧
      ∀ n : ℕ, Function.Bijective (injectiveHomMap e T a F n J) ∧
        Nontrivial (cohomology e T F n ⟶ J) ∧
        Nontrivial (T.obj (shifts F n) ⟶
          (DerivedCategory.singleFunctor B 0).obj (v.obj J)) := by
  sorry

end DerivedCategory.UnboundedCohomologyObstruction
