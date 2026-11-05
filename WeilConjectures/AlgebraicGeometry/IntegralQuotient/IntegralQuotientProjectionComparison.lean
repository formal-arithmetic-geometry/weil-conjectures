/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientDirectImageComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.QuotientPullbackTensorCoherence
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-! # Reduction of the actual integral projection morphism

Source: blueprint main-20261015, integral proper-base-change proof, paragraph (3);
Stacks Project, Tags 0B56, 07A4, 07A6 and 0D6D
(blueprint: lem-sfb-integral-quotient-projection-comparison).

The scalar tensor comparison is specified by its computation counits and the signed
ordinary balancing map. Unlike the exact-scalar interface, this applies to reduction
modulo a uniformizer. Positive levels are indexed by n + 1, as in the dependency.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.all false
set_option linter.unusedVariables false
set_option maxHeartbeats 200000

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.ProEtale.QuotientChange
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] ScalarTensorNormalized

section GenericComputations

section CachedGenericStructures
variable {C : Type*} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
end CachedGenericStructures
attribute [local instance 2000] cachedComplexMonoidal cachedHomotopyMonoidal
  cachedDerivedMonoidal

@[irreducible] private def canonicalScalarTensorIso (n : ℕ) (T : Scheme.{u}) :
    ScalarTensorIso l E n T := by
  let m := CondensedRing.internalScalarMonoidal (reduction l E n) T
  unfold ScalarTensorIso D CondensedRing.derivedTensor
  exact asIso (extension (reduction l E n) T).leftDerivedTensorComparison

attribute [local irreducible] cochainCompute

end GenericComputations

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

/-- The uniquely normalized scalar tensor balancing isomorphism. The existence
statement determines the whole natural isomorphism, rather than an arbitrary map.
Source: Stacks 07A4, blueprint paragraph (3)
(blueprint: lem-sfb-integral-quotient-projection-comparison). -/
@[irreducible] def scalarTensorIso (n : ℕ) (T : Scheme.{u}) :
    ScalarTensorIso l E n T :=
  (scalarTensorIso_existsUnique l E n T).exists.choose

/-- The existing pullback tensor comparison with its named pullback functor.
Source: Stacks 07A4 (blueprint: lem-sfb-integral-quotient-projection-comparison). -/
@[irreducible] def actualTensorPull
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.postcompose₂.obj (L Λ f)).obj (CondensedRing.derivedTensor Λ Y) ⟶
      (((Functor.whiskeringLeft₂ _).obj (L Λ f)).obj (L Λ f)).obj
        (CondensedRing.derivedTensor Λ X) := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.leftDerivedUpperStarTensor Λ f

/-- The actual projection bifunctor transformation, using the existing adjunction
and its actual tensor comparison. This is the recorded moduleObjectProjectionMap
before evaluating its two components, with only its functor names made explicit.
Source: Stacks 0B56 (blueprint: lem-sfb-integral-quotient-projection-comparison). -/
@[irreducible] def actualProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    F Λ f ⋙ CondensedRing.derivedTensor Λ Y ⟶
      (Functor.postcompose₂.obj (F Λ f)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 (DerivedCategory (Modules Λ X)))).obj
          (L Λ f)).obj (CondensedRing.derivedTensor Λ X)) :=
  (adj Λ f).rightAdjointProjectionMap (actualTensorPull Λ f)

/-- The displayed projection comparison equation, with the coefficient parameters
shared explicitly. This is an equality of actual arrows in the quotient module
category; it neither forgets the scalar action nor asserts only cohomological equality.
Source: blueprint integral proper-base-change proof (3), Stacks 0B56 and 07A6
(blueprint: lem-sfb-integral-quotient-projection-comparison). -/
@[irreducible] def ProjectionComparisonEquation
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : D a Y ⋙ L S f ≅ L R f ⋙ D a X)
    (bX : (Functor.postcompose₂.obj (D a X)).obj (CondensedRing.derivedTensor R X) ≅
      (((Functor.whiskeringLeft₂ _).obj (D a X)).obj (D a X)).obj
        (CondensedRing.derivedTensor S X))
    (bY : (Functor.postcompose₂.obj (D a Y)).obj (CondensedRing.derivedTensor R Y) ≅
      (((Functor.whiskeringLeft₂ _).obj (D a Y)).obj (D a Y)).obj
        (CondensedRing.derivedTensor S Y))
    (K : DerivedCategory (Modules R X)) (M : DerivedCategory (Modules R Y)) : Prop :=
  (bY.hom.app ((F R f).obj K)).app M ≫
      ((CondensedRing.derivedTensor S Y).map ((rho a f c).app K)).app ((D a Y).obj M) ≫
      ((actualProjection S f).app ((D a X).obj K)).app ((D a Y).obj M) =
    (D a Y).map (((actualProjection R f).app K).app M) ≫
      (rho a f c).app (((CondensedRing.derivedTensor R X).obj K).obj ((L R f).obj M)) ≫
      (F S f).map
        ((bX.hom.app K).app ((L R f).obj M) ≫
          ((CondensedRing.derivedTensor S X).obj ((D a X).obj K)).map (c.inv.app M))

@[irreducible] private def uncurriedScalarTensor (n : ℕ) (T : Scheme.{u})
    (b : ScalarTensorIso l E n T) :
    QuotientSectionTensor.TensorIso (reduction l E n) T :=
  uncurryTensorIso (D (reduction l E n) T)
    (CondensedRing.derivedTensor (integral l E) T)
    (CondensedRing.derivedTensor (finite l E n) T) b

end AlgebraicGeometry.ProEtale.IntegralQuotient
