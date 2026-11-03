/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.StrictDirectImageMixedUnit.StrictDirectImageMixedUnitData
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison

/-! # The normalized direct-image/total-limit comparison

Source: Stacks 0A07, 0D6E, 0941; the direct-image paragraph of
`lem-fix-operation-reduction`
(blueprint: lem-weil-direct-image-limit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
/-- The two ordinary presentations of completed-coefficient direct image coincide.
Their derived comparison retains the universal right-derived units.
Source: Stacks 0D6E
(blueprint: lem-weil-direct-image-limit-comparison). -/
def completedDirectImageComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    sfCompletedDerivedDirectImage l E f ≅
      PurCompactSupport.push (PurCompactSupport.completed l E) f := by
  have hm : proEtaleRingDirectImageMap f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f) = sfCompletedCoefficientMap l E f :=
    (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply (sfCompletedCoefficientMap l E f)
  have he : sfCompletedModuleDirectImage l E f =
      proEtaleRingModuleDirectImage f
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f) := by
    unfold proEtaleRingModuleDirectImage
    rw [hm]
    rfl
  have hF : (sfCompletedModuleDirectImage l E f).Additive :=
    sfCompletedModuleDirectImage_additive l E f
  have hG : (proEtaleRingModuleDirectImage f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f)).Additive := he ▸ hF
  exact @Functor.rightDerivedFunctorNatIso _ _ _ _ _ _ _ _ _ _ _ hF hG (eqToIso he)

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
/-- Direct image commutes with total limit on the whole ringed sequence site, with
its ordinary projection and whole-complex derived-unit normalizations.
Source: Stacks 0A07, 0D6E, 0941; direct-image paragraph of
`lem-fix-operation-reduction`
(blueprint: lem-weil-direct-image-limit-comparison).

Proof: ordinary direct image is sectionwise restriction to the inverse-image
object. Ordinary coefficient restriction keeps the underlying abelian sheaf.
Thus both orders of ordinary limit and direct image have the same compatible
section tuples; identity on those tuples is linear and natural and commutes with
every limit projection. For derivation, regard the entire sequence as modules on
the ringed product site. Its quotient-system inverse image is exact, so system
direct image preserves K-injectives. Treat coefficient restriction by ringed-topos
composition, without a K-injective preservation assumption for restriction. Derive
the two factorizations using their universal right-derived units. The composition
comparison and the exact coefficient-restriction comparison give the stated
isomorphism. The universal-unit equation for these compositors is precisely
LimitComparison.normalization. This is a comparison on entire complexes before
any evaluation, so no faithfulness of derived evaluations is used. The argument
works for empty schemes, zero complexes, and arbitrary scheme morphisms. -/
theorem directImageLimitComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty (StrictDirectImageMixedUnit.LimitComparison l E f) := by sorry

attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
/-- Reconstruction along direct image, using its normalized limit comparison
and the actual reduction/limit unit. It is defined on every derived object.
Source: Stacks 0A07, 0D6E
(blueprint: lem-weil-direct-image-limit-comparison). -/
def directImageReconstruction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : StrictDirectImageMixedUnit.LimitComparison l E f) :
    PurCompactSupport.push (PurCompactSupport.completed l E) f ⟶
      FrobeniusExchange.integralDirectImage l E f :=
  (completedDirectImageComparison l E f).inv ≫
    Functor.whiskerRight ((FrobeniusExchange.models l E).system X).adjunction.unit
      (sfCompletedDerivedDirectImage l E f) ≫
    Functor.whiskerLeft (FrobeniusExchange.reduction l E X) C.derived.inv

end WeilConjectures
