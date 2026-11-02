/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSheafExt
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerStrictAdjunctData
import WeilConjectures.AlgebraicGeometry.Strict.StrictKummerUnitNormalization
import WeilConjectures.AlgebraicGeometry.Kummer.KummerAdjunctFromUnit

/-! # Strict Kummer comparison and adjunct compatibility

Source: diagonal tower system proof, the target paragraph of step (3) and naturality in step (4).
(blueprint: lem-sfb-kummer-strict-adjunct-compatibility). -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] CategoryTheory.Abelian.Ext
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 11000] kummerModuleHasExt kummerAbHasExt

attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ diagonalDerivedSingleCounit
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierEtaleKummerUnit cartierProKummerUnit cartierProIntegralGenerator cartierProRootMap
  cartierReducedEtale cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierResidueReducedPro diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary geoCartierLine
  Ext.homEquiv Ext.mapExactFunctor Functor.mapDerivedCategory
  Functor.mapDerivedCategorySingleFunctor

/-- Assemble the target comparison before specializing to concrete coefficient sheaves. -/
private theorem compatibility_from_normalized_target
    {A B : Type*} [Category A] [Abelian A] [HasExt.{w} A]
    [Category B] [Abelian B] [HasExt.{w} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    {ℓ : ℕ} {L : A ⥤ B} {U : B ⥤ A} {ad : L ⊣ U}
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {D : DiagonalDerivedReduction ℓ L}
    {C : ℕ → Type*} [∀ n, Category (C n)] [∀ n, Abelian (C n)]
    [∀ n, HasExt.{w} (C n)]
    {F : ∀ n, C n ⥤ B} [∀ n, (F n).Additive]
    [∀ n, PreservesFiniteLimits (F n)] [∀ n, PreservesFiniteColimits (F n)]
    {V : ∀ n, C n ⥤ A} [∀ n, (V n).Additive]
    [∀ n, PreservesFiniteLimits (V n)] [∀ n, PreservesFiniteColimits (V n)]
    {M : A} {rootsTower : ℕᵒᵖ ⥤ A} {P : ∀ n, C n}
    {κ : ∀ n, Ext M ((V n).obj (P n)) 1}
    {rootNorm : ∀ H : ℕᵒᵖ ⥤ B, (H ⋙ U ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ (F n).obj (P n)) → Prop}
    (σ : ∀ n, V n ≅ F n ⋙ U) (η : ∀ n, DiagonalEvaluationUnit U ad D n)
    (hσ : ∀ n (S : A) (Q : C n) (q : S ⟶ U.obj ((F n).obj Q))
      (g : S ⟶ (V n).obj Q), HEq q g → q ≫ (σ n).inv.app Q = g)
    (target : KummerUnitNormalizedTarget ℓ L U ad D C F V M rootsTower P κ
      rootNorm σ η) :
    KummerTargetAdjunctCompatibility ℓ L U ad D C F V M rootsTower P κ rootNorm := by
  unfold KummerUnitNormalizedTarget at target
  obtain ⟨H, roots, b, t, ht, hb⟩ := target
  unfold KummerTargetAdjunctCompatibility
  refine ⟨H, roots, b, t, ht, ?_⟩
  intro n S a ha Q s g hg f e he
  let E := (evaluation ℕᵒᵖ B).obj (op n)
  let q := ad.unit.app S ≫ U.map ((D.ordinary.π n).app S)
  refine kummer_adjunct_from_unit D.T E U (F n) (V n) (σ n)
    (η n).unit a b s (t n) q g (κ n) ?_ (hb n) ?_ f e he
  · rw [ha]
    exact (η n).single S
  · simpa only [q, Functor.map_comp, Category.assoc] using
      hσ n S Q (ad.unit.app S ≫ U.map ((D.ordinary.π n).app S ≫ s.hom)) g hg

/-- A strict Kummer comparison computes the adjunct of every residue lift.

Source: diagonal tower system proof, target paragraph of step (3), and
naturality in step (4)
(blueprint: lem-sfb-kummer-strict-adjunct-compatibility).

Proof: compute simultaneous reduction on a flat-term K-flat resolution of
comparison units, comparing at each exponent with the two-term coefficient
resolution. Exact comparison and Kummer exactness give only the roots kernel
in degree minus one. The coefficient transition is multiplication by the prime
in degree minus one and identity in degree zero; hence its action on the kernel
is the actual power-prime roots transition. Good truncation in the category of
strict systems gives H and its underlying roots isomorphism. Take b to be the
negative normalized Kummer isomorphism, and use the roots-to-line comparison
for t. This proves the displayed roots equation at every level.
For the last assertion, compare evaluation of the same resolution with derived
residue extension, then forget to abelian sheaves. The source counit and the
quotient adjunction give the prescribed map g. The negative normalization of b
gives minus the positive Kummer unit, preceded by the units comparison.
Naturality of the derived adjunction unit for f therefore computes the adjunct
of the evaluated arrow as minus f followed by this unit. If a residue class e
restricts to that evaluated arrow, functoriality of exact scalar restriction
and the equation for g identify its scalar adjunct with this computation.
This assertion does not produce e, or claim that restriction is full on Ext.
The residue lift is an independent input to this compatibility calculation. -/
theorem kummer_strict_adjunct_compatibility (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) :
    kummerStrictAdjunctCompatibilityStatement ℓ W hW D := by
  classical
  let η := fun n ↦ (diagonal_evaluation_unit_exists ℓ W D n).some
  unfold kummerStrictAdjunctCompatibilityStatement
  refine compatibility_from_normalized_target
    (fun n ↦ diagonalFiniteForgetIso ℓ n W) η ?_ ?_
  · exact fun n S Q q g h ↦ diagonalFiniteForgetIso_transport ℓ n W S Q q g h
  · exact strict_kummer_unit_normalization ℓ W hW D η

end AlgebraicGeometry.ProEtale
