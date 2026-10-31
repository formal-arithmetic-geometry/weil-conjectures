/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationSupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.ConstructibleSheaf.FreeLifting
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.CategoryTheory.ScalarLocalizationUnderlyingTelescope
public import WeilConjectures.AlgebraicGeometry.PadicIntegersInvertEll

/-!
# The rational localization push mate on its specified telescope legs

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.proof.md,
paragraph (1) (blueprint: lem-sfb-rational-localization-push-legs).

The ordinary module-object derived categories and the existing normalized unit cocones
are used throughout. The native restriction comparison is the ring-sheaf comparison
under the module-object/module-sheaf identifications of the node.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The restricted canonical scalar push mate, followed by the canonical restriction
comparison. This is `d ∘ V(γ)` in the node's functional composition convention.
Source: the rational proper-base-change proof, paragraph (1)
(blueprint: lem-sfb-rational-localization-push-legs). -/
def rationalLocalizationPushComparison {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))) :
    (integralLocalizationCocone ℓ E Y
        ((moduleObjectDerivedPushforward (integralCoeff ℓ E) p).obj K)).pt ⟶
      (moduleObjectDerivedPushforward (integralCoeff ℓ E) p).obj
        (integralLocalizationCocone ℓ E X K).pt :=
  (Mod.comap (coefficientMap (integralScalarMap ℓ E) Y)).mapDerivedCategory.map
      ((derivedPushHom (integralScalarMap ℓ E) p).app K) ≫
    (derivedComapLowerStarIso (integralScalarMap ℓ E) p).hom.app
      ((integralScalarExtension ℓ E X).obj K)

/-- The scalar push mate has every specified localization leg, is the unique continuity
arrow with those legs, and is natural on bounded-below complexes.
Source: the rational proper-base-change proof, paragraph (1)
(blueprint: lem-sfb-rational-localization-push-legs).

Proof plan:
1. The actual coefficient inclusion is localization at ℓ by
   det-prop-sfb-qlbar-colimit-x-invert-ell; scalar extension is exact. The bounded-below
   pushforward of sk-def-sfb-module-derived-pushpull keeps the input bounded below.
2. Expand def-sfb-derived-push-hom by the unit-counit mate formula
   def-sfb-mate-push-hom. The triangle identity gives c η_Y = G_A(η_X).
   By lem-sfb-derived-comap-native-restriction-comparison, the native comparison here
   is precisely lem-weil-pbc-ring-sheaf-change-adjunction under the stated equivalences.
3. Integer multiplication is central. Cancel its invertible powers on the localized
   objects to commute c with the inverse powers of ℓ, using only additivity of G_A.
4. The normalized legs of lem-weil-pbc-scalar-localization-underlying-telescope are
   the actual unit followed by the restricted inverse powers. Step 2 and step 3
   therefore give c j_Y,n = G_A(j_X,n) for every natural number n.
5. In the distinguished telescope triangle D --(1-s)--> D --> U --> D[1], the family
   G_A(j_X,n) defines b : D --> B with b(1-s)=0. Exactness of Hom(-,B), namely
   lem-weil-pbc-hom-out-of-triangle-exact, supplies a continuity arrow U --> B.
6. For a difference e with zero legs, the same exactness gives e=kδ. On the shifted
   summands write k_n and recursively set z_0=0 and z_(n+1)=ℓ⁻¹(z_n-k_n). Then
   z(1-s)[1]=k. Consecutive triangle arrows compose to zero by
   lem-weil-pbc-hom-into-triangle-exact, so e=0. Finally naturality of the existing
   push mate and restriction comparison gives the displayed naturality identity.
No completeness or constructibility is used. -/
theorem rationalLocalization_push_legs [FiniteDimensional ℚ_[ℓ] E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [QuasiCompact p.left] [QuasiSeparated p.left]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X.left)))
    (hK : DerivedCategory.TStructure.t.plus K) :
    (∀ n : ℕ,
      (integralLocalizationCocone ℓ E Y.left
          ((moduleObjectDerivedPushforward (integralCoeff ℓ E) p.left).obj K)).ι.app n ≫
          rationalLocalizationPushComparison ℓ E p.left K =
        (moduleObjectDerivedPushforward (integralCoeff ℓ E) p.left).map
          ((integralLocalizationCocone ℓ E X.left K).ι.app n)) ∧
    (∀ h : (integralLocalizationCocone ℓ E Y.left
          ((moduleObjectDerivedPushforward (integralCoeff ℓ E) p.left).obj K)).pt ⟶
        (moduleObjectDerivedPushforward (integralCoeff ℓ E) p.left).obj
          (integralLocalizationCocone ℓ E X.left K).pt,
      (∀ n : ℕ,
        (integralLocalizationCocone ℓ E Y.left
            ((moduleObjectDerivedPushforward (integralCoeff ℓ E) p.left).obj K)).ι.app n ≫
            h = (moduleObjectDerivedPushforward (integralCoeff ℓ E) p.left).map
              ((integralLocalizationCocone ℓ E X.left K).ι.app n)) →
        h = rationalLocalizationPushComparison ℓ E p.left K) ∧
    (∀ (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X.left))),
      DerivedCategory.TStructure.t.plus L → ∀ f : K ⟶ L,
        (Mod.comap (coefficientMap (integralScalarMap ℓ E) Y.left)).mapDerivedCategory.map
            ((integralScalarExtension ℓ E Y.left).map
              ((moduleObjectDerivedPushforward (integralCoeff ℓ E) p.left).map f)) ≫
            rationalLocalizationPushComparison ℓ E p.left L =
          rationalLocalizationPushComparison ℓ E p.left K ≫
            (moduleObjectDerivedPushforward (integralCoeff ℓ E) p.left).map
              ((Mod.comap (coefficientMap (integralScalarMap ℓ E) X.left)).mapDerivedCategory.map
                ((integralScalarExtension ℓ E X.left).map f))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
