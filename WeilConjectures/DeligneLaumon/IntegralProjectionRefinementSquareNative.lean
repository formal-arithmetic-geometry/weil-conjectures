/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackTensorComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.Exact.ExactFunctorCoproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionSuccessive
import WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportIdentityCalculus
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedCompositorCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CompositionAdjunctionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian

/-! # Condensed integral projection and one proper refinement

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/
prop-sf-pf-coherence.proof.md, compactification-independence sentence
(blueprint: lem-sf-integral-projection-refinement-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace WeilConjectures

/-- The native ordinary condensed integral projection square for one supplied
proper compactification refinement.

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/
prop-sf-pf-coherence.proof.md, compactification-independence sentence
(blueprint: lem-sf-integral-projection-refinement-square).

Proof plan, following the eight steps of the DAG node:

1. Write the native refinement adjunct as open base change followed by the clopen
   projector, then transpose under pullback/direct image. Compare this transpose with
   the open-adjunction-normalized map of `lem-zl-condensed-open-proper-pasting`.
2. Apply `lem-pur-adjunction-mate-transpose` to its Cartesian open restriction. The
   open unit--square--counit normalization reduces the open transpose to the clopen
   projection, identity on the distinguished component and zero on its complement.
3. Finite-type schemes over the field are Noetherian; their opens are quasi-compact.
   With `lem-pod-condensed-open-derived-calculus`, compare clopen extension with clopen
   direct image by transposing the inverse open unit. Both vanish on the complementary
   open. Joint detection in `lem-sfb-condensed-support-derived-localization` makes this
   comparison invertible, including the empty complement case.
4. Under this normalized clopen comparison the projection is the unit of restriction
   followed by direct image. Its composite with the other unit is the unit for the
   identity map, by `lem-fix-condensed-pullback-coherence`. Open adjunction therefore
   identifies the native refinement transpose with the normalized one.
5. Identify their direct-image compositors. The native compositor is conjugate to
   ordinary pullback composition. Module pullback is exact and the module category is
   Grothendieck abelian. Apply `lem-sfb-derived-composition-adjunction-normalization`
   to identify the termwise K-injective direct compositor with this same conjugate.
6. Specialize `lem-sf-projection-refinement-descent` to the continuous integral
   coefficient. It gives bounded constructibility of the displayed tensor input and
   invertibility of the native refinement at both inputs, without a Tor condition on K.
7. Apply `lem-sf-refinement-projection-counit`: its refinement is exactly the native
   clopen map and its projection is the proper counit followed by the open tensor
   comparison. This gives the directed square on arbitrary unbounded inputs.
8. Precompose by the tensor of the inverse refinement at K and postcompose by its
   inverse at the tensor input. Bifunctoriality and the inverse identities give the
   displayed equation. Neither a projection map nor a proper exchange is inverted.

The statement retains ordinary uncompleted tensor and pullback, the supplied proper
refinement without a Cartesian condition, and the zero and empty cases.
-/
theorem integralProjectionRefinementSquareNative
    (D₀ : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hlp : l ≠ D₀.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D₀.k))] [Y.Over (Spec (.of D₀.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D₀.k))]
    [QuasiCompact (X ↘ Spec (.of D₀.k))]
    [IsSeparated (X ↘ Spec (.of D₀.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D₀.k))]
    [QuasiCompact (Y ↘ Spec (.of D₀.k))]
    [IsSeparated (Y ↘ Spec (.of D₀.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D₀.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₁ c₂ : Compactification f) (u : c₁.Refinement c₂)
    (K : D (properOpenIntegralCoefficient l E) X)
    (L : D (properOpenIntegralCoefficient l E) Y)
    (hK : boundedConstructible
      (condensedRingObj (properOpenIntegralCoefficient l E) X) K)
    (hL : condensedConstructibleFiniteTor
      (properOpenIntegralCoefficient l E) Y L) :
    boundedConstructible
      (condensedRingObj (properOpenIntegralCoefficient l E) X)
      (K ⊗ (P (properOpenIntegralCoefficient l E) f).obj L) ∧
      IsIso ((refinement (properOpenIntegralCoefficient l E) u).app K) ∧
      IsIso ((refinement (properOpenIntegralCoefficient l E) u).app
        (K ⊗ (P (properOpenIntegralCoefficient l E) f).obj L)) ∧
      ∀ [hKiso : IsIso ((refinement (properOpenIntegralCoefficient l E) u).app K)]
        [hHiso : IsIso ((refinement (properOpenIntegralCoefficient l E) u).app
          (K ⊗ (P (properOpenIntegralCoefficient l E) f).obj L))],
        ((pf (properOpenIntegralCoefficient l E) c₁ K L ≫
            (@asIso _ _ _ _ ((refinement (properOpenIntegralCoefficient l E) u).app
              (K ⊗ (P (properOpenIntegralCoefficient l E) f).obj L)) hHiso).inv) =
          (((@asIso _ _ _ _ ((refinement (properOpenIntegralCoefficient l E) u).app K)
            hKiso).inv ⊗ₘ 𝟙 L) ≫ pf (properOpenIntegralCoefficient l E) c₂ K L)) := by
  sorry

end WeilConjectures
