/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.ZMod.Basic
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.SixFunctors.Finite.BaseChange
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.ExchangeIdentityPasting
import Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.FiniteBoundaryReconstruction
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.ChowLemma.ClosedModel
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import Sheaf.AlgebraicGeometry.ProperStability
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.OpenClosedRecollement
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import Sheaf.AlgebraicGeometry.CoordinateGenericDimension
import Sheaf.AlgebraicGeometry.FiniteBoundaryComparison
import Sheaf.AlgebraicGeometry.FiniteGenericRadicialSmoothing
import Sheaf.AlgebraicGeometry.FiniteRadicialExchangeDescent
import Sheaf.AlgebraicGeometry.ProjectiveCoordinateBoundary
import Sheaf.AlgebraicGeometry.SmoothGenericDirectImage
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful

/-!
# Generic bounded constructibility for an open immersion

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`thm-fin-deligne-generic-open.md` (blueprint: thm-fin-deligne-generic-open).

Base changes are expressed using arbitrary Cartesian presentations. The two pullback
squares over `U` present `Y_U` and `X_U`; the two squares over `T` present `Y_T` and `X_T`.
The coefficient ring is the canonical universe lift of the prime field.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Generic bounded constructibility and universal Noetherian base change for an open
immersion and a constructible prime-field sheaf.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/thm-fin-deligne-generic-open.md`
(blueprint: thm-fin-deligne-generic-open).

Proof plan (the eight steps of the node):
1. Shrink to an affine base. Finite type implies Noetherianity. Exact module inverse image
   and exchange after forgetting coefficients reduce locality to the abelian-sheaf case.
   Etale restriction preserves injectives, so finite open target covers detect all claims.
2. Induct on generic source dimension, extending the assertion to immersions by their
   open/closed factorization and finite exchange. Replace the target by schematic closure.
   Remove vertical components; an empty generic source or dimension zero reduces to an
   identity immersion after shrinking, using finite discreteness in dimension zero.
3. For a projective target use affine coordinates and the lower-dimensional assertion.
   The coordinate dimension lemma and projective boundary lemma give a good open whose
   reduced complement is finite over a smaller base.
4. For a smooth source and finite locally constant sheaf take a projective closed model.
   Smooth generic direct image and composition bound its total direct image; finite
   boundary reconstruction now proves bounded constructibility of the open direct image.
5. Proper base change and vertical pasting make the pushed-forward exchange invertible.
   Finite boundary comparison makes the actual exchange invertible over every Noetherian
   test scheme, without assuming constructibility of its target.
6. For a general sheaf use generic radicial smoothing. Universal-homeomorphism invariance
   permits reductions. Apply the smooth case to the dense smooth open and its composite.
   The cone of the unit is bounded constructible by the Serre property and the cohomology
   sequence, and open/closed recollement identifies it with a closed-supported complex.
7. Apply lower-dimensional induction to its finitely many cohomology sheaves. Truncation
   triangles, triangulated direct image and exchange, composition and pasting give both
   assertions for this cone. The unit triangle then gives both assertions for the sheaf.
8. A finite radicial surjection is a closed homeomorphism. The closed image of the bad
   complement misses the generic point; its complement is a nonempty base open whose full
   inverse image is good. Radicial exchange descent gives both claims on that open.
-/
theorem exists_nonempty_open_isBoundedConstructible_derived_open_pushforward
    (k : Type u) [Field k] (S : Scheme.{u}) [IsIntegral S]
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k)
    (X Y : Scheme.{u}) (aX : X ⟶ S) (aY : Y ⟶ S)
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : X ⟶ Y) [IsOpenImmersion j] (hj : j ≫ aY = aX)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    ∃ U : S.Opens, Nonempty U ∧
      ∀ (XU YU : Scheme.{u}) (pX : XU ⟶ X) (pY : YU ⟶ Y)
        (bU : YU ⟶ U.toScheme) (jU : XU ⟶ YU),
        IsPullback pY bU aY U.ι →
        IsPullback pX jU j pY →
        DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) YU
          ((R((jU)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
            ((L((pX)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ∧
        ∀ (T : Scheme.{u}) [IsNoetherian T] (t : T ⟶ U.toScheme)
          (XT YT : Scheme.{u}) (qX : XT ⟶ XU) (qY : YT ⟶ YU)
          (bT : YT ⟶ T) (jT : XT ⟶ YT),
          IsPullback qY bT bU t →
          ∀ sq : IsPullback qX jT jU qY,
            IsIso ((derivedBaseChangeMap
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) sq.toCommSq).app
                ((L((pX)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
                  ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
  sorry

end AlgebraicGeometry.Etale
