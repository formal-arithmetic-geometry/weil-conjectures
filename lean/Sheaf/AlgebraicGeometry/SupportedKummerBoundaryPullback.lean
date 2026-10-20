/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem
import Sheaf.AlgebraicGeometry.SupportedKummerCartierPullback
import Sheaf.AlgebraicGeometry.RelativeTorsorCohomology
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Sheaf.AlgebraicGeometry.PullbackConstantModule

/-!
# Cartier pullback of the supported Kummer boundary

Source: blueprint lem-amb-cartier-kummer-map; Stacks 03PL and 0A45
(blueprint: lem-asd-supported-kummer-boundary-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

-- Match the stored instances of the boundary and scalar interfaces.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2


/-- Cartier pullback preserves the normalized supported Kummer class, with the
canonical closed exchange and any roots-normalized twist transport.
Source: Stacks 03PL, 0A45; blueprint lem-amb-cartier-kummer-map, penultimate paragraph
(blueprint: lem-asd-supported-kummer-boundary-pullback).

Proof: pull the dual Cartier ideal and its canonical section back. Since the new
ideal is again Cartier, the canonical comparison with its dual is an isomorphism,
including the specified frame on the complement. Naturality of the relative torsor
class and the Kummer connecting map identifies the two relative boundaries. The
module/abelian comparisons commute with inverse image on both the scheme and its
open complement. The supported-Hom comparison transports this equality to Ext.
The normalized roots and pure tensor equations identify
the target comparison with the line component of t. These normalizations also cover
N = 1, when the coefficient line is zero. No flatness of the base map is needed. -/
theorem supported_kummer_boundary_pullback (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) {D : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2)
    (hκ : SupportedKummerBoundary A N hA i hI hT κ)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {D' T' : Scheme.{u}} (i' : D' ⟶ T') [IsClosedImmersion i']
    (v : T' ⟶ T) (w : D' ⟶ D) (sq : IsPullback w i' i v)
    (hI' : i'.ker.IsInvertible)
    (κ' : Ext ((lowerStar (ModuleCat.{u + 1} A) i').obj (ordinaryFiniteConstant A D'))
      (Scheme.finiteEtaleTateLine T' N A hA) 2)
    (hκ' : SupportedKummerBoundary A N hA i' hI'
      (by simpa using hT.map v.appTop.hom) κ') :
    (Ext.mk₀ (supportedConstantExchange A i i' v w sq.toCommSq)).comp κ' (zero_add 2) =
        (κ.mapExactFunctor (upperStar (ModuleCat.{u + 1} A) v)).comp
          (Ext.mk₀ (t.line v hT).hom) (add_zero 2) := by
  sorry

end AlgebraicGeometry.Etale
