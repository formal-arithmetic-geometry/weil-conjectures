/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPullback.NativeCondensedPullbackFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.DeligneLaumon.CondensedClopenCompact.CondensedClopenCompactDecomposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ModelSemilinearComparison.CondensedModelFrobeniusOperatorsBase
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.CondensedLisseExtensionInertia.CondensedLisseExtensionInertia

/-! # The compact-support constant-field Frobenius comparison

This is the cohomological step after the geometric fibre identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.MonObj AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures

/-- The canonical compact-support comparison intertwines extension Frobenius with
positive powers of the original Frobenius.
Source: latest blueprint, sk-lem-wft-infinity-reduction, opening proof paragraph
(blueprint: lem-wft-infinity-constant-extension-comparison).

Proof: identify the geometric fibres by fibre-product associativity. Choose a Nagata
compactification over the finite base; base change it to the extension and to the
fixed algebraic closure. The geometric fibre isomorphism conjugates the extension
Frobenius to the m-th power. Use the canonical proper and open exchange maps and
terminal-section insertion to compare compact-support complexes. The exchange
cocycle and naturality identify transport for the composite with ordered iterated
transport. The prescribed extension structure is the ordered iterate of the original
Weil structure. The natural-transport power formula therefore identifies the composite
endomorphism with the m-th power of the original one. Normalize comparisons between
the given compactifications through their common refinement; refinement independence
and the exchange pasting equations preserve this identity. Apply homology in degree r,
which preserves composition and isomorphisms. This yields the displayed intertwining
identity for the actual two GlobalGeometricFrobenius operators. No eigenvalue or weight
bound is used. For m = 1 this is compactification independence; the zero cohomology
object causes no exception. -/
theorem infinity_constant_extension_comparison
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ WeilCoefficient.qbar)
    (r : ℤ) (m : ℕ) (hm : 1 ≤ m)
    (E : ConstantExtensionData D ell hEll X₀ c₀ K r m hm)
    [IsIso (constantExtensionGeometricMap D m hm X₀
      (infinityConstantExtensionModel D m hm X₀)
      (infinityConstantExtensionProjection D m hm X₀))] :
    ∃ e : compactCohomology D ell hEll X₀ c₀ K r ≅
        compactCohomology (NativeCondensedPullback.constantExtensionDatum D m hm)
          ell hEll (infinityConstantExtensionModel D m hm X₀) E.cₘ E.Kₘ r,
      ModuleCat.ofHom
          ((compactFrobenius D ell hEll X₀ WeilCoefficient.qbar c₀ K r).hom ^ m) ≫
          e.hom = e.hom ≫ E.extensionFrobenius := by sorry

end WeilConjectures
