/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Finite-reduction vanishing for a lisse integral module on an affine curve

Source: latest blueprint lem-a1-affine-hc0.proof.md, finite-level support argument.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- At each positive finite reduction, the compact image of a lisse integral sheaf
has zero cohomology in degrees -1 and 0. No rational sheaf or Weil structure is used.

Source: latest blueprint lem-a1-affine-hc0.proof.md, paragraph 2 and the preceding
assertion that negative cohomology vanishes
(blueprint: lem-a1-lattice-reduction-vanishing).

Proof: a locally finite free integral module is flat. Its derived quotient modulo
pi^(n+1) is therefore its ordinary quotient in degree zero, a finite locally constant
module. The finite coefficient correspondence realizes this quotient on the etale site.
Scalar-six compares the derived quotient of the actual compact image with the compact
image of this quotient. Compute that image using the canonical etale compact-support
comparison as R-Gamma of extension by zero on a compactification. A nonnegative
injective resolution gives H^(-1)=0 and identifies H^0 with sections of extension by
zero. The proper-support range theorem injects these into sections on U whose closed
support is proper over the base field. Faithfulness of a geometric stalk on finite
locally constant sheaves over connected U shows a section vanishing at one point is
zero; thus a nonzero section has full support. Smoothness implies U is reduced, so
its full closed support is U. But U is nonproper: field extension preserves dimension,
and a proper affine curve would be finite over the field and have dimension zero,
contradicting pure dimension one and nonemptiness. Hence H^0=0. Transport the two
vanishings through the scalar and site comparisons and exact restriction from the
finite quotient coefficient ring, as used in AdicCompletion.integralLevel. -/
theorem curveLatticeReductionVanishing
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (U₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    [Smooth U₀.hom] [IsAffine U₀.left] [Nonempty U₀.left]
    (hDim : U₀.left.IsPureDimension 1)
    (hConnected : ConnectedSpace (D.geometricFiber U₀).left)
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (L : AdicCompletion.Modules ell E (D.geometricFiber U₀).left)
    (hL : CondensedRing.LocallyFree
      (AdicCompletion.ring ell E (D.geometricFiber U₀).left) L)
    (c : Compactification (D.geometricFiber U₀).hom) :
    ∀ n : ℕ,
      IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj
        (AdicCompletion.integralLevel ell E (Spec (.of D.k))
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (DerivedNakayama.integerRing ell E) c).obj
              ((DerivedCategory.singleFunctor _ 0).obj L)) n)) ∧
      IsZero ((DerivedCategory.homologyFunctor _ 0).obj
        (AdicCompletion.integralLevel ell E (Spec (.of D.k))
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (DerivedNakayama.integerRing ell E) c).obj
              ((DerivedCategory.singleFunctor _ 0).obj L)) n)) := by
  sorry

end WeilConjectures
