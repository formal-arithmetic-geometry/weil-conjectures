/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartGeneralStatement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Cohomological range of an affine curve

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/`
`sec-fourier-transform/sec-perverse-t-exactness-of-the-fourier-transform/`
`sk-l-dl-a1-endpoints/lem-zl-affine-curve-range.md`, statement
(order 4206) (blueprint: lem-zl-affine-curve-range).

The coefficient is the actual pulled-back condensed Qbar-ell module with its
native Weil fixed-pair structure.  Compact support is the recorded ordinary
condensed construction `condensedQbarCompactSections`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

/-- Compact-support cohomology of a constructible coefficient sheaf on a smooth
affine curve is concentrated in degrees `0`, `1`, and `2`.

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/`
`sec-fourier-transform/sec-perverse-t-exactness-of-the-fourier-transform/`
`sk-l-dl-a1-endpoints/lem-zl-affine-curve-range.md`, statement (order 4206)
(blueprint: lem-zl-affine-curve-range).
The proof is postponed and follows the source's ten steps:
(1) forget the fixed-pair Weil structure, base-change the smooth relative
    dimension-one curve, and decompose the affine curve into finitely many
    connected components, with the empty case included;
(2) descend each component's constructible coefficient to a finite extension
    and use scalar comparison for compact support;
(3) shrink to the lisse stratum and deviss the finite zero-dimensional
    complement, choosing integral lattices on both pieces;
(4) reduce the lattices modulo powers of a uniformizer, retaining the
    quotient transition maps and degree-zero finite-Tor models;
(5) compute finite-level compact support on a proper compactification by
    open extension and etale comparison, obtaining the upper bound two and
    finiteness;
(6) treat the finite complement by its identity compactification, obtaining
    only degree zero and no negative degrees by bounded-below injective
    resolutions;
(7) apply constructible stability and the integral criterion to derived
    complete the compact-support complex and compare it with the inverse
    limit of the finite levels after exact point evaluation;
(8) use the Mittag--Leffler assertion for finite cohomology groups to pass the
    range through the derived limit, including the possible degree-three edge;
(9) invert the uniformizer and extend scalars to `\overline{\mathbf Q}_ell`,
    using flatness and scalar comparison;
(10) apply the open--closed distinguished triangle on each component and
    assemble the finitely many components inductively.  The hypotheses and
    conclusion are exactly the condensed coefficient and ordinary compact
    cohomology notions of the statement; the heart closure used in the
    construction is the recorded `coefficientHeartGeneralStatement`, and the
    Weil pair is the native Weil module `condensedWeilModules` (equal to
    `StrictWeilCondensed.WeilModule` and to `weilSheafModuleCategory` for
    `\overline{\mathbf Q}_ell`).
-/
theorem affineCurve_compactSupport_range
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p)
    (C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
    [IsAffine C₀.left] [SmoothOfRelativeDimension 1 C₀.hom]
    (F : condensedWeilModules (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius C₀).hom)
    (hF : IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
      (D.geometricFiber C₀).left F.carrier)
    (c : Compactification (D.geometricFiber C₀).hom) :
    ∀ i : ℤ, i ∉ ({0, 1, 2} : Set ℤ) →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (PadicAlgCl ell)) i).obj
        ((condensedQbarCompactSections ell D.k c).obj
          ((DerivedCategory.singleFunctor _ 0).obj F.carrier))) := by
  sorry

end WeilConjectures
