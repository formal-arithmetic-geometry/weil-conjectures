/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Compact degree zero of an ordinary middle image

Source: current blueprint, lem-wf-euler-product-middle-extension.proof.md,
second paragraph. This is a statement about the actual geometric coefficient module;
it requires neither a Weil structure nor a complex embedding.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures

/-- The ordinary direct image of a lisse module from a dense open of a smooth
geometrically connected affine curve has zero compact cohomology in degree zero.

Proof: choose a smooth proper compactification k of the geometric curve, with
finite nonempty boundary. Put G = j_*M. The canonical map alpha : k_!G ->
k_*G = (kj)_*M is injective. Both sides are constructible by stability of
constructibility under direct image and extension by zero; their kernel is
constructible by the coefficient-heart theorem. Geometric-point evaluation is
exact: pullback to the point is exact, and terminal sections over the algebraically
closed point are exact. At a point in the curve alpha is the identity after
restriction; at a boundary point its source is zero. Its kernel therefore has
zero geometric stalks. Use the coefficient-heart finite lisse filtration and
lisse-stalk vanishing, inductively along the filtration, to conclude that the
kernel is zero. Thus a compactly supported section of G injects into a section
of (kj)_*M, hence into a global section of M on U. The representation equivalence
identifies the latter with a fundamental-group invariant vector v of the
geometric generic stalk. Its germ at a boundary point is v inside the inertia
invariants, by the boundary-stalk theorem. A section extended by zero has zero
boundary germ, so v is zero. Every compact section is consequently zero. The
degree-zero derived/ordinary compact-cohomology comparison gives the displayed
zero object. Independence of compactification transports this conclusion from
the smooth compactification to the arbitrary presentation c.
The zero coefficient module and the identity open immersion satisfy the same
argument. No choice of Weil structure, Frobenius operator or scalar embedding is used.
Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
  sec-purity-real-sheaves/sec-weights-at-the-boundary-points/sk-p-real-semi/
  lem-wf-euler-product-middle-extension.proof.md, second paragraph
(blueprint: lem-wf-middle-image-compact-zero). -/
theorem isZero_middleImage_compact_zero
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    {U₀ X₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [SmoothOfRelativeDimension 1 X₀.hom]
    [GeometricallyConnected X₀.hom] [IsAffine X₀.left]
    (j : U₀ ⟶ X₀) [IsOpenImmersion j.left] [IsDominant j.left]
    (M : Mod (Sheaf (Scheme.ProEt.topology (D.geometricFiber U₀).left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (D.geometricFiber U₀).left))
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M)
    (c : Compactification (D.geometricFiber X₀).hom) :
    IsZero ((CondensedRing.condensedRingCompactCohomology
      (Profinite.padicAlgClRingObj ell) c 0).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((NativeL2.middleImage D ell j).obj M))) := by
  sorry

end WeilConjectures
