/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.CondensedConventions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeGeometricFourier.NativeGeometricFourierModel
public import WeilConjectures.AlgebraicGeometry.DualBundlePairing
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedRealified.CondensedRealifiedKernel
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Fourier transform of the boundary sequence

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-a1/sec-purity-of-the-lisse-part-of-the-fourier-transform/
sk-p-dl-a1-correction/_section.md, sk-p-dl-a1-correction.proof.md and
prop-fd-zero-extension-comparison.md
(blueprint: sk-p-dl-a1-correction).
All sheaves are actual condensed modules with geometric-Frobenius structure.
The extension by zero is the existing canonical mate construction. Its map to
the ordinary middle image is specified by its identity restriction under the
two adjunctions. The boundary is its cokernel in Weil modules, so its Frobenius
is the induced quotient structure.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2.BoundaryCorrection
open AlgebraicGeometry.CondensedOrigin
open AlgebraicGeometry.ProEtale.CondensedRing

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]

/-- The structure projection of the arithmetic affine line, as an Over morphism.
Source: def-fd-transform, affine-line specialization (blueprint: sk-p-dl-a1-correction). -/
def lineProjection : model D ⟶ Over.mk (𝟙 (Spec (.of D.k₀))) :=
  Over.homMk (model D).hom (Category.comp_id _)

variable {X₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- A Weil module in degree zero, via the existing canonical ambient realization.
Source: rem-dl-a1-conventions, sheaves as complexes
(blueprint: sk-p-dl-a1-correction). -/
@[irreducible] def singlePair (M : WeilModule D l X₀) :
    Endofunctor.IsoAlgebra
      (StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
        (StrictWeilCondensed.modelFrobenius D X₀)) :=
  (StrictWeilCondensed.ambientComparison (Profinite.padicAlgClRingObj l)
    (StrictWeilCondensed.modelFrobenius D X₀)).obj ((DerivedCategory.singleFunctor _ 0).obj M)

/-- Shift the complex and its structure using the specified shift comparison.
Source: def-fd-transform, shift convention (blueprint: sk-p-dl-a1-correction). -/
@[irreducible] def shiftedPair
    (K : Endofunctor.IsoAlgebra
      (StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
        (StrictWeilCondensed.modelFrobenius D X₀)))
    (n : ℤ) : Endofunctor.IsoAlgebra
      (StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
        (StrictWeilCondensed.modelFrobenius D X₀)) :=
  Endofunctor.IsoAlgebra.mk ((shiftFunctor _ n).obj K.carrier)
    (((StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
      (StrictWeilCondensed.modelFrobenius D X₀)).commShiftIso n).app K.carrier ≪≫
        (shiftFunctor _ n).mapIso K.str)

/-- The normalized affine-line transform and its canonical arithmetic descent datum.
No independent functor or Frobenius lift is supplied as a hypothesis.
Source: def-fd-transform and its Weil convention
(blueprint: sk-p-dl-a1-correction). -/
@[irreducible] def fourierPair
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj.{u} l)))
    (c : Compactification (pullback.snd (lineProjection D).left (lineProjection D).left))
    (K : Endofunctor.IsoAlgebra
      (StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
        (StrictWeilCondensed.modelFrobenius D (model D)))) :
    Endofunctor.IsoAlgebra
      (StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
        (StrictWeilCondensed.modelFrobenius D (model D))) :=
  Endofunctor.IsoAlgebra.mk
    ((NativeGeometricFourier.transform D (Profinite.padicAlgClRingObj l)
      (lineProjection D) (lineProjection D) ψ
      (AffineSpace.stdPairing PUnit (Spec (.of D.k₀))) c 1).obj K.carrier)
    (NativeGeometricFourier.transformDatum D (Profinite.padicAlgClRingObj l)
      (lineProjection D) (lineProjection D) ψ
      (AffineSpace.stdPairing PUnit (Spec (.of D.k₀))) c 1 K.carrier K.str)

set_option maxHeartbeats 1000000 in
-- The signature includes the actual coefficient-module Fourier and Frobenius comparisons.
end WeilConjectures.NativeL2.BoundaryCorrection
