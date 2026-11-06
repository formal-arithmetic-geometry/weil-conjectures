/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension

import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteQuotientSupportedClassicalWindow
import all WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientConstructible
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralPositiveReductionConstructible
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Supported cohomology of a finite integral reduction

Source: blueprint latest, `sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
the first two finite-reduction steps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- The continuous coefficient map, with both rings retained for dependent transport.
Source: actual quotient projection in the item node. -/
private def coefficientArrow (A B : Type u) [CommRing A] [CommRing B]
    (tA : TopologicalSpace A) (tB : TopologicalSpace B)
    (hA : @IsTopologicalRing A tA _) (hB : @IsTopologicalRing B tB _)
    (f : A →+* B) (hf : @Continuous A B tA tB f) :
    Arrow (Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :=
  letI := tA
  letI := tB
  letI := hA
  letI := hB
  letI := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A
  letI := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} B
  letI := Profinite.isMonHom_continuousMapRingObjMapOfUniverse.{u, u} f hf
  Arrow.mk (Mon.ofHom (Profinite.continuousMapRingObjMapOfUniverse f hf))

/-- Changing topologies by equality changes none of the bundled coefficient data. -/
private theorem coefficientArrow_eq (A B : Type u) [CommRing A] [CommRing B]
    (tA tA' : TopologicalSpace A) (tB tB' : TopologicalSpace B)
    (hA : @IsTopologicalRing A tA _) (hA' : @IsTopologicalRing A tA' _)
    (hB : @IsTopologicalRing B tB _) (hB' : @IsTopologicalRing B tB' _)
    (f : A →+* B) (hf : @Continuous A B tA tB f)
    (hf' : @Continuous A B tA' tB' f) (ha : tA = tA') (hb : tB = tB') :
    coefficientArrow A B tA tB hA hB f hf =
      coefficientArrow A B tA' tB' hA' hB' f hf' := by
  subst tA'
  subst tB'
  rfl

/-- The two norm presentations give the same actual positive quotient arrow.
Source: the spectral-norm coefficient comparison and the finite quotient calculation. -/
private theorem reductionArrow_eq (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    Arrow.mk (Mon.ofHom (DerivedNakayama.reductionRing l E (n + 1))) =
      Arrow.mk (Mon.ofHom (IntegralQuotient.reduction l E n)) := by
  have hm : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  have ht := congrArg (fun m : PseudoMetricSpace E ↦
    m.toUniformSpace.toTopologicalSpace) hm.symm
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  have hd : AdicCompletion.finiteTopology l E (n + 1) =
      IntegralQuotient.quotientTopology l E n := by
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let := FiniteModelQuotient.finiteTopology_discrete l E n
    exact DiscreteTopology.eq_bot
  exact coefficientArrow_eq _ _ _ _ _ _ _ _ _ _ _ _ _ hti hd

set_option synthInstance.maxHeartbeats 200000 in
-- The generalized coefficient arrow needs the exact module-derived functor instances.
set_option maxHeartbeats 1600000 in
-- Generalizing the coefficient arrow requires the module-derived category instances.
/-- The open restriction of supported sections of a finite reduction has cohomology
in `[-1,c+1]`, and its underlying cohomology sheaves are classical local torsion.

Source: blueprint latest, `sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
first two finite-reduction steps; Stacks Tags 0A45, 09B1 and 09AA.
(blueprint: lem-sfb-integral-stratum-finite-cd-reductions-support-window).

Proof: use the length-one uniformizer resolution to identify the scalar restriction
of the positive quotient reduction with the cone of the uniformizer power on N[0].
Its cohomology is the kernel in degree -1 and the cokernel in degree 0. Positive
reduction constructibility and finite-coefficient comparison show these sheaves
are classical, even when N has torsion. Identify the continuous integral and quotient
coefficient presentations with those of the supported-window theorem, transporting
the reduction map and restriction functor as well. The unit assumption on ell gives
invertibility in every residue field. Apply finite_quotient_supported_classical_window
with a=-1, b=0 and exponent n+1. It gives the claimed bound and classical local torsion
before restriction to S. Exact open inverse image commutes with homology; the
etale/pro-etale inverse-image comparison preserves classicality, and inverse image
preserves the filtered union of prime-power kernels. This gives both conclusions
on S. Zero N and empty strata give zero complexes, so require no extra hypotheses. -/

end CategoryTheory
