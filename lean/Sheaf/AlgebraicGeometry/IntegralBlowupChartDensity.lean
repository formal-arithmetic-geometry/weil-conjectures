/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Compactification.StrictTransformChartModel
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Mathlib.AlgebraicGeometry.Gluing
import Sheaf.AlgebraicGeometry.PrincipalOpenDenseOfNonZeroDivisor
import WeilConjectures.AlgebraicGeometry.IntegralIdealGenericStalk
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Blowup.Affine.Localization

/-! # Integral blowup charts and density of the center complement

Source: Stacks Project, Algebra, Tags 052R and 07Z3; Divisors, Tags 02ND and 0804
(blueprint: lem-sfb-integral-blowup-chart-density).

The ideal-sheaf datum encodes a quasi-coherent ideal. Its support is the closed locus
where the stalk ideal is proper. The affine comparison is expressed by the canonical
open embedding and its cartesian square, so it identifies open subschemes over the base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Integral blowup charts and their dense principal center complements.

Source: Stacks Project, Algebra, Tags 052R and 07Z3; Divisors, Tags 02ND and 0804
(blueprint: lem-sfb-integral-blowup-chart-density).

Proof:
1. Apply lem-weil-pbc-integral-scheme-ideal-generic-stalk to the nonzero ideal:
   its sections on every nonempty affine open are nonzero, and its generic stalk is
   the whole generic local ring.
2. By lem-weil-pbc-quasi-coherent-ideal-zero-set-affine the proper-stalk locus is
   closed. Its complement contains the generic point, hence is nonempty and dense.
   Its nonempty affine opens have domain section rings, so it is integral.
3. The gluing of def-nagata-global-blowup-glue-data identifies the affine local model
   with the inverse image of each affine open: a point represented on another piece
   lies in their prescribed overlap. Use prop-nagata-global-blowup-cover-independent,
   def-nagata-global-blowup-local-model and lem-weil-pbc-glue-schemes.
4. On smaller affine opens, prop-nagata-affine-blowup-restrict and
   def-nagata-global-blowup-overlap-basic-map identify both comparisons on common
   basic refinements. The uniqueness in lem-weil-pbc-scheme-morphism-gluing gives
   equality everywhere, namely naturality of the canonical embeddings.
5. By lem-weil-pbc-quasi-coherent-finite-type-affine the affine ideal is finitely
   generated. For any chosen generators, prop-nagata-affine-blowup-chart-cover and
   prop-nagata-affine-blowup-chart give the finite affine cover, with chart ring
   def-nagata-blowup-chart-ring and its canonical algebra structure map.
6. A zero generator localizes at zero, giving the zero chart ring and empty spectrum.
7. A nonzero generator localizes a domain to a nonzero domain. Its unital subalgebra
   A[I/a] is a nonzero domain and the image of a is nonzero (Tag 052R).
8. In A[I/a], each generator f_j equals a*(f_j/a), so the extended ideal is (a).
   By lem-weil-pbc-quasi-coherent-ideal-zero-set-affine and def-weil-affine-spectrum,
   the inverse image of the center complement is precisely the principal open D(a).
   Equality of these opens identifies their restricted structure sheaves as well.
9. The principal open is dense by lem-pc-principal-open-dense-of-nonzerodivisor;
   it is nonempty since the zero prime avoids a. Since the affine ideal is nonzero,
   some chosen generator is nonzero, so a nonempty chart occurs. -/
theorem integral_blowup_chart_density
    {T : Scheme.{u}} [IsIntegral T] (I : T.IdealSheafData)
    (hI : I ≠ ⊥) (hfinite : I.toModules.IsFiniteType) :
    Nonempty I.support.compl ∧
    Dense (I.support.compl : Set T) ∧
    IsIntegral (Scheme.Opens.toScheme (X := T) I.support.compl) ∧
    ∀ (V : T.affineOpens), Nonempty V.1 →
      I.ideal V ≠ ⊥ ∧
      IsPullback (I.blowupNatTrans.app V) (I.blowupι V) V.1.ι I.blowupMap ∧
      I.blowupMap ⁻¹ᵁ V.1 = (I.blowupι V).opensRange ∧
      (∀ (W : T.affineOpens) (hWV : W ≤ V),
        I.blowupFunctor.map (homOfLE hWV) ≫ I.blowupι V = I.blowupι W) ∧
      ∀ (r : ℕ) (f : Fin (r + 1) → I.ideal V),
        Ideal.span (Set.range fun i ↦ (f i : Γ(T, V.1))) = I.ideal V →
        (⨆ i, (AffineBlowup.chartRingι (I.ideal V) (f i).2).opensRange) = ⊤ ∧
        (∀ i : Fin (r + 1),
          AffineBlowup.chartRingι (I.ideal V) (f i).2 ≫
              AffineBlowup.toSpec (I.ideal V) =
            Spec.map (CommRingCat.ofHom
              (algebraMap Γ(T, V.1) (AffineBlowup.chartRing (I.ideal V) (f i))))) ∧
        (∀ i : Fin (r + 1),
          ((f i : Γ(T, V.1)) = 0 →
            IsEmpty (Spec (.of (AffineBlowup.chartRing (I.ideal V) (f i))))) ∧
          ((f i : Γ(T, V.1)) ≠ 0 →
            IsDomain (AffineBlowup.chartRing (I.ideal V) (f i)) ∧
            (AffineBlowup.chartRingι (I.ideal V) (f i).2 ≫ I.blowupι V) ⁻¹ᵁ
                (I.blowupMap ⁻¹ᵁ I.support.compl) =
              PrimeSpectrum.basicOpen
                (algebraMap Γ(T, V.1) (AffineBlowup.chartRing (I.ideal V) (f i)) (f i)) ∧
            (PrimeSpectrum.basicOpen
              (algebraMap Γ(T, V.1) (AffineBlowup.chartRing (I.ideal V) (f i)) (f i)) :
                Set (PrimeSpectrum (AffineBlowup.chartRing (I.ideal V) (f i)))).Nonempty ∧
            Dense (PrimeSpectrum.basicOpen
              (algebraMap Γ(T, V.1) (AffineBlowup.chartRing (I.ideal V) (f i)) (f i)) :
                Set (PrimeSpectrum (AffineBlowup.chartRing (I.ideal V) (f i)))))) ∧
        (∃ i : Fin (r + 1), (f i : Γ(T, V.1)) ≠ 0 ∧
          Nonempty (Spec (.of (AffineBlowup.chartRing (I.ideal V) (f i))))) := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
