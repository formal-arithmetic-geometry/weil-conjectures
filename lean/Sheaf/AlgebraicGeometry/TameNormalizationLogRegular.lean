/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.NormalScheme
public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import Sheaf.AlgebraicGeometry.UnramifiedFieldFibreDecomposition
import Sheaf.AlgebraicGeometry.FiniteEtaleDescentDataExistence
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.TraceFormula.LogRegularDivisorialStructure
import WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Sheaf.AlgebraicGeometry.InvertibleKummerChartLogRegular
import Sheaf.AlgebraicGeometry.PrimeToOrderSNCKummerCharts
import Sheaf.AlgebraicGeometry.RegularBoundaryDivisorialChart

/-!
# Log regularity of tame normalization over a regular boundary

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé IX, Proposition 2.1(i)--(iii)
and paragraph 2.2, printed pp. 133--134; Exposé VI, 1.8 and 2.3, printed pp. 70 and 73
(blueprint: lem-per-tame-normalization-log-regular).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Normalization in the function field of a connected finite étale torsor of invertible
order over the complement of a strict normal crossings boundary is finite, integral,
excellent and Noetherian, and its inverse-image boundary is log regular. The integral
structure of the cover and its function-field algebra are conclusions, not assumptions.
The equality of generic morphisms specifies the algebra induced by the cover. The dense
open used by the pair predicate is exactly the inverse image of the boundary complement.

Source: ILO, Exposé IX, Proposition 2.1(i)--(iii) and paragraph 2.2, pp. 133--134;
Exposé VI, 1.8 and 2.3, pp. 70 and 73
(blueprint: lem-per-tame-normalization-log-regular).

Proof plan:
1. The Cartier boundary misses the generic point, so its complement is nonempty, normal
   and Noetherian (rem-pc-regular-normal). The cover is Noetherian by finite type over a
   Noetherian scheme (lem-weil-pbc-finite-type-over-noetherian). Its clopen normal integral
   decomposition (lem-fin-etale-normal-components), connectedness and surjectivity make
   it integral. Base change to the generic point (lem-galois-descent-data-existence) gives
   a finite étale domain over the base function field, hence a finite separable field by
   lem-trf-unramified-field-fibre-decomposition and def-weil-etale-morphism. Its structural
   algebra is characterized by the displayed equality of generic morphisms.
2. Glue integral closures in that field (def-fin-normalization-extension). On every
   affine normal Noetherian domain, integral closure in the finite separable extension
   is finite (lem-weil-pbc-noetherian-normal-separable-integral-closure-finite), giving
   finiteness of the canonical map (def-weil-finite-integral-morphism). Generic
   normalization is integral (lem-weil-pbc-normalization-in-residue-field-extension).
   Finite-type stability and localization preserve excellence
   (lem-exc-finite-type-localization-excellent), and finite type over Noetherian gives
   Noetherianity of the normalization (lem-weil-pbc-finite-type-over-noetherian).
3. The regular boundary has a fine saturated divisorial log structure, log regular
   with triviality locus its complement (lem-per-regular-boundary-divisorial-chart).
4. The invertible-order torsor gives compatible injective Kummer characteristic charts
   on the finite normalization, with finite group cokernel of invertible exponent and
   étale scheme comparison (lem-per-prime-to-order-snc-kummer-charts).
5. These charts preserve log regularity (lem-per-invertible-kummer-chart-log-regular).
   The torsion-free-cokernel criterion is not applicable to nontrivial Kummer roots.
6. In an injective Kummer map of sharp monoids P → Q, Q = 0 implies P = 0. Conversely,
   P = 0 forces every q to have a positive multiple zero, hence to be a unit, hence zero
   by sharpness. Thus the source triviality locus is exactly the inverse-image open.
   Divisorial recovery (lem-trf-log-regular-divisorial-structure) identifies its log
   structure with that of the required pair (def-trf-log-regular-pair). This includes
   the empty boundary, for which both characteristic monoids are zero everywhere. -/
theorem tame_normalization_log_regular
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (hExcellent : ∀ W : Y.affineOpens, IsExcellent Γ(Y, W))
    (hRegular : IsRegularScheme Y) (T : Y.IdealSheafData)
    (hT : IsStrictNormalCrossingsBoundary T)
    (G : Type v) [Group G] [Finite G] (hG : IsUnit (Nat.card G : Γ(Y, ⊤)))
    (C : Scheme.GaloisCoverAction G (Scheme.Opens.toScheme T.support.compl))
    [ConnectedSpace C.Z] :
    ∃ (_ : IsIntegral C.Z) (_ : Algebra Y.functionField C.Z.functionField),
      Y.fromSpecOfAlgebraFunctionField C.Z.functionField =
        C.Z.fromSpecFunctionField ≫ C.π ≫ Scheme.Opens.ι T.support.compl ∧
      IsFinite (Y.fromNormalizationIn C.Z.functionField) ∧
      IsIntegral (Y.normalizationIn C.Z.functionField) ∧
      (∀ W : (Y.normalizationIn C.Z.functionField).affineOpens,
        IsExcellent Γ(Y.normalizationIn C.Z.functionField, W)) ∧
      ∃ (_ : IsNoetherian (Y.normalizationIn C.Z.functionField))
        (hU : DenseRange
          (Scheme.Opens.ι ((Y.fromNormalizationIn C.Z.functionField) ⁻¹ᵁ T.support.compl))),
        IsDivisorialFineSaturatedLogRegularPair
          (Y.normalizationIn C.Z.functionField)
          (Scheme.Opens.toScheme
            ((Y.fromNormalizationIn C.Z.functionField) ⁻¹ᵁ T.support.compl))
          (Scheme.Opens.ι ((Y.fromNormalizationIn C.Z.functionField) ⁻¹ᵁ T.support.compl)) hU := by
  sorry

end AlgebraicGeometry.Scheme
