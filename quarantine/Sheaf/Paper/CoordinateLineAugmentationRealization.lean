/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G9
-/
module

public import Sheaf.Paper.CoordinateLineAdjunctionMaps

/-! # Realization of the coordinate-line augmentation

Source: current blueprint, sk-prop-an, coordinate-line proof
(blueprint: lem-pur-coordinate-line-augmentation-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CoordinateLine
open AffineLinePurity VectorIntegrationSite
/-- The actual affine augmentation is the realization of the composite ordinary counit.
Source: current blueprint, final site-comparison paragraph of
cor-pur-affine-space-zero-section-purity.proof.md
(blueprint: lem-pur-coordinate-line-augmentation-realization).

Proof: expand the standard compactification comparison into exact open extension
comparison and the specified proper direct-image mate. The open counit comparison
and projectiveComparison's trace equation identify the restricted trace with
comparison of Rq*(e_V) followed by t_q. The tensor/exchange square for the proper
mate and the open projection square identify the canonical projections, including
pullback composition. Both projections are invertible on the stated finite-Tor
input. Invert that square, tensor the trace equation and use the unit-normalized
monoidal comparison (siteTensorUnitEvaluation). This gives comparison of the
ordinary inverse-projection
trace composite. The ordinary counit tensor formula identifies it with the actual
composite counit. Naturality transports from comparison of Ke to K along eK.
The retained sourceCoordinates and sourceComparison are precisely the coordinate
maps of these squares. The fixed and canonical compactification comparisons agree
by their identical exact open map and proper counit mate; expanding their inclusion
comparisons cancels the intervening identities. All inputs to the proper mate are
bounded below by etaleSource_plus. Empty schemes and zero coefficients are included. -/
theorem coordinate_line_augmentation_realization
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] [IsNoetherian T]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj) :
    (fixedCompactSupportComparisonIso (Ring P)
        (affineTraceLineCompactification T)).inv.app
      ⟨etaleSource P.coefficients.l P.extension (P.level - 1) T r hA Ke,
        etaleSource_plus P.coefficients.l P.extension (P.level - 1) T r hA Ke hKe⟩ ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
      (affineTraceLineCompactification T)).map
        (sourceComparison P.coefficients.l P.extension (P.level - 1) T r hA
          K.obj Ke eK).hom ≫
    augmentation P.coefficients.l P.extension (P.level - 1) T r hA
      (primeUnit P T aT) P.field.k aT K.obj Ke hKe eK =
    (VectorIntegrationSite.comparison (Ring P) T).map
      ((Etale.affineTraceLineLeft (Ring P) T).map (sourceCoordinates P T r hA Ke).hom ≫
        (adjunction (Ring P) (P.coefficients.l ^ (r + 1)) hA T
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
          (by simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r + 1))).counit.app Ke) ≫
      eK.hom := by
  sorry

end AlgebraicGeometry.ProEtale.CoordinateLine
