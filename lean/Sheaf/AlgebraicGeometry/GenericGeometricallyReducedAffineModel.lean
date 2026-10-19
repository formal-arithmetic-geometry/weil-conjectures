/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction
import WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation
import Sheaf.AlgebraicGeometry.GenericQuasiSeparatedness
import Sheaf.AlgebraicGeometry.ReductionGenericFibre
import Sheaf.RingTheory.PowerGeneratedSpectrumHomeomorphism

/-! # Affine model with a geometrically reduced generic fibre

This is the construction part of Stacks Project Tag 0550.  The final preparation
theorem only has to propagate the generic-fibre assertion from the chosen generic
point to every generic point of the integral base.
(blueprint: lem-pur-generic-geometrically-reduced-preparation-core)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The affine finite universal-homeomorphism model before generic-point propagation.

Source: Stacks Project, Tag 0550, clauses (1)--(8).

Proof: choose an affine open in the irreducible base and pass to its reduced domain.
The generic fibre is finite type over the fraction field, so the finite purely inseparable
extension supplied by the finite-inseparable geometric-reduction theorem makes its
reduction geometrically reduced. Scale finitely many field generators so that their
powers lie in the base ring and adjoin them to obtain a finite integral affine domain.
The power-generated spectrum criterion gives a universal homeomorphism. Pull back the
family and reduce it; the reduction-generic-fibre comparison identifies its generic
fibre with the chosen geometrically reduced reduction. Generic flatness, local finite
presentation, and generic quasi-separatedness then hold after intersecting nonempty
opens. A principal open in the original affine base whose inverse image lies in this
intersection supplies the displayed model. Its distinguished point is generic because
the model is integral.

(blueprint: lem-pur-generic-geometrically-reduced-preparation-core)
-/
theorem exists_generic_geometricallyReduced_affine_model {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] [IrreducibleSpace S] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ IsAffineOpen U ∧
      ∃ T : Scheme.{u}, IsIntegral T ∧ IsAffine T ∧
        ∃ q : T ⟶ U.toScheme, IsFinite q ∧
          (topologically IsHomeomorph).universally q ∧
          Flat ((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
            pullback.snd f (q ≫ U.ι)) ∧
          LocallyOfFinitePresentation ((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
            pullback.snd f (q ≫ U.ι)) ∧
          QuasiCompact ((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
            pullback.snd f (q ≫ U.ι)) ∧
          QuasiSeparated ((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
            pullback.snd f (q ≫ U.ι)) ∧
          ∃ η : T, IsGenericPoint η Set.univ ∧ GeometricallyReduced
            (((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
              pullback.snd f (q ≫ U.ι)).fiberToSpecResidueField η) := by
  sorry

end AlgebraicGeometry
