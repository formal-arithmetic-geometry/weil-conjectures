/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q41
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Log regularity under saturated toric chart refinements

Source: Illusie--Laszlo--Orgogozo, Exposé VI, §1.8, and Exposé VIII,
§§3.3.8--3.3.11 (blueprint: lem-trf-log-regular-toric-refinement).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The affine tensor-product ring for a monoid chart refinement.  The two
algebra structures are induced by `β` and by the inclusion `i` of monoids.
Source: ILO VIII, 3.3.8--3.3.11 (blueprint: lem-trf-log-regular-toric-refinement). -/
abbrev toricChartRing {A : Type u} [CommRing A] {P : Type u} [CommMonoid P]
    (β : P →* A) (Q : Submonoid (Algebra.GrothendieckGroup P)) (i : P →* Q) : Type u :=
  letI : Algebra (MonoidAlgebra ℤ P) A :=
    (MonoidAlgebra.lift ℤ A P β).toRingHom.toAlgebra
  letI : Algebra (MonoidAlgebra ℤ P) (MonoidAlgebra ℤ Q) :=
    ((MonoidAlgebra.lift ℤ (MonoidAlgebra ℤ Q) P
      ((MonoidAlgebra.of ℤ Q).comp i)).toRingHom).toAlgebra
  TensorProduct (MonoidAlgebra ℤ P) A (MonoidAlgebra ℤ Q)

/-- The canonical monoid chart on the tensor-product ring of `toricChartRing`.
Source: ILO VIII, 3.3.8--3.3.11 (blueprint: lem-trf-log-regular-toric-refinement). -/
noncomputable def toricChartMap {A : Type u} [CommRing A] {P : Type u} [CommMonoid P]
    (β : P →* A) (Q : Submonoid (Algebra.GrothendieckGroup P)) (i : P →* Q) : Q →*
    toricChartRing β Q i := by
  letI : Algebra (MonoidAlgebra ℤ P) A :=
    (MonoidAlgebra.lift ℤ A P β).toRingHom.toAlgebra
  letI : Algebra (MonoidAlgebra ℤ P) (MonoidAlgebra ℤ Q) :=
    ((MonoidAlgebra.lift ℤ (MonoidAlgebra ℤ Q) P
      ((MonoidAlgebra.of ℤ Q).comp i)).toRingHom).toAlgebra
  exact (Algebra.TensorProduct.includeRight :
    MonoidAlgebra ℤ Q →ₐ[MonoidAlgebra ℤ P]
      TensorProduct (MonoidAlgebra ℤ P) A (MonoidAlgebra ℤ Q)).toMonoidHom.comp
      (MonoidAlgebra.of ℤ Q)

/-- A log-regular affine chart remains log regular under an fs toric refinement.
The chart is global (the identity étale object), and its structural image is the
specified ring map. The conclusion's global chart has structural image exactly
`toricChartMap`, so it identifies the log structure with the associated log structure,
rather than merely asserting the existence of an unrelated log structure.

Proof: (1) `Q` is fs, and the inclusion of `P` induces an isomorphism on group
completions since `P` already generates its group completion.
(2) An affine open of a locally Noetherian scheme is Noetherian
[pqf-lem-affine-open-locnoeth]. Finite monoid generators of `Q` give finite algebra
generators of the tensor product, hence it is Noetherian
[lem-weil-pbc-finite-type-algebra-noetherian]. Thus its spectrum is locally Noetherian.
(3) Form the associated log structure of the canonical chart
[lem-trf-associated-log-universal-stalks]. It is fs, and the compatible charts define
a log morphism to `Y`. (4) The affine fiber-product identification
[lem-weil-pbc-fibre-product-affine-spectra] identifies its chart comparison with the
identity on the tensor-product spectrum, which is étale.
(5) Apply log smooth preservation of log regularity
[lem-trf-log-smooth-log-regular], using the group isomorphism and this comparison.
(6) When the tensor product is zero its spectrum is empty, and all geometric-point
conditions are vacuous. Source: ILO VI 1.8; VIII 3.3.8--3.3.11
(blueprint: lem-trf-log-regular-toric-refinement). -/
theorem logRegular_toricChartRefinement
    (Y : FineSaturatedLogScheme.{u}) (A : Type u) [CommRing A]
    (eA : Y.scheme ≅ Scheme.Spec.obj (Opposite.op (CommRingCat.of A)))
    (hY : Y.IsLogRegular) (P : Type u) [CommMonoid P]
    (pFine : IsFineSaturatedMonoid P) (β : P →* A)
    (βY : P →* Y.logStructure.monoidSheaf.obj.obj
      (op (Scheme.Etale.mk (𝟙 Y.scheme))))
    (hβY : Y.logStructure.IsChart (Scheme.Etale.mk (𝟙 Y.scheme)) βY)
    (hβ : ∀ p : P,
      Y.logStructure.alpha.app (op (Scheme.Etale.mk (𝟙 Y.scheme))) (βY p) =
        eA.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (β p)))
    (Q : Submonoid (Algebra.GrothendieckGroup P))
    (qFine : IsFineSaturatedMonoid Q) (i : P →* Q)
    (hi : ∀ p : P, (i p : Algebra.GrothendieckGroup P) =
      Algebra.GrothendieckGroup.of p) :
    ∃ (X : FineSaturatedLogScheme.{u})
      (eC : X.scheme ≅ Scheme.Spec.obj
        (Opposite.op (CommRingCat.of (toricChartRing β Q i))))
      (βX : Q →* X.logStructure.monoidSheaf.obj.obj
        (op (Scheme.Etale.mk (𝟙 X.scheme)))),
      X.IsLogRegular ∧ X.logStructure.IsChart (Scheme.Etale.mk (𝟙 X.scheme)) βX ∧
        ∀ q : Q,
          X.logStructure.alpha.app (op (Scheme.Etale.mk (𝟙 X.scheme))) (βX q) =
            eC.hom.appTop
              ((Scheme.ΓSpecIso (CommRingCat.of (toricChartRing β Q i))).inv
                (toricChartMap β Q i q)) := by
  sorry

end AlgebraicGeometry
