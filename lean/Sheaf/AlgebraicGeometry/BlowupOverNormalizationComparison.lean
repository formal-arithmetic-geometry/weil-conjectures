/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.NormalizedBlowupFinality
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Field.ULift
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-!
# Normalized blowups over the componentwise normalization

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose VIII,
Proposition 2.2.4(ii), using 2.2.2 and 2.2.4(i), printed p.90
(blueprint: lem-trf-blowup-over-normalization-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Normalizing a blowup agrees uniquely with the normalized blowup of the extended
ideal on the componentwise normalization. The inverse is unique among all morphisms
of schemes over the original base. Since the base is finite type over Q, it is
Noetherian; coherence of a quasi-coherent ideal is finite generation on affine opens.
Dense complement is equivalent to the closed zero set being nowhere dense.

Source: ILO, Expose VIII, Proposition 2.2.4(ii), using 2.2.2 and 2.2.4(i), printed p.90
(blueprint: lem-trf-blowup-over-normalization-comparison).

Proof:
1. By lem-trf-normalization-affine-stalk-closure, S and its normalization are
Noetherian with finitely many components and the normalization map is finite.
By lem-sfb-componentwise-normalization-generic-properties the normalized base is
normal and its generic points correspond to those of S. Finiteness and
lem-sfb-finite-type-composition-base-change make it finite type over Q. The dense
open complement of the centre contains every generic point of S.
2. Extension of the ideal is affine-locally I B for A -> B. Finite generators extend,
and pqf-lem-coherent-ft-locnoeth gives coherence on the normalized base. Its generic
points map away from the original centre, so the extended centre has dense complement.
The affine identity (I B) C = I C identifies iterated extended ideals.
3. By lem-trf-normalized-blowup-finality the normalized blowup X is normal, takes
generic points to generic points, and principalizes J. Apply
lem-sfb-component-dominant-normalization-lift to get the unique n over S.
4. The single-point generic fibres of the normalization imply that n takes generic
points to generic points. Its extended ideal equals J O_X and is invertible. Apply
lem-trf-normalized-blowup-finality over the normalized base to get a unique map
X -> Y over that base.
5. Finality for (S,J) gives the unique reverse S-morphism r : Y -> X. Normalization
lifting uniqueness gives r followed by n equal to Y's structural map.
6. Finality over S identifies the composite X -> Y -> X with the identity. Finality
over the normalized base similarly identifies Y -> X -> Y with the identity.
The comparison is therefore an isomorphism; its uniqueness follows from forward-map
uniqueness, and its inverse is the unique S-morphism already obtained. All steps
apply componentwise, to the empty scheme, and to the unit ideal. -/
theorem normalizedBlowup_over_normalization_comparison (S : Scheme.{u})
    (a : S ⟶ Spec (.of (ULift.{u} ℚ))) [IsReduced S]
    [LocallyOfFiniteType a] [QuasiCompact a] (J : S.IdealSheafData)
    (hJ : ∀ U : S.affineOpens, (J.ideal U).FG)
    (hcentre : Dense (J.support.compl : Set S)) :
    Dense ((J.comap S.fromReducedNormalization).support.compl :
      Set S.reducedNormalization) ∧
    (∃! n : J.normalizedBlowup ⟶ S.reducedNormalization,
      n ≫ S.fromReducedNormalization = J.normalizedBlowupMap) ∧
    (∀ n : J.normalizedBlowup ⟶ S.reducedNormalization,
      n ≫ S.fromReducedNormalization = J.normalizedBlowupMap →
      (∃! e : J.normalizedBlowup ≅ (J.comap S.fromReducedNormalization).normalizedBlowup,
        e.hom ≫ (J.comap S.fromReducedNormalization).normalizedBlowupMap = n) ∧
      (∀ e : J.normalizedBlowup ≅ (J.comap S.fromReducedNormalization).normalizedBlowup,
        e.hom ≫ (J.comap S.fromReducedNormalization).normalizedBlowupMap = n →
        e.inv ≫ J.normalizedBlowupMap =
          (J.comap S.fromReducedNormalization).normalizedBlowupMap ≫
            S.fromReducedNormalization ∧
        (∀ r : (J.comap S.fromReducedNormalization).normalizedBlowup ⟶ J.normalizedBlowup,
          r ≫ J.normalizedBlowupMap =
            (J.comap S.fromReducedNormalization).normalizedBlowupMap ≫
              S.fromReducedNormalization → r = e.inv) ∧
        e.hom ≫ e.inv = 𝟙 J.normalizedBlowup ∧
        e.inv ≫ e.hom = 𝟙 (J.comap S.fromReducedNormalization).normalizedBlowup)) := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
