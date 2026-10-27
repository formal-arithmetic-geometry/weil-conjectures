/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import WeilConjectures.RingTheory.GRing
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.FiniteStability
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.SmoothAtPointFibreCriterion

/-!
# Smooth neighbourhoods from regular stalk maps

Source: Stacks Project, Morphisms, Tag 01V9, (2) implies (1), and Varieties,
Tags 038U and 038X (blueprint: lem-per-lfp-regular-stalk-smooth-neighborhood).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A locally finitely presented morphism of locally Noetherian schemes is smooth on
an open neighbourhood of any point where its stalk map is regular.
Source: Stacks Project, Morphisms, Tag 01V9, (2) implies (1), combined with
Varieties, Tags 038U and 038X
(blueprint: lem-per-lfp-regular-stalk-smooth-neighborhood).

Proof:
1. Set A = O_{Y,f(x)}, B = O_{X,x}, m = m_{f(x)}, and k = kappa(f(x)).
   Regularity of A -> B gives flatness and geometric regularity of B tensor_A k
   by `def-weil-pbc-g-ring`, applied to the maximal ideal of A (Stacks 07BZ).
2. The local ring of the scheme fibre at the point over x is B/mB, via the
   fibre projection, by `lem-sbc-scheme-fibre-stalk-quotient` (Stacks 0HA1).
   By `lem-weil-pbc-fibre-ring-localization-quotient` (Stacks 00E6), the ring
   B tensor_A k is also B/mB: elements of A outside m already map to units in B.
   These identifications respect k because both maps send each residue class
   of a in A to the class of its image in B. Tensor with each finite purely
   inseparable extension of k to transfer geometric regularity to the fibre stalk.
3. The fibre is locally of finite type over k. Choose finite-presentation affine
   charts for f (`def-sbc-locally-finite-presentation`). The open and affine
   fibre-product descriptions (`lem-weil-pbc-open-fibre-product` and
   `lem-weil-pbc-fibre-product-affine-spectra`) identify their fibres with
   Spec(S tensor_R k). Finite presentation survives base change by
   `lem-weil-pbc-finite-presentation-base-change-composition`; its polynomial
   generators give finite type (`def-weil-finite-type-morphism`).
4. Apply `lem-per-geometrically-regular-stalk-smooth-over-field` (Stacks 038U,
   038X) to this fibre and its geometrically regular stalk. It gives a smooth
   open neighbourhood of the point over x in the fibre.
5. Use `lem-trf-smooth-at-point-fibre-criterion` (Stacks 01V9): local finite
   presentation is assumed, flatness of the stalk map is step 1, and smoothness
   of the fibre at the point is step 4. Its reverse implication supplies the
   required open neighbourhood U of x, smooth over Y. -/
theorem exists_smooth_open_neighborhood_of_regular_stalkMap
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] (x : X)
    (hregular : (f.stalkMap x).hom.IsRegular) :
    ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f) := by
  sorry

end AlgebraicGeometry
