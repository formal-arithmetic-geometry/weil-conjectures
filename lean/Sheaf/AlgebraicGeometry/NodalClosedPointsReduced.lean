/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Reducedness from smooth or nodal closed points

Source: Stacks Project, curves.tex, Tag 0E37, reducedness paragraph; algebra.tex,
Tags 00MC and 05CK; varieties.tex, Tag 0478.
(blueprint: lem-trf-nodal-points-reduced-algebraically-closed).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme locally of finite type over an algebraically closed field is reduced if each
closed point without a smooth open neighbourhood has completed local ring `F[[u,v]]/(uv)`.
The completed-ring isomorphism need only be a ring isomorphism. No dimension, quasi-compactness,
separatedness, properness or nonemptiness hypothesis is required.

Source: Stacks Project, curves.tex, Tag 0E37, reducedness paragraph, using algebra.tex,
Tags 00MC and 05CK and varieties.tex, Tag 0478.
(blueprint: lem-trf-nodal-points-reduced-algebraically-closed).

Proof plan:
1. The field is Noetherian, and locally finite type over a locally Noetherian scheme implies
   locally Noetherian (pqf-def-locnoeth, pqf-lem-locnoeth-lft). Affine-stalk localization and
   localization-noetherian then show that every local ring is Noetherian
   (lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-localization-noetherian).
2. At a closed point with a smooth open neighbourhood, smooth geometric fibres are reduced
   (sbc-lem-smooth-geometrically-reduced). The identity field extension gives reducedness of
   that neighbourhood, and its stalk agrees with the ambient stalk (def-pc-reduced-scheme).
3. Restrict power series to the two axes. Both restrictions vanish exactly for multiples of
   uv: shift coefficients by (1,1). Thus the quotient by (uv) embeds into the product of the
   one-variable power-series domains (def-weil-pbc-multivariate-power-series,
   lem-weil-pbc-power-series-domain), and is reduced.
4. At a nonsmooth closed point the Noetherian local ring injects into its completion by
   faithful flatness (lem-weil-pbc-local-completion-faithfully-flat,
   lem-weil-pbc-faithfully-flat-ideal-contraction with the zero ideal). The given ring
   isomorphism and step 3 show its stalk is reduced.
5. Every point y has a closed specialization x (lem-sc-lft-over-field-jacobson-space).
   In an affine neighbourhood of x, also containing y, the primes satisfy q = p_y <= p_x = p
   (def-weil-affine-spectrum). Its stalks are B_q and B_p
   (lem-weil-pbc-affine-open-stalk-localization). If a/b in B_q is nilpotent, choose n >= 1
   and t outside q with t*a^n = 0. Then (t*a/1)^n = 0 in the reduced ring B_p, so t*a/1 = 0.
   Choose u outside p with u*t*a = 0. Since u*t is outside q, a/b = 0 in B_q
   (def-weil-pbc-localization-at-prime).
6. All stalks are reduced, hence the scheme is reduced (def-pc-reduced-scheme). The empty
   case is vacuous, and the argument uses neither a finite cover nor a dimension bound. -/
theorem isReduced_of_nodal_closed_points
    (F : Type u) [Field F] [IsAlgClosed F]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of F)) [LocallyOfFiniteType f]
    (hnodal : ∀ x : C, x ∈ closedPoints C →
      (¬ ∃ U : C.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) →
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
          (C.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) F ⧸ Ideal.span
            {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) F) * MvPowerSeries.X 1}))) :
    IsReduced C := by
  sorry

end AlgebraicGeometry
