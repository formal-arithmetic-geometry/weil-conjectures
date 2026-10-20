/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.NormalCrossingsDivisor
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsDivisor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.CartierDivisorNowhereDense
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.Density
import Sheaf.AlgebraicGeometry.NCMaximalBranchBlowup
import Sheaf.AlgebraicGeometry.PermissibleBoundaryPreservation
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible

/-!
# Strictification of normal crossings divisors

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose VIII, 4.1.2--4.1.8,
Remark 4.2.2(i); Stacks 0B8X (blueprint: lem-trf-normal-crossings-strictification).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A normal crossings divisor on an integral regular finite-type scheme over an
algebraically closed field admits a proper modification, unchanged off the divisor,
with dense inverse image of that open and smooth strict normal crossings reduced boundary.
Source: ILO VIII 4.1.2--4.1.8 and Remark 4.2.2(i); Stacks 0B8X
(blueprint: lem-trf-normal-crossings-strictification).

Proof plan, following the node's eight steps:
1. Finite type over a field implies Noetherianity
   (`lem-weil-pbc-finite-type-over-noetherian`), and the Cartier complement is dense
   (`lem-pc-cartier-divisor-nowhere-dense`). Start with the old divisor and empty accumulated
   exceptional boundary. There is a finite maximal geometric branch depth.
2. If the old divisor is empty, use the identity. Otherwise iterate permissible blowups
   at its maximal branch locus, leaving the original complement unchanged.
3. `lem-trf-nc-maximal-branch-blowup` supplies the regular coordinate centre and lowers
   the branch depth of the OLD strict transform by one. Blowup properness and the
   complement isomorphism are `thm-nagata-global-blowup-proper` and
   `thm-nagata-global-blowup-complement`; finite type persists by
   `lem-sfb-finite-type-composition-base-change`.
4. `lem-trf-permissible-boundary-preservation` preserves ambient regularity, normal
   crossings of the total boundary and strict normal crossings of the accumulated
   exceptional boundary. Reductions use `def-weil-pbc-scheme-reduction`.
5. `lemma-nagata-admissible-blowup-preserves-density` preserves the dense complement;
   regularity and that integral dense open make the new ambient scheme integral.
6. After at most the initial depth many steps the old strict transform is empty.
   Thus the reduced inverse-image boundary is precisely the accumulated strict normal
   crossings exceptional boundary. Include the terminal Cartier-centre blowup.
7. Compose the proper maps (`lem-weil-pbc-proper-composition`) to obtain `q`, its
   complement isomorphism and dense inverse image.
8. An algebraically closed field is perfect. Apply `lem-trf-regular-perfect-field-smooth`
   to the finite-type regular ambient scheme and each regular component and intersection.
   They become smooth, with the same codimensions, including the empty boundary. -/
theorem exists_normalCrossings_strictification
    (F : Type u) [Field F] [IsAlgClosed F]
    (V : Scheme.{u}) (f : V ⟶ Spec (.of F)) [IsIntegral V]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hV : ∀ x : V, ∃ U : V.affineOpens, x ∈ U.1 ∧ IsRegularRing Γ(V, U.1))
    (Z : V.IdealSheafData) (hZ : Z.IsNormalCrossingsDivisor) :
    ∃ (V₂ : Scheme.{u}) (f₂ : V₂ ⟶ Spec (.of F)) (q : V₂ ⟶ V),
      IsIntegral V₂ ∧ Smooth f₂ ∧ LocallyOfFiniteType f₂ ∧ QuasiCompact f₂ ∧
        q ≫ f = f₂ ∧ IsProper q ∧ IsIso (q ∣_ Z.support.compl) ∧
        Dense ((q ⁻¹ᵁ Z.support.compl : V₂.Opens) : Set V₂) ∧
        ((Z.comap q).radical).IsStrictNormalCrossingsDivisor f₂ := by
  sorry

end AlgebraicGeometry
