/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.NormalCrossingsDivisor
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.PermissibleCenter
public import Sheaf.AlgebraicGeometry.UnionOfIrreducibleComponents
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.StrictTransform
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.Complement
import Sheaf.AlgebraicGeometry.EtaleReducedCartierDescent
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.TraceFormula.EtaleComponentCoordinateIdentification
import Sheaf.TraceFormula.EtaleRegularIntersectionDescent
import Sheaf.AlgebraicGeometry.PermissibleCoordinateChart
import Sheaf.AlgebraicGeometry.StrictTransformFlatBaseChange

/-!
# Permissible blowups preserve a normal-crossings boundary

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VIII,
4.1.2--4.1.4(i), Remark 4.2.2(i), and Lemma 4.2.9 (blueprint:
lem-trf-permissible-boundary-preservation).
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The ideal sheaf cutting out the strict transform of a closed subscheme in a blowup.
Source: ILO, Exposé VIII, Lemma 4.2.9 (blueprint:
lem-trf-permissible-boundary-preservation). -/
def strictTransformIdeal {X : Scheme.{u}} (I Z : X.IdealSheafData) :
    I.blowup.IdealSheafData :=
  (I.strictTransformι Z.subschemeι ≫ pullback.snd Z.subschemeι I.blowupMap).ker

/-- A permissible blowup preserves regularity, normal crossings, and the strict boundary.
Source: ILO, Exposé VIII, 4.1.2--4.1.4(i), Remark 4.2.2(i), and Lemma 4.2.9
(blueprint: lem-trf-permissible-boundary-preservation).

Proof:
1. By `thm-nagata-global-blowup-proper` and `def-weil-proper-morphism` the blowup
   is finite type over the Noetherian scheme X. Thus `lem-weil-pbc-finite-type-over-noetherian`
   and `lem-weil-pbc-noetherian-finitely-many-components` give Noetherianity and finiteness
   of the boundary component families. `thm-nagata-global-blowup-complement` identifies the
   complement of E with X minus M; `lemma-nagata-strict-transform-restrict` identifies
   the strict transforms there. The claims on this open follow from the hypotheses.
2. At x in M choose the stated etale boundary coordinates and representatives on an
   affine neighbourhood. `lem-trf-etale-component-coordinate-identification` identifies
   the original distinct regular components of H with distinct coordinate hyperplanes
   and supplies the generic-point condition for strict-transform base change.
3. Base change the blowup to this neighbourhood, using `lem-weil-pbc-etale-scheme-base-change`
   and `thm-nagata-blowup-flat-base-change`. A point over a given pair (y,w) exists since
   the tensor product of the two residue-field extensions is nonzero. On a standard chart,
   `lem-trf-permissible-coordinate-chart` gives regularity and coordinate boundaries.
   Apply `lem-trf-strict-transform-flat-etale-base-change` to the original H components:
   their transforms are empty or distinct surviving coordinate hyperplanes. The reduced
   exceptional inverse image is the additional exceptional coordinate hyperplane.
4. `lem-trf-etale-reduced-cartier-descent` identifies the reduced pullbacks and descends
   their Cartier property. The coordinate equations give normal crossings of B+.
   Apply `lem-trf-etale-regular-intersection-descent` to E and the nonempty strict transforms
   of the H components, including the empty intersection, to descend ambient regularity
   and regular intersections of the expected codimension. By `rem-pc-regular-normal`
   the components of the regular Noetherian E are disjoint and clopen. Strict transforms
   of original H components are irreducible as closures of their irreducible complements
   of M. Splitting E into its components therefore proves the SNC criterion for H+.
5. Off E the transforms agree with B and H; on the charts their reduced unions with E
   are precisely B+ and H+. The scheme-theoretic closure `def-nagata-strict-transform`
   and reduction `def-weil-pbc-scheme-reduction` give the displayed ideal equalities.
   Every H+ hyperplane is a B+ hyperplane, giving the component assertion. The empty
   original H has empty strict transform and H+ = E. -/
theorem permissible_boundary_preservation
    (X : Scheme.{u}) [IsNoetherian X] (hX : IsRegularScheme X)
    (B H M : X.IdealSheafData)
    (hB : B.IsNormalCrossingsDivisor)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hHB : (H.support : Set X) ⊆ (B.support : Set X))
    (hHcomponents : IsUnionOfIrreducibleComponents H B)
    (hM : IsPermissibleCenter B M) :
    IsRegularScheme M.blowup ∧
      ((B.comap M.blowupMap).radical).IsNormalCrossingsDivisor ∧
      IsStrictNormalCrossingsBoundary ((H ⊓ M).comap M.blowupMap).radical ∧
      (((H ⊓ M).comap M.blowupMap).radical.support : Set M.blowup) ⊆
        (((B.comap M.blowupMap).radical).support : Set M.blowup) ∧
      IsUnionOfIrreducibleComponents ((H ⊓ M).comap M.blowupMap).radical
        ((B.comap M.blowupMap).radical) ∧
      (B.comap M.blowupMap).radical =
        strictTransformIdeal M B ⊓ (M.comap M.blowupMap).radical ∧
      ((H ⊓ M).comap M.blowupMap).radical =
        strictTransformIdeal M H ⊓ (M.comap M.blowupMap).radical := by
  sorry

end AlgebraicGeometry
