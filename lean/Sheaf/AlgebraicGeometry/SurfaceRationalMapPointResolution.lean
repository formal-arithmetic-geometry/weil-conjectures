/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.RegularPointBlowupGeometry

/-!
# Elimination of indeterminacy on a regular Noetherian surface

Source: Stacks Project, Resolution of Surfaces, Tag 0C5H
(`resolve-lemma-extend-rational-map-blowing-up`), with regularity from Tag 0AGR
(blueprint: lem-sfb-surface-rational-map-point-resolution).

The existing ordinary blowup tower retains all intermediate schemes and their maps.
Vanishing ideals of closed singletons specify the reduced closed point centres.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A map on a dense open of an integral regular Noetherian surface extends to a proper
relative target after finitely many blowups of reduced closed points away from that open.
All intermediate schemes are again integral regular Noetherian surfaces. Length zero
is allowed.

Source: Stacks Project, Tag 0C5H, with regularity from Tag 0AGR
(blueprint: lem-sfb-surface-rational-map-point-resolution).

Proof plan:
1. Among domains V containing U to which f extends, minimize the closed complement T
   using lem-weil-pbc-noetherian-scheme-closed-subsets-minimal.
2. The local dimension chain formula (lem-sc-scheme-stalk-dimension-generalization-chains)
   bounds local dimensions by two. Integrality puts the generic point in U. At a remaining
   dimension-one point, regularity and lem-sc-regular-dim1-dvr give a DVR, hence a valuation
   ring (def-sc-discrete-valuation-ring). The extension given by
   lem-sfb-rational-map-extension-valuation-point contradicts maximality of V.
3. Thus all points of T have local dimension two and are closed. Noetherian induction on
   closed subsets, together with sobriety (lem-sc-scheme-sober), makes T finite: a minimal
   counterexample is reducible, since its generic point would otherwise be closed.
4. Noetherian induction also shows every open of X is quasi-compact, so V -> X is
   quasi-compact.
5. Form the scheme-theoretic image Z of the graph V -> X ×_S Y
   (def-nagata-scheme-theoretic-image). Proper base change and closed-immersion properness
   (lem-weil-pbc-proper-base-change, lem-weil-pbc-closed-immersion-proper) make Z -> X
   proper. The partial-section image theorem (lemma-nagata-scheme-image-partial-section)
   makes it an isomorphism over V; the other projection extends the map there.
6. Apply lem-sfb-regular-point-blowup-domination to this modification and T. Its tower
   dominates Z, and its reduced closed centres map into T, hence avoid the original U.
7. Induct along the tower using lem-sfb-regular-point-blowup-geometry: every level is
   integral, regular and Noetherian, each step is proper and unchanged off its centre,
   and every closed point over T has local dimension two. Properness makes its image
   closed; the complement isomorphism handles points not over the next centre.
8. Every point of a Noetherian scheme has a closed specialization: minimize a nonempty
   closed subset of its closure and use sobriety to make it a singleton. The local chain
   formula bounds dimension by the dimension at such a specialization and identifies
   global dimension with the supremum of local dimensions.
9. Inductively the next level has dimension at most two by step 8 and the off-centre
   isomorphism. The proper blowup has closed image containing the dense complement of
   the centre, hence is surjective. A closed specialization over the centre has local
   dimension two by the geometry lemma, giving the reverse dimension bound.
10. Compose the tower maps: lem-weil-pbc-proper-composition gives properness, and the
    off-centre isomorphisms give the isomorphism over U. Compose the domination map to Z
    with its projection to Y to obtain g. The graph identity gives agreement with f over
    the inverse image of U and the S-morphism identity. For U = X take the length-zero
    tower; the same option applies whenever f already extends.
-/
theorem exists_surface_rational_map_point_resolution
    (S X Y : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (hX : IsRegularScheme X) (hdim : topologicalKrullDim X = 2)
    (U : X.Opens) (hU : Dense (U : Set X))
    (f : U.toScheme ⟶ Y) (hf : f ≫ sY = U.ι ≫ sX) :
    ∃ (A : OrdinaryBlowupTower X) (g : A.level (Fin.last A.length) ⟶ Y),
      (∀ i : Fin A.length, ∃ (p : A.level i.castSucc) (hp : IsClosed ({p} : Set _)),
        A.center i = Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩ ∧
          A.toBase i.castSucc p ∉ U) ∧
      (∀ i : Fin (A.length + 1), IsIntegral (A.level i) ∧
        IsRegularScheme (A.level i) ∧ IsNoetherian (A.level i) ∧
          topologicalKrullDim (A.level i) = 2) ∧
      IsProper (A.toBase (Fin.last A.length)) ∧
      IsIso (A.toBase (Fin.last A.length) ∣_ U) ∧
      g ≫ sY = A.toBase (Fin.last A.length) ≫ sX ∧
      (A.toBase (Fin.last A.length) ⁻¹ᵁ U).ι ≫ g =
        (A.toBase (Fin.last A.length) ∣_ U) ≫ f := by
  sorry

end AlgebraicGeometry
