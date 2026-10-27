/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.Blowup.AdmissibleBlowup
import WeilConjectures.Compactification.StrictTransform
import WeilConjectures.Blowup.BlowupUniversal

/-!
# Domination by blowups at regular surface points

Source: Stacks Project, Resolution of Surfaces, Tag 0AHI,
`resolve-lemma-dominate-by-blowing-up-in-points`
(blueprint: lem-sfb-regular-point-blowup-domination).

The existing ordinary tower records all intermediate schemes and their composites.
The vanishing ideal of a closed singleton specifies its reduced scheme structure.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A proper morphism which is an isomorphism away from finitely many regular
surface points is dominated by a finite tower of blowups of reduced closed points
above those points. Length zero is allowed.

Source: Stacks Project, Resolution of Surfaces, Tag 0AHI
(blueprint: lem-sfb-regular-point-blowup-domination).

Proof plan:
1. The finite union T of closed points is closed. Its open complement U is
   quasi-compact by lem-weil-pbc-noetherian-open-subscheme-noetherian. The base
   is quasi-separated by lem-weil-pbc-locally-noetherian-quasi-separated and
   quasi-compact by hypothesis.
2. Apply sk-lem-nagata-sketch-elimination to f and U. It gives a U-admissible
   blowup B with open strict transform and schematically dense inverse image of U.
   Unpack def-nagata-admissible-blowup to obtain its finite-type ideal I, equal
   to the unit ideal on U.
3. By def-nagata-strict-transform and def-nagata-scheme-theoretic-closure, the
   strict transform is closed in Y times_X B. By lem-weil-pbc-proper-base-change
   and lem-weil-pbc-closed-immersion-proper its map to B is proper. Its closed
   image contains the schematically dense inverse image of U, hence is all of B.
   A surjective open immersion is an isomorphism (def-weil-open-immersion).
   Its inverse followed by the projection to Y gives q : B -> Y over X.
4. Since I is the unit ideal off T, O_X/I is supported on T. Apply
   lem-sfb-surface-point-ideal-principalization to obtain the point-blowup tower
   with centers over T and effective Cartier, hence invertible, extended ideal.
5. By def-nagata-extended-ideal and thm-nagata-blowup-universal-property, the
   composite t from the top of this tower lifts to B. Compose this lift with q.
   The resulting h satisfies h followed by f equals t. The principalization
   permits length zero; for empty T one can take the inverse of f.
-/
theorem exists_regular_point_blowup_domination
    (X Y : Scheme.{u}) [IsNoetherian X]
    (T : TopologicalSpace.Closeds X) (hT : (T : Set X).Finite)
    (hclosed : ∀ t ∈ (T : Set X), IsClosed ({t} : Set X))
    (hregular : ∀ t ∈ (T : Set X), IsRegularLocalRing (X.presheaf.stalk t))
    (hdim : ∀ t ∈ (T : Set X), ringKrullDim (X.presheaf.stalk t) = 2)
    (f : Y ⟶ X) [IsProper f] (hiso : IsIso (f ∣_ T.compl)) :
    ∃ (A : OrdinaryBlowupTower X) (h : A.level (Fin.last A.length) ⟶ Y),
      h ≫ f = A.toBase (Fin.last A.length) ∧
      ∀ i : Fin A.length, ∃ (p : A.level i.castSucc) (hp : IsClosed ({p} : Set _)),
        A.center i = Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩ ∧
          A.toBase i.castSucc p ∈ (T : Set X) := by
  sorry

end AlgebraicGeometry
