/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.Proper
import Sheaf.AlgebraicGeometry.ReducedNormalization
import WeilConjectures.RingTheory.RegularRingFaithfullyFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.AlgebraicGeometry.NormalizationCompletionBaseChange

/-!
# Descent of normalized point blowups from completion

Source: Stacks Project, Resolution of Surfaces, Tags 0BGA and 0BG6(3)
(blueprint: lem-per-normalized-blowup-completion-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite proper normalized point-blowup tower over the completion descends to the
local domain, with its arrows and base maps; regularity of the endpoint descends too.
The base maps in degree zero are isomorphisms identifying that degree with the spectrum.
The vanishing ideal of the closed singleton gives its reduced induced scheme structure.
Each normalization is explicitly in the ordinary blowup's function field. The pullback
squares and commuting adjacent arrows express an isomorphism of the entire base-changed
sequence, including all structure maps. The index `Fin n` is empty when `n = 0`.

Source: Stacks Project, Tags 0BGA and 0BG6(3)
(blueprint: lem-per-normalized-blowup-completion-descent).

Proof plan:
1. Induct on the length, starting with the identity spectrum tower. The completion has
   the same residue field as A (lem-weil-pbc-local-completion-local-ring). The special
   fibres of the given and descended stages agree. A closed centre therefore descends
   to a closed point over the closed point of Spec A.
2. Blow up that reduced point. Completion is flat
   (lem-weil-pbc-noetherian-completion-flat); flatness survives base change
   (lem-weil-pbc-flat-morphism-base-change). The pulled ideal defines precisely the
   corresponding reduced point. Apply thm-nagata-blowup-flat-base-change.
3. The ordinary descended blowup is integral by faithfully flat descent from its
   integral completed blowup. The completed blowup is normal off the special fibre:
   thm-nagata-global-blowup-complement identifies that open with an open of the preceding
   normal stage; lem-weil-pbc-normalization-normal-stalks supplies normality of each
   normalized stage. Apply lem-per-normalization-completion-base-change (Tag 0BG9):
   the normalization is finite and its base change is the specified normalization.
   This preserves both adjacent arrows and the structure maps.
4. The descended stages are of finite type over A. Their closed-point ideals are of
   finite type, so thm-nagata-global-blowup-proper makes the ordinary blowup proper.
   Its finite normalization is proper by lem-weil-pbc-finite-proper; use
   lem-weil-pbc-proper-composition for the composite.
5. Completion is faithfully flat (lem-weil-pbc-local-completion-faithfully-flat), and
   remains flat and surjective on the endpoint (lem-weil-pbc-flat-morphism-base-change,
   lem-weil-pbc-surjective-base-change). At a point above each descended point the local
   flat map is faithfully flat (lem-weil-pbc-flat-local-hom-faithfully-flat). Apply
   lem-weil-pbc-regular-ring-faithfully-flat-descent to the regular endpoint stalks.
   The descended endpoint is locally Noetherian, hence is a regular scheme. -/
theorem exists_normalizedBlowup_tower_of_completion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    [IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    (n : ℕ) (Z : Fin (n + 1) → Scheme.{u})
    (bZ : ∀ i : Fin n, Z i.succ ⟶ Z i.castSucc)
    (pZ : ∀ i, Z i ⟶ Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
    (hZ₀ : IsIso (pZ 0))
    (hpZ : ∀ i : Fin n, bZ i ≫ pZ i.castSucc = pZ i.succ)
    (hZ : ∀ i : Fin n, IsProper (bZ i) ∧
      ∃ (y : Z i.castSucc) (hy : IsClosed ({y} : Set (Z i.castSucc))),
        pZ i.castSucc y =
          IsLocalRing.closedPoint (AdicCompletion (IsLocalRing.maximalIdeal A) A) ∧
        ∃ (J : (Z i.castSucc).IdealSheafData),
          J = Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩ ∧
          ∃ (_ : IsIntegral J.blowup) (e : Z i.succ ≅ J.blowup.normalization),
            e.hom ≫ J.blowup.fromNormalization ≫ J.blowupMap = bZ i) :
    ∃ (X : Fin (n + 1) → Scheme.{u})
      (bX : ∀ i : Fin n, X i.succ ⟶ X i.castSucc)
      (pX : ∀ i, X i ⟶ Spec (.of A)),
      IsIso (pX 0) ∧
      (∀ i : Fin n, bX i ≫ pX i.castSucc = pX i.succ) ∧
      (∀ i : Fin n, IsProper (bX i) ∧
        ∃ (x : X i.castSucc) (hx : IsClosed ({x} : Set (X i.castSucc))),
          pX i.castSucc x = IsLocalRing.closedPoint A ∧
          ∃ (J : (X i.castSucc).IdealSheafData),
            J = Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩ ∧
            ∃ (_ : IsIntegral J.blowup) (e : X i.succ ≅ J.blowup.normalization),
              e.hom ≫ J.blowup.fromNormalization ≫ J.blowupMap = bX i) ∧
      (∃ c : ∀ i, Z i ⟶ X i,
        (∀ i, IsPullback (c i) (pZ i) (pX i)
          (Spec.map (CommRingCat.ofHom
            (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))) ∧
        (∀ i : Fin n, c i.succ ≫ bX i = bZ i ≫ c i.castSucc)) ∧
      (IsRegularScheme (Z (Fin.last n)) → IsRegularScheme (X (Fin.last n))) := by
  sorry

end AlgebraicGeometry
