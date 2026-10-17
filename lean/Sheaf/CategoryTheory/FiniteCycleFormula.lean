/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Mathlib.CategoryTheory.Subobject.Lattice
import Sheaf.CategoryTheory.DerivedCoupleExact
import all Sheaf.CategoryTheory.FinitePageImageLift
import Sheaf.CategoryTheory.DerivedCoupleKernelIdentities
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.CategoryTheory.DerivedCoupleExact
import WeilConjectures.CategoryTheory.DerivedCoupleKernelIdentities
import WeilConjectures.CategoryTheory.ExactCouple
import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.FinitePageImageLift

/-!
# Finite cycles of an exact couple

Source: Stacks Project, Homological Algebra, Lemma 12.21.4 (Tag 011T).
(blueprint: lem-sp-finite-cycle-formula)
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple
variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem pullback_square {U V W : C} (Z : Subobject W)
    (i : U ⟶ V) [Mono i] (a : (Z : C) ⟶ U) (f : W ⟶ V)
    (h : a ≫ i = Z.arrow ≫ f)
    (hZ : Z = (Subobject.pullback f).obj (Subobject.mk i)) (S : Subobject U) :
    (Subobject.«exists» Z.arrow).obj ((Subobject.pullback a).obj S) =
      (Subobject.pullback f).obj ((Subobject.map i).obj S) := by
  rw [Subobject.exists_obj_eq_imageSubobject, imageSubobject_mono,
    Subobject.map_obj_eq_mk]
  apply le_antisymm
  · apply (Subobject.mk_le_iff_factors _ _).mpr
    apply pullback_factors
    apply (Subobject.mk_factors_iff _ _).mpr
    refine ⟨Subobject.pullbackπ a S, ?_⟩
    change Subobject.pullbackπ a S ≫ (S.arrow ≫ i) = _
    rw [← Category.assoc, (Subobject.isPullback a S).w, Category.assoc, h]
    simp only [Category.assoc]
  · apply Subobject.le_of_factors
    let R := (Subobject.pullback f).obj (Subobject.mk (S.arrow ≫ i))
    have hRi : (Subobject.mk i).Factors (R.arrow ≫ f) := by
      apply Subobject.factors_of_le _ ?_
        ((Subobject.factors_pullback_obj_iff _ _ _).mp (Subobject.factors_self R))
      exact Subobject.mk_le_mk_of_comm S.arrow rfl
    have hRZ : Z.Factors R.arrow := by
      rw [hZ]
      exact pullback_factors _ _ _ hRi
    let l := Z.factorThru R.arrow hRZ
    have hl : l ≫ Z.arrow = R.arrow := Z.factorThru_arrow _ hRZ
    have hRa : S.Factors (l ≫ a) := by
      obtain ⟨s, hs⟩ := (Subobject.mk_factors_iff _ _).mp
        ((Subobject.factors_pullback_obj_iff _ _ _).mp (Subobject.factors_self R))
      change s ≫ (S.arrow ≫ i) = R.arrow ≫ f at hs
      apply (Subobject.factors_iff _ _).mpr
      refine ⟨s, ?_⟩
      change s ≫ S.arrow = l ≫ a
      apply (cancel_mono i).mp
      simpa only [Category.assoc, h, ← Category.assoc l, hl] using hs
    have hlP : ((Subobject.pullback a).obj S).Factors l := pullback_factors _ _ _ hRa
    apply (Subobject.mk_factors_iff _ _).mpr
    refine ⟨((Subobject.pullback a).obj S).factorThru l hlP, ?_⟩
    change _ ≫ (((Subobject.pullback a).obj S).arrow ≫ Z.arrow) = _
    rw [← Category.assoc, Subobject.factorThru_arrow, hl]

/-- The finite cycle subobject is the inverse image of the incoming alpha image.
Source: Stacks Project, Lemma 12.21.4 (Tag 011T), and Remark 12.21.5 (Tag 0AMJ).
(blueprint: lem-sp-finite-cycle-formula).

Proof: Take the recursively prescribed incoming powers A and mono inclusions I from
pageCouple_image_prefix. Induction on their recurrences identifies A with incomingAlphaIter.
Write T for the canonical cycle-boundary tower. First induct on r to prove that
T.projection r followed by page f and I r equals the cycle inclusion followed by original f.
The base is projection_zero and I zero being the identity. At the successor substitute
projection_succ and the recurrence for I. The derived f restriction equation replaces
its projection, f and derived-D inclusion by kernel.ι followed by the preceding f.
Use cycleLift_comm and the induction hypothesis, then compose the nested cycle inclusions.

Now induct on r to identify T.Z r with the pullback of image I r under original f.
At zero I is the identity, its image is top, and pulling back top gives top.
For the successor, the differential kernel identity rewrites ker(page d) as the pullback
under page f of ker(page g). Compose this pullback with the cycle projection.
The preceding commutative square and the inductive cycle formula identify its image
in the initial E with the pullback under original f of the image of ker(page g) under I r.
This square identity follows from the pullback factorization test in both directions;
monicity of I r permits cancellation when lifting a factorization back through the square.
Exactness identifies ker(page g) with the incoming page-alpha image, namely the subobject
represented by derivedDInclusion. Its direct image under I r is represented by their
composite, which is I (r+1) by its recurrence. This proves the successor formula.
Finally image I r equals image A r, and A r is incomingAlphaIter r, as required.
The proof works for every integer bidegree, without any finite-tail or cocone hypothesis. -/
theorem finiteCycle_formula (X : BigradedExactCouple C 0) (t : ℕ) (p q : ℤ) :
    X.cycleBoundaryTower.Z t p q =
      (Subobject.pullback (X.f p q)).obj
        (imageSubobject (X.incomingAlphaIter t (p + 2) (q - 1))) := by
  sorry


end CategoryTheory.BigradedExactCouple
