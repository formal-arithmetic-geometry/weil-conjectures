/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianLimitStageShift
import WeilConjectures.AlgebraicGeometry.BoundedBelowContinuityInduction

/-! # Reduction of bounded-below continuity to pure coefficients

Source: Stacks Tag 0GIU, finite descent on the lower cohomological bound.
(blueprint: lem-sf-abelian-limit-stage-induction).
-/

@[expose] public section

universe u' u

set_option autoImplicit false

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale.AbelianLimitStageSystem

variable {B W : Scheme.{u}} {I : Type u} [Category.{u} I]
  (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  (S : LimitStageSystem B W I)

omit [HasSmallSiteSheafify A] in
private lemma stage_isZero (α : LimitStage B W)
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A))
    (a p : ℤ) [K.IsGE a] (hp : p < a) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ p).obj
      ((AbelianLimitStage.functor A α).obj K)) := by
  have : ((upperStar A α.w).mapDerivedCategoryPlus.obj K).IsGE a :=
    Functor.IsTExact.isGE_obj DerivedCategory.Plus.TStructure.t
      DerivedCategory.Plus.TStructure.t (upperStar A α.w).mapDerivedCategoryPlus K a
  exact ((upperStar A α.π).map_isZero
    (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      (lowerStar A α.g) ((upperStar A α.w).mapDerivedCategoryPlus.obj K) a hp)).of_iso
        (((upperStar A α.π).mapDerivedCategoryPlusHomologyFunctorIso p).app _).symm

/-- Below a common lower bound both sides of the stage comparison vanish.

Proof: exact inverse image preserves the lower bound and right derived direct image
has no homology below it. Apply this to every stage and to the limit stage. The
colimit of a diagram of zero objects is zero by its universal property, so its map
to the zero point-stage object is an isomorphism.
Source: Stacks Tag 0GIU, the vanishing start of the induction.
(blueprint: lem-sf-abelian-limit-stage-induction). -/
theorem isIso_comparison_of_lt
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A))
    (a p : ℤ) [K.IsGE a] (hp : p < a) : IsIso (comparison A S K p) := by
  have hD : IsZero (colimit (diagram A S K p)) := by
    rw [IsZero.iff_id_eq_zero]
    apply colimit.hom_ext
    intro i
    exact (stage_isZero A (S.obj i.unop) K a p hp).eq_of_src _ _
  have hP := stage_isZero A S.pt K a p hp
  have heq : comparison A S K p = (hD.iso hP).hom := hD.eq_of_src _ _
  rw [heq]
  infer_instance

/-- Continuity for all pure coefficient complexes implies continuity for every
bounded-below coefficient complex.

Proof: use finite descent on the lower cohomological bound. Below the bound all
stage homology objects vanish. Split a complex at its bottom nonzero degree into
a pure lower truncation and an upper truncation with the next lower bound. In the
five-term long exact sequence the two pure comparisons and the two upper-truncation
comparisons are isomorphisms; the five lemma gives the desired comparison.
Source: Stacks Tag 0GIU, truncation triangle and five-lemma induction.
(blueprint: lem-sf-abelian-limit-stage-induction). -/
theorem isIso_comparison_of_pure [IsCofiltered I]
    (hpure : ∀ (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) (a p : ℤ),
      K.IsGE a → K.IsLE a → IsIso (comparison A S K p))
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) (p : ℤ) :
    IsIso (comparison A S K p) := by
  apply DerivedCategory.Plus.property_of_vanishing_pure_truncation
    (fun K p ↦ IsIso (comparison A S K p)) ?_ hpure ?_ K p
  · intro L a q hL hq
    let := hL
    exact isIso_comparison_of_lt A S L a q hq
  · intro L a q hL hlow hhigh
    exact isIso_comparison_triangle A S
      ((DerivedCategory.Plus.TStructure.t.triangleLTGE (a + 1)).obj L)
      (DerivedCategory.Plus.TStructure.t.triangleLTGE_distinguished (a + 1) L) q
      (hhigh (q - 1) (by omega)) (hlow q) (hhigh q le_rfl) (hlow (q + 1))

/-- It suffices to prove continuity for sheaves placed in degree zero.

Proof: a complex concentrated in degree `a` is isomorphic to a single sheaf in
that degree. The single-functor shift isomorphism identifies this with a degree-zero
sheaf shifted by `-a`. Shift invariance and coefficient-isomorphism invariance give
the pure case; the preceding truncation induction then gives all bounded-below
complexes.
Source: Stacks Tag 0GIU, the single-sheaf base case and finite descent.
(blueprint: lem-sf-abelian-limit-stage-induction). -/
theorem isIso_comparison_of_single [IsCofiltered I]
    (hsingle : ∀ (F : Sheaf W.smallEtaleTopology A) (p : ℤ),
      IsIso (comparison A S ((DerivedCategory.Plus.singleFunctor _ 0).obj F) p))
    (K : DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) (p : ℤ) :
    IsIso (comparison A S K p) := by
  apply isIso_comparison_of_pure A S ?_ K p
  intro L a q hGE hLE
  let := hGE
  let := hLE
  obtain ⟨F, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Plus.ι.obj L) a
  let e' : L ≅ (DerivedCategory.Plus.singleFunctor _ a).obj F :=
    DerivedCategory.Plus.ι.preimageIso
      (e ≪≫ ((DerivedCategory.Plus.singleFunctorιIso _ a).app F).symm)
  let e'' := ((DerivedCategory.Plus.singleFunctors _).shiftIso (-a) a 0 (by omega)).app F
  have hshift : IsIso (comparison A S
      (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦-a⟧) q) := by
    let := hsingle F (-a + q)
    exact isIso_comparison_shift A S _ (-a) q
  have : IsIso (comparison A S (((DerivedCategory.Plus.singleFunctors _).functor 0 ⋙
      shiftFunctor (DerivedCategory.Plus (Sheaf W.smallEtaleTopology A)) (-a)).obj F) q) := by
    simpa only [Functor.comp_obj] using hshift
  exact isIso_comparison_of_iso A S (e' ≪≫ e''.symm) q

end AlgebraicGeometry.Etale.AbelianLimitStageSystem
