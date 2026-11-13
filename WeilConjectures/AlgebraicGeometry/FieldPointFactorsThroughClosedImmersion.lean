/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism

/-!
# Field-valued points factor through closed immersions

## References

* Stacks Project, Schemes, Lemma Tag 0356 (applied to `Spec K`), Definition Tag 01HK and
  Lemma Tag 01L7.
-/

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry

/--
Let `i : Z ⟶ X` be a closed immersion of schemes, let `K` be a field,
and let `s : Spec K ⟶ X` have image point `i z`. Then there is exactly one
morphism `s' : Spec K ⟶ Z` with `s' ≫ i = s`, and its unique point maps to `z`.
-/
theorem field_point_factors_through_closed_immersion
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {K : Type u} [Field K]
    (s : Spec (.of K) ⟶ X) (z : Z)
    (h : s.base (default : Spec (.of K)) = i.base z) :
    (∃! s' : Spec (.of K) ⟶ Z, s' ≫ i = s) ∧
      ∀ s' : Spec (.of K) ⟶ Z, s' ≫ i = s → s'.base (default : Spec (.of K)) = z := by
  have hr : IsIso (i.residueFieldMap z) :=
    i.isIso_residueFieldMap z
  have hx : s (IsLocalRing.closedPoint K) = i z := by
    simpa only [Subsingleton.elim (IsLocalRing.closedPoint K)
      (default : Spec (.of K))] using h
  obtain ⟨φ, hφ⟩ : ∃ φ : X.residueField (i z) ⟶ .of K,
      Spec.map φ ≫ X.fromSpecResidueField (i z) = s := by
    exact ⟨(X.residueFieldCongr hx).inv ≫
      X.descResidueField (Scheme.stalkClosedPointTo s), by
        rw [Spec.map_comp, Category.assoc]
        simp only [Scheme.residueFieldCongr_inv,
          Scheme.residueFieldCongr_fromSpecResidueField]
        exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X s⟩
  let s' : Spec (.of K) ⟶ Z :=
    Spec.map (inv (i.residueFieldMap z) ≫ φ) ≫ Z.fromSpecResidueField z
  have hs' : s' ≫ i = s := by
    dsimp only [s']
    rw [Category.assoc, ← i.SpecMap_residueFieldMap_fromSpecResidueField z,
      ← Spec.map_comp_assoc]
    simpa only [IsIso.hom_inv_id_assoc] using hφ
  constructor
  · exact ⟨s', hs', fun t ht ↦ (cancel_mono i).1 (ht.trans hs'.symm)⟩
  · intro t ht
    apply i.isEmbedding.injective
    calc
      i (t (default : Spec (.of K))) = (t ≫ i) (default : Spec (.of K)) := rfl
      _ = s (default : Spec (.of K)) := congrArg
        (fun f : Spec (.of K) ⟶ X ↦ f (default : Spec (.of K))) ht
      _ = i z := h

end AlgebraicGeometry
