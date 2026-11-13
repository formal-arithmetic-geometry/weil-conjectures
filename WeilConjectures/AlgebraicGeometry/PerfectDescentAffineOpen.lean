/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectDescentOnOpen
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.AffineDescentColimitModel
import WeilConjectures.AlgebraicGeometry.AffineDescentStageRealization
import WeilConjectures.Algebra.Homology.AffinePerfectColimitDescent
import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.PerfectComplex

/-! # Descent of perfect complexes on an affine open

## References

* Stacks Project, Tag 09RF.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Perfect complexes descend on an affine open, and on the empty open
(Stacks, Tags 09RF, 0BC7 and 08EB). -/
theorem perfect_descent_affine_open
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ i : I, IsNoetherianRing (R.obj i)]
    (c : Cocone R) (hc : IsColimit c) (i : I) (Xi : Scheme.{u}) (s : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (U : Xi.Opens) (hU : IsAffineOpen U ∨ U = ⊥) :
    PerfectDescentOnOpen R c i Xi s U := by
  have hUaff : IsAffineOpen U := hU.elim id (fun h ↦ h ▸ isAffineOpen_bot Xi)
  intro Z f _ hf
  dsimp only
  intro E hE
  have hZ : IsAffine Z := by
    have hRange : IsAffineOpen f.opensRange := hf ▸ hUaff
    have htop : IsAffineOpen (⊤ : Z.Opens) := by
      apply (f.isAffineOpen_iff_of_isOpenImmersion).mp
      simpa using hRange
    let : IsAffine (⊤ : Z.Opens).toScheme := htop
    exact IsAffine.of_isIso Z.topIso.inv
  let : IsAffine Z := hZ
  let t := f ≫ s
  let F := affineDescentRings R i t
  let : Nonempty (Set.Ici i) := ⟨⟨i, le_rfl⟩⟩
  let : IsDirected (Set.Ici i) (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨k, ha, hb⟩ := IsDirected.directed (r := (· ≤ ·)) a.val b.val
    exact ⟨⟨k, a.property.trans ha⟩, ha, hb⟩⟩
  obtain ⟨P, hb, hfinite, hprojective, ⟨e⟩⟩ :=
    exists_affine_descent_colimit_model R c i Z t hc E hE
  obtain ⟨j, Pj, hbj, hfj, hpj, ⟨eP⟩⟩ :=
    CochainComplex.exists_finite_projective_model_of_directed_colimit
      F P hb hfinite hprojective
  obtain ⟨hperfect, ⟨ePull⟩⟩ :=
    affine_descent_stage_realization R c i Z t j Pj hbj hfj hpj
  refine ⟨j.val, j.property,
    (affineDescentRealization (affineDescentStage R i t j)
      (F.obj j) (𝟙 _)).obj Pj, hperfect, ?_⟩
  exact ⟨ePull ≪≫ (affineDescentRealization (pullback t (Spec.map (c.ι.app i)))
    (colimit F) (colimit.desc F (affineDescentRingCocone R i t c))).mapIso eP ≪≫ e⟩

end AlgebraicGeometry
