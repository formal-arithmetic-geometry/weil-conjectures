/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Paper.ContinuousIntegralLocalizationModel

/-! # Transporting localization colimits from a strict complex model -/

@[expose] public section

universe u v w x y z
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

private noncomputable def sequenceComparison
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] (C : A) (K : B) (e : F.obj C ≅ K) :
    integralLocalizationSequence ℓ C ⋙ F ⟶ integralLocalizationSequence ℓ K :=
  NatTrans.ofSequence (fun _ ↦ e.hom) (by
    intro n
    simp only [CategoryTheory.Functor.comp_map, integralLocalizationSequence,
      Functor.ofSequence_map_homOfLE_succ]
    change F.map (ℓ • 𝟙 C) ≫ e.hom = e.hom ≫ (ℓ • 𝟙 K)
    rw [F.map_nsmul, F.map_id]
    simp)

omit [Fact ℓ.Prime] in
/-- Transport colimits from a strict complex telescope along its localization-unit model.
Source: Bhatt--Scholze, Lemma 6.8.2.
(blueprint: lem-weil-pbc-integral-localization-colimit-transport).
Proof: whisker the representative isomorphism to identify the diagrams, and use the
model vertex isomorphism and its leg equations to identify the cocones. -/
theorem localizationCocone_isColimit_of_model
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory A]
    [HasColimitsOfShape (ULift.{x} ℕ) A]
    (K : DerivedCategory A) (c : Cocone (integralLocalizationSequence ℓ K))
    (m : IntegralLocalizationComplexModel.{v, w, x} ℓ K c)
    {B : Type y} [Category.{z} B] (F : DerivedCategory A ⥤ B)
    (hcont : ∀ (C : CochainComplex A ℤ) (a : ℤ), C.IsStrictlyGE a →
      Nonempty (IsColimit ((DerivedCategory.Q ⋙ F).mapCocone
        (condensedContinuityCocone
          (integralLocalizationLiftedSequence.{max v w, w, x} ℓ C) a)))) :
    Nonempty (IsColimit (F.mapCocone (c.whisker
      (ULift.orderIso : ULift.{x} ℕ ≃o ℕ).equivalence.functor))) := by
  let C := m.complex
  let a := m.bound
  let e := m.representative
  let v := m.comparison
  have hv := m.leg
  have hC := m.strictlyGE
  let J := (ULift.orderIso : ULift.{x} ℕ ≃o ℕ).equivalence.functor
  let D := integralLocalizationLiftedSequence.{max v w, w, x} ℓ C
  let α₀ := sequenceComparison ℓ DerivedCategory.Q C K e.symm
  let α := Functor.whiskerRight (Functor.whiskerLeft J α₀) F
  have : ∀ n, IsIso (α.app n) := fun n ↦ by
    change IsIso (F.map e.inv)
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let cF := F.mapCocone (c.whisker J)
  obtain ⟨hc⟩ := hcont C a hC
  refine ⟨(IsColimit.precomposeHomEquiv (asIso α) cF) ?_⟩
  apply hc.ofIsoColimit
  refine Cocone.ext (F.mapIso v) ?_
  intro n
  change F.map (DerivedCategory.Q.map
      ((condensedContinuityCocone D a).ι.app n)) ≫ F.map v.hom =
    F.map e.inv ≫ F.map (c.ι.app n.down)
  rw [← F.map_comp, ← F.map_comp, hv]

end AlgebraicGeometry.ProEtale.CondensedRing
