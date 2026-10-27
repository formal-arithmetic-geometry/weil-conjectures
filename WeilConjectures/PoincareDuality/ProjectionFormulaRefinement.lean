/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormulaOfCompactification
public import WeilConjectures.PoincareDuality.ProjectionRefinementAbstract
public import WeilConjectures.PoincareDuality.RefinementProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp

/-!

# The exceptional projection morphism and refinements of compactifications

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The condensed field `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

variable {X Z Z₁ Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

set_option profiler true in
/-- **The projection morphism of a composite** `h ≫ p₁` on bounded constructible complexes: the
projection morphism of `Lp₁^* ⊣ Rp₁_*` followed by `Rp₁_*` of that of `Lh^* ⊣ Rh_*`, through the
composition isomorphisms. -/
lemma boundedConstructibleProjectionMorphism_comp (h : Z ⟶ Z₁) (p₁ : Z₁ ⟶ Y)
    (A : Dᵇc(Z.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧) :
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (h ≫ p₁)).projectionMorphism A B =
      (boundedConstructibleLowerStarComp ℓ h p₁).inv.app A ▷ B ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ p₁).projectionMorphism
          ((boundedConstructibleLowerStar ℓ h).obj A) B ≫
        (boundedConstructibleLowerStar ℓ p₁).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ h).projectionMorphism A
            ((boundedConstructibleUpperStar _ ℓ p₁).obj B)) ≫
        (boundedConstructibleLowerStarComp ℓ h p₁).hom.app _ ≫
        (boundedConstructibleLowerStar ℓ (h ≫ p₁)).map
          (A ◁ (boundedConstructibleUpperStarComp _ ℓ h p₁).inv.app B) := by
  rw [Adjunction.projectionMorphism_eq_of_iso _
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ p₁).comp
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ h))
    (boundedConstructibleUpperStarComp _ ℓ h p₁) (fun M N ↦ by
      rw [Functor.OplaxMonoidal.comp_δ]
      exact boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ h p₁ M N) A B,
    Adjunction.projectionMorphism_comp]
  simp only [Category.assoc]
  rfl

section Refinement

variable {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

set_option profiler true in
/-- The comparison `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement is `Rp₁_*` of the abstract
pushforward comparison `CategoryTheory.Adjunction.refinementPushforward`, followed by the
composition isomorphism. -/
lemma boundedConstructibleLowerShriekRefinementIso_hom_app (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ sq)]
    [∀ M, IsIso (Adjunction.restrictionComparison
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ i)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ i₁)
      (boundedConstructibleUpperStarTriangleComparison 𝐐 ℓ
        sq.toCommSq.snd_comp_eq_of_fst_eq_id) M)]
    (M : Dᵇc(X.left)⟦𝐐⟧) :
    (boundedConstructibleLowerShriekRefinementIso ℓ sq (p₁ := p₁) rfl).hom.app M =
      (boundedConstructibleLowerStar ℓ p₁).map (Adjunction.refinementPushforward
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ i)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ i₁)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ h)
        (boundedConstructibleUpperStarTriangleComparison 𝐐 ℓ
          sq.toCommSq.snd_comp_eq_of_fst_eq_id) M) ≫
        (boundedConstructibleLowerStarComp ℓ h p₁).hom.app _ := by
  have hR := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement 𝐐 ℓ sq
  simp only [boundedConstructibleLowerShriekRefinementIso,
    boundedConstructibleOpenImmersionLowerShriekRefinementPushforward, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, asIso_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, eqToIso_refl, Iso.refl_hom,
    Category.id_comp, Category.comp_id, Functor.map_comp, NatIso.isIso_inv_app]
  simp only [boundedConstructibleOpenImmersionLowerShriekRefinement_app,
    Adjunction.refinementPushforward, Functor.map_comp]

set_option profiler true in
omit [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] in
/-- The composition isomorphisms of the pullbacks along `i₁ = i ≫ h` and `f = i₁ ≫ p₁ = i ≫ h ≫ p₁`
are compatible. -/
lemma boundedConstructibleUpperStarComp_refinement_hom_app {p₁ : Z₁ ⟶ Y} {f : X ⟶ Y}
    (w : i ≫ h = i₁) (hf₁ : i₁ ≫ p₁ = f) (hf : i ≫ h ≫ p₁ = f) (B : Dᵇc(Y.left)⟦𝐐⟧) :
    (eqToIso (congrArg (boundedConstructibleUpperStar 𝐐 ℓ) hf₁.symm) ≪≫
        boundedConstructibleUpperStarComp 𝐐 ℓ i₁ p₁).hom.app B ≫
      (boundedConstructibleUpperStarTriangleComparison 𝐐 ℓ w).hom.app
        ((boundedConstructibleUpperStar 𝐐 ℓ p₁).obj B) =
    (eqToIso (congrArg (boundedConstructibleUpperStar 𝐐 ℓ) hf.symm) ≪≫
        boundedConstructibleUpperStarComp 𝐐 ℓ i (h ≫ p₁)).hom.app B ≫
      (boundedConstructibleUpperStar 𝐐 ℓ i).map
        ((boundedConstructibleUpperStarComp 𝐐 ℓ h p₁).hom.app B) := by
  subst w hf₁
  simp only [boundedConstructibleUpperStarTriangleComparison, Iso.trans_hom, NatTrans.comp_app,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp, Category.assoc,
    boundedConstructibleUpperStarComp_assoc_app, eqToIso.hom, eqToHom_app, eqToHom_trans_assoc]
  rw [eqToHom_refl, Category.id_comp]

set_option profiler true in
/-- **The comparison along a refinement intertwines the exceptional projection morphisms**: for
factorizations `f = i ≫ p` and `f = i₁ ≫ p₁` into open immersions followed by morphisms and a
refinement `h` (`i ≫ h = i₁` cartesian, `h ≫ p₁ = p`), the comparison
`ρ : i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` carries the exceptional projection morphism of `(i₁, p₁)` to that
of `(i, p)` (blueprint `prop-sf-pf-coherence`; SGA 4, Exposé XVII, 5.2.2). -/
theorem boundedConstructibleLowerShriekRefinementIso_hom_app_whiskerRight_comp
    (sq : IsPullback (𝟙 X) i i₁ h) {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p) {f : X ⟶ Y}
    (hf : i ≫ p = f) (hf₁ : i₁ ≫ p₁ = f)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ sq)]
    (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧) :
    (boundedConstructibleLowerShriekRefinementIso ℓ sq wp).hom.app K ▷ B ≫
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ p).projectionMorphism
          ((boundedConstructibleOpenImmersionLowerShriek 𝐐 ℓ i).obj K) B ≫
        (boundedConstructibleLowerStar ℓ p).map
          (inv ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ
              i).projectionComparison K ((boundedConstructibleUpperStar 𝐐 ℓ p).obj B)) ≫
            (boundedConstructibleOpenImmersionLowerShriek 𝐐 ℓ i).map
              (K ◁ (eqToIso (congrArg (boundedConstructibleUpperStar 𝐐 ℓ) hf.symm) ≪≫
                boundedConstructibleUpperStarComp 𝐐 ℓ i p).inv.app B)) =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ p₁).projectionMorphism
          ((boundedConstructibleOpenImmersionLowerShriek 𝐐 ℓ i₁).obj K) B ≫
        (boundedConstructibleLowerStar ℓ p₁).map
          (inv ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ
              i₁).projectionComparison K ((boundedConstructibleUpperStar 𝐐 ℓ p₁).obj B)) ≫
            (boundedConstructibleOpenImmersionLowerShriek 𝐐 ℓ i₁).map
              (K ◁ (eqToIso (congrArg (boundedConstructibleUpperStar 𝐐 ℓ) hf₁.symm) ≪≫
                boundedConstructibleUpperStarComp 𝐐 ℓ i₁ p₁).inv.app B)) ≫
        (boundedConstructibleLowerShriekRefinementIso ℓ sq wp).hom.app
          (K ⊗ (boundedConstructibleUpperStar 𝐐 ℓ f).obj B) := by
  subst wp hf
  obtain rfl : i ≫ h = i₁ := sq.toCommSq.snd_comp_eq_of_fst_eq_id
  have hR := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement 𝐐 ℓ sq
  have : ∀ M, IsIso (Adjunction.restrictionComparison
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ i)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ (i ≫ h))
      (boundedConstructibleUpperStarTriangleComparison 𝐐 ℓ
        sq.toCommSq.snd_comp_eq_of_fst_eq_id) M) := fun M ↦ by
    rw [← boundedConstructibleOpenImmersionLowerShriekRefinement_app]
    infer_instance
  rw [boundedConstructibleLowerShriekRefinementIso_hom_app,
    boundedConstructibleLowerShriekRefinementIso_hom_app]
  have key := Adjunction.whiskerRight_refinement_comp_exceptionalProjection
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ i)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction 𝐐 ℓ (i ≫ h))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ h)
    (boundedConstructibleUpperStarTriangleComparison 𝐐 ℓ sq.toCommSq.snd_comp_eq_of_fst_eq_id)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (h ≫ p₁))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ p₁)
    (fun K M ↦ by
      refine Adjunction.μ_comp_hom_app_eq_of_δ _ (fun K M ↦ ?_) K M
      simp only [boundedConstructibleUpperStarTriangleComparison, Iso.trans_hom, eqToIso_refl,
        Iso.refl_hom, Category.id_comp, Functor.OplaxMonoidal.comp_δ]
      exact boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ i h K M)
    (boundedConstructibleLowerStarComp ℓ h p₁) (boundedConstructibleUpperStarComp 𝐐 ℓ h p₁)
    (boundedConstructibleProjectionMorphism_comp ℓ h p₁)
    (eqToIso (congrArg (boundedConstructibleUpperStar 𝐐 ℓ) rfl) ≪≫
      boundedConstructibleUpperStarComp 𝐐 ℓ i (h ≫ p₁))
    (eqToIso (congrArg (boundedConstructibleUpperStar 𝐐 ℓ) hf₁.symm) ≪≫
      boundedConstructibleUpperStarComp 𝐐 ℓ (i ≫ h) p₁)
    (boundedConstructibleUpperStarComp_refinement_hom_app ℓ
      sq.toCommSq.snd_comp_eq_of_fst_eq_id hf₁ rfl) K B
  simpa only [Category.assoc] using key

end Refinement

end AlgebraicGeometry.ProEtale.CondensedRing
