/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionCoherence
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence

/-!

# The refinement comparison and the projection formula

The restriction comparison `i_! ⟶ i₁_! ⋙ Lh^*` of a refinement of compactifications
(`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekRefinement`) is the abstract
restriction comparison `CategoryTheory.Adjunction.restrictionComparison` of the adjunctions
`i_! ⊣ Li^*`, `i₁_! ⊣ Li₁^*` and the triangle comparison `Li₁^* ≅ Lh^* ⋙ Li^*`
(`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekRefinement_app`), so that the
compatibilities of `ProjectionCoherence` apply to it.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Z Z₁ : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

/-- The restriction comparison of a refinement is the abstract restriction comparison. -/
lemma boundedConstructibleOpenImmersionLowerShriekRefinement_app (w : i ≫ h = i₁)
    (M : Dᵇc(X.left)⟦Λ⟧) :
    (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ w).app M =
      Adjunction.restrictionComparison
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁)
        (boundedConstructibleUpperStarTriangleComparison Λ ℓ w) M := by
  subst w
  simp [boundedConstructibleOpenImmersionLowerShriekRefinement,
    boundedConstructibleOpenImmersionLowerShriekRefinementUnitStep,
    boundedConstructibleOpenImmersionLowerShriekRefinementTriangleStep,
    boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep,
    Adjunction.restrictionComparison, Functor.squareTransport]

omit [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] in
variable [IsEllAdicFinitenessCoefficient ℓ Λ] in
/-- The triangle comparison `Li₁^* ≅ Lh^* ⋙ Li^*` is compatible with the multiplications of the
monoidal derived pullbacks. -/
lemma boundedConstructibleUpperStarTriangleComparison_μ (w : i ≫ h = i₁)
    (K M : Dᵇc(Z₁.left)⟦Λ⟧) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStar Λ ℓ i₁) K M ≫
        (boundedConstructibleUpperStarTriangleComparison Λ ℓ w).hom.app (K ⊗ M) =
      ((boundedConstructibleUpperStarTriangleComparison Λ ℓ w).hom.app K ⊗ₘ
          (boundedConstructibleUpperStarTriangleComparison Λ ℓ w).hom.app M) ≫
        Functor.LaxMonoidal.μ (boundedConstructibleUpperStar Λ ℓ i) _ _ ≫
          (boundedConstructibleUpperStar Λ ℓ i).map
            (Functor.LaxMonoidal.μ (boundedConstructibleUpperStar Λ ℓ h) K M) := by
  subst w
  refine Adjunction.μ_comp_hom_app_eq_of_δ_comp _ (fun K M ↦ ?_) K M
  simp only [boundedConstructibleUpperStarTriangleComparison, Iso.trans_hom, eqToIso_refl,
    Iso.refl_hom, Category.id_comp]
  exact boundedConstructibleUpperStarComp_hom_app_tensor_δ Λ ℓ i h K M

section Bridge

variable [IsEllAdicFinitenessCoefficient ℓ Λ] {P Q : Over (Spec (.of k))}
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]

/-- The projection morphism of the bounded constructible adjunction `Lg^* ⊣ Rg_*` is the derived
projection morphism. -/
lemma boundedConstructibleUpperStarLowerStarAdjunction_projectionMorphism_hom (g : P ⟶ Q)
    (A : Dᵇc(P.left)⟦Λ⟧) (B : Dᵇc(Q.left)⟦Λ⟧) :
    ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ g).projectionMorphism A B).hom =
      properProjectionMorphism Λ g.left A.obj B.obj :=
  ObjectProperty.projectionMorphism_restrictFullyFaithful_hom _ _
    (derivedUpperStarLowerStarAdjunction Λ g.left) _ A B


/-- The projection comparison of the bounded constructible adjunction `i_! ⊣ Li^*` along an open
immersion is the derived projection comparison. -/
lemma boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_projectionComparison_hom
    (j : P ⟶ Q) [IsOpenImmersion j.left] (M : Dᵇc(P.left)⟦Λ⟧) (N : Dᵇc(Q.left)⟦Λ⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).projectionComparison
        M N).hom =
      openImmersionProjectionComparison Λ j.left M.obj N.obj :=
  ObjectProperty.projectionComparison_restrictFullyFaithful_hom _ _
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j.left) _ M N

end Bridge

section Independence

variable [IsEllAdicFinitenessCoefficient ℓ Λ] {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

omit [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] in
/-- The projection comparison of `i_! ⊣ Li^*` on bounded constructible complexes is an
isomorphism, being the derived one. -/
instance isIso_boundedConstructibleOpenImmersionProjectionComparison {P Q : Over (Spec (.of k))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom] (j : P ⟶ Q)
    [IsOpenImmersion j.left] (M : Dᵇc(P.left)⟦Λ⟧) (N : Dᵇc(Q.left)⟦Λ⟧) :
    IsIso
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).projectionComparison
        M N) := by
  have : IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).projectionComparison
        M N)) := by
    rw [ObjectProperty.ι_map,
      boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_projectionComparison_hom]
    infer_instance
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map _

/-- **The exceptional projection morphism is independent of the compactification**, refinement
step (blueprint `prop-sf-pf-coherence`, independence clause): for a refinement `h : Z ⟶ Z₁` of
compactifications `f = i₁ ≫ p₁ = i ≫ p` (`sq`, `wp`), the refinement isomorphism
`boundedConstructibleLowerShriekRefinementIso` carries the exceptional projection morphism of
`(i₁, p₁)` to that of `(i, p)`, for identifications `cf`, `cf₁` of `Lf^*` compatible with the
triangle comparisons (`hcoh`). -/
theorem exceptionalProjection_boundedConstructibleLowerShriekRefinementIso
    (sq : IsPullback (𝟙 X) i i₁ h) {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ sq)]
    {f : X ⟶ Y}
    (cf : boundedConstructibleUpperStar Λ ℓ f ≅
      boundedConstructibleUpperStar Λ ℓ p ⋙ boundedConstructibleUpperStar Λ ℓ i)
    (cf₁ : boundedConstructibleUpperStar Λ ℓ f ≅
      boundedConstructibleUpperStar Λ ℓ p₁ ⋙ boundedConstructibleUpperStar Λ ℓ i₁)
    (hcoh : ∀ B, cf.hom.app B ≫ (boundedConstructibleUpperStar Λ ℓ i).map
        ((boundedConstructibleUpperStarTriangleComparison Λ ℓ wp).hom.app B) =
      cf₁.hom.app B ≫ (boundedConstructibleUpperStarTriangleComparison Λ ℓ
        sq.toCommSq.snd_comp_eq_of_fst_eq_id).hom.app
          ((boundedConstructibleUpperStar Λ ℓ p₁).obj B))
    (K : Dᵇc(X.left)⟦Λ⟧) (B : Dᵇc(Y.left)⟦Λ⟧) :
    Adjunction.exceptionalProjection
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁)
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p₁) cf₁ K B ≫
        (boundedConstructibleLowerShriekRefinementIso Λ ℓ sq wp).hom.app
          (K ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj B) =
      (boundedConstructibleLowerShriekRefinementIso Λ ℓ sq wp).hom.app K ▷ B ≫
        Adjunction.exceptionalProjection
          (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i)
          (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p) cf K B := by
  subst wp
  obtain rfl := sq.toCommSq.snd_comp_eq_of_fst_eq_id
  have hρ := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ sq
  have : ∀ M, IsIso (Adjunction.restrictionComparison
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ (i ≫ h))
      (boundedConstructibleUpperStarTriangleComparison Λ ℓ
        sq.toCommSq.snd_comp_eq_of_fst_eq_id) M) := fun M ↦ by
    rw [← boundedConstructibleOpenImmersionLowerShriekRefinement_app]
    infer_instance
  have key := Adjunction.exceptionalProjection_comp_refinement
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ (i ≫ h))
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ (h ≫ p₁))
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p₁)
    (boundedConstructibleUpperStarTriangleComparison Λ ℓ sq.toCommSq.snd_comp_eq_of_fst_eq_id)
    (boundedConstructibleUpperStarTriangleComparison Λ ℓ (rfl : h ≫ p₁ = h ≫ p₁)) cf cf₁
    (fun X Y ↦ by
      refine Adjunction.μ_comp_hom_app_eq_of_δ_comp _ (fun K M ↦ ?_) X Y
      simp only [boundedConstructibleUpperStarTriangleComparison, Iso.trans_hom, eqToIso_refl,
        Iso.refl_hom, Category.id_comp]
      exact boundedConstructibleUpperStarComp_hom_app_tensor_δ Λ ℓ i h K M)
    (fun X Y ↦ by
      simp only [boundedConstructibleUpperStarTriangleComparison, Iso.trans_hom, eqToIso_refl,
        Iso.refl_hom, Category.id_comp]
      exact boundedConstructibleUpperStarComp_hom_app_tensor_δ Λ ℓ h p₁ X Y)
    hcoh K B
  have hR : ∀ M, (boundedConstructibleLowerShriekRefinementIso Λ ℓ sq rfl).hom.app M =
      (boundedConstructibleLowerStar Λ ℓ p₁).map
        ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit.app
            ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ (i ≫ h)).obj M) ≫
          (boundedConstructibleLowerStar Λ ℓ h).map (inv (Adjunction.restrictionComparison
            (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i)
            (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ (i ≫ h))
            (boundedConstructibleUpperStarTriangleComparison Λ ℓ
              sq.toCommSq.snd_comp_eq_of_fst_eq_id) M))) ≫
        (conjugateIsoEquiv ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p₁).comp
            (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h))
          (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ (h ≫ p₁))
          (boundedConstructibleUpperStarTriangleComparison Λ ℓ (rfl : h ≫ p₁ = h ≫ p₁))).hom.app
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i).obj M) := by
    intro M
    simp only [boundedConstructibleLowerShriekRefinementIso,
      boundedConstructibleOpenImmersionLowerShriekRefinementPushforward, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, asIso_hom, eqToIso_refl, Iso.trans_refl]
    simp only [Functor.rightUnitor_inv_app, Functor.associator_inv_app, Functor.associator_hom_app,
      Category.id_comp, NatIso.isIso_inv_app,
      boundedConstructibleOpenImmersionLowerShriekRefinement_app]
    congr 1
    simp only [boundedConstructibleLowerStarComp, boundedConstructibleUpperStarTriangleComparison,
      eqToIso_refl, Iso.refl_trans]
    rfl
  rw [hR, hR]
  exact key

end Independence

end AlgebraicGeometry.ProEtale.CondensedRing
