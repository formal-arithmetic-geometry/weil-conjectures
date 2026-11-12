/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceInvariantsAverage
public import WeilConjectures.TraceFormula.Specialization.TraitSliceInvariantsDegree
public import WeilConjectures.TraceFormula.Specialization.TraitSliceInvariantsIntegralModel

/-!

# The slicing exchange as the inclusion of the invariants, granted the cartesian step

Let `M''` be the base change of a model `M` of finite type over `S = Spec k'⟦t⟧` along
`v : Spec K⟦t⟧ ⟶ Y`, `K` algebraically closed, and `φ : M'' ⟶ M` the projection. It factors as
`M'' ⟶ N''_{L^sep} ⟶ N'' ⟶ M` through the Galois layer of the change-of-traits model `N''`
(`NearbyCyclesModel.baseChangeGaloisModel`), the last arrow `χ` being its cartesian part. Granted
that the pullback exchange of `χ` is invertible ("M1 at `T`", an explicit hypothesis), the
slicing exchange `α_φ` is the inclusion of the invariants of the generic automorphisms
(`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_of_isIso_cartesian`): a
subgroup `V` of finite index acts trivially and `α_φ` is split by the average over `P' ⧸ V`.

The proof applies the stabilization of nearby cycles along Galois layers to `N''`
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_integralModel`, with the
integral model of `NearbyCyclesModel.exists_integralModel_baseChangeGaloisModel` and the degrees of
`AlgebraicGeometry.not_dvd_finrank_traitTensorCompositum`), transports the average along
`M'' ⟶ N''_{L^sep}` and `χ`
(`NearbyCyclesModel.exists_retraction_pullbackExchange_of_comp_galoisLayer`), and reindexes it by
`P' ⧸ V ≃ Gal(L₁ / L)` (`MonoidHom.card_nsmul_eq_sum_quotient_ker'`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme PadicAlgCl

attribute [local instance] traitGenericFieldAlgebra

/-- Constructibility of a derived pullback passes to any further factorization. -/
private lemma boundedConstructible_leftDerivedUpperStar_obj_of_factorization
    {Z Y X : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X) (hfg : f ≫ g = fg)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hA : boundedConstructible (condensedRingObj Λ Y) (L((g)^*⟦Λ⟧).obj A)) :
    boundedConstructible (condensedRingObj Λ Z) (L((fg)^*⟦Λ⟧).obj A) :=
  (boundedConstructible _).prop_of_iso ((leftDerivedUpperStarCompOfEq Λ hfg).app A).symm
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ f _ hA)

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {Y : Scheme.{u}} (b : M.total ⟶ Y) {p : Y ⟶ trait k'}
  (hb : b ≫ p = q) (v : trait K ⟶ Y) (hv : v ≫ p = traitMap k' K)
  {ℓ : ℕ} [Fact ℓ.Prime]

/-- The total-space component of `M'' ⟶ N''_{L^sep} ⟶ N'' ⟶ M` is that of `M'' ⟶ M`. -/
lemma baseChangeToGaloisModel_comp_total :
    ((baseChangeToGaloisLayer hM b hb v hv).total ≫
      ((baseChangeGaloisModel hM b hb v hv).galoisLayerHom
        (baseChangeGaloisResidue hM b hb v hv) (traitTensorCompositumSep (PowerSeries K)
          (traitGenericField k') (traitGenericField K))).total) ≫
      (((baseChangeHom hM b hb v hv).traitChangeModelHom (traitGenericField K)
        (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
        (baseChangeHom_total_comp hM b hb v hv)).comp
          (baseChangeHom hM b hb v hv).fromCartesian).total =
      (baseChangeHom hM b hb v hv).total := by
  simp

/-- The generic component of `M'' ⟶ N''_{L^sep} ⟶ N'' ⟶ M` is that of `M'' ⟶ M`. -/
lemma baseChangeToGaloisModel_comp_generic :
    ((baseChangeToGaloisLayer hM b hb v hv).generic ≫
      ((baseChangeGaloisModel hM b hb v hv).galoisLayerHom
        (baseChangeGaloisResidue hM b hb v hv) (traitTensorCompositumSep (PowerSeries K)
          (traitGenericField k') (traitGenericField K))).generic) ≫
      (((baseChangeHom hM b hb v hv).traitChangeModelHom (traitGenericField K)
        (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
        (baseChangeHom_total_comp hM b hb v hv)).comp
          (baseChangeHom hM b hb v hv).fromCartesian).generic =
      (baseChangeHom hM b hb v hv).generic := by
  rw [Hom.comp_generic, Category.assoc]
  exact (baseChangeToGaloisLayer_generic_fst_fst_assoc hM b hb v hv _).trans
    (pullback.lift_fst _ _ _)

set_option trace.profiler true in
/-- **The slicing exchange is the inclusion of the invariants, given the cartesian step**: if the
pullback exchange of the cartesian part `χ : N'' ⟶ M` of the base change is invertible at `A`
(`hM1`) and `Lε^* A ≅ Lj^* B` for a bounded constructible `B` on the total space, a subgroup `V` of
finite index of the generic automorphisms acts trivially on `Ψ_{M''} A`, and the pullback
exchange of `M'' ⟶ M` has a retraction `r` with `[P' : V] • (r ≫ α) = ∑_{σ ∈ P' ⧸ V} σ`. -/
theorem exists_subgroup_pullbackExchange_baseChangeHom_of_isIso_cartesian [IsSeparated p]
    [IsAlgClosed K] [Fact (ringChar k' ≠ ℓ)]
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)
      (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))}
    (hB : boundedConstructible _ B)
    (eB : L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B ≅
      L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A)
    (hM1 : IsIso (((((baseChangeHom hM b hb v hv).traitChangeModelHom (traitGenericField K)
        (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
        (baseChangeHom_total_comp hM b hb v hv)).comp
          (baseChangeHom hM b hb v hv).fromCartesian).pullbackExchange
            (Profinite.padicAlgClRingObj ℓ)).app A)) :
    ∃ (V : Subgroup (GenericAut k' K)) (_ : Fintype (GenericAut k' K ⧸ V)),
      (∀ σ ∈ V, (baseChangeAut hM b hb v hv σ).autAction (Profinite.padicAlgClRingObj ℓ)
          (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) = 𝟙 _) ∧
      ∃ r, ((baseChangeHom hM b hb v hv).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app A ≫
          r = 𝟙 _ ∧
        Fintype.card (GenericAut k' K ⧸ V) •
          (r ≫ ((baseChangeHom hM b hb v hv).pullbackExchange
            (Profinite.padicAlgClRingObj ℓ)).app A) =
        ∑ σ : GenericAut k' K ⧸ V, (baseChangeAut hM b hb v hv σ.out).autAction
          (Profinite.padicAlgClRingObj ℓ) (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) := by
  have hT := IsTraitModelOver.baseChange hM b hb v hv
  have : LocallyOfFiniteType (baseChangeTotalStructure hM b hb v hv) := hT.locallyOfFiniteType
  have : QuasiCompact (baseChangeTotalStructure hM b hb v hv) := hT.quasiCompact
  have := hT.locallyOfFiniteType
  have := hT.quasiCompact
  have := hT.isSeparated
  have hc := (baseChangeHom hM b hb v hv).isPullback_cartesianModelTensor hM.isPullback_j
    (baseChangeHom_total_comp hM b hb v hv)
  have : LocallyOfFiniteType ((baseChangeHom hM b hb v hv).cartesianModelTensor
      (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
      (baseChangeHom_total_comp hM b hb v hv)) := MorphismProperty.of_isPullback hc.flip ‹_›
  have : QuasiCompact ((baseChangeHom hM b hb v hv).cartesianModelTensor
      (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
      (baseChangeHom_total_comp hM b hb v hv)) := MorphismProperty.of_isPullback hc.flip ‹_›
  have : LocallyOfFiniteType (baseChangeGaloisResidue hM b hb v hv) :=
    MorphismProperty.pullback_snd _ _ ‹_›
  have : QuasiCompact (baseChangeGaloisResidue hM b hb v hv) :=
    MorphismProperty.pullback_snd _ _ ‹_›
  have : IsLocallyNoetherian (baseChangeGaloisModel hM b hb v hv).generic :=
    LocallyOfFiniteType.isLocallyNoetherian (baseChangeGaloisResidue hM b hb v hv)
  have : CompactSpace (baseChangeGaloisModel hM b hb v hv).generic :=
    QuasiCompact.compactSpace_of_compactSpace (baseChangeGaloisResidue hM b hb v hv)
  have : IsNoetherian (baseChangeGaloisModel hM b hb v hv).generic := ⟨⟩
  have : QuasiCompact (baseChangeSpecial b v).hom := 
    MorphismProperty.of_isPullback hT.isPullback_i ‹_›
  have : IsSeparated (baseChangeSpecial b v).hom := 
    MorphismProperty.of_isPullback hT.isPullback_i ‹_›
  have : CompactSpace (baseChangeGaloisModel hM b hb v hv).total :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd b v)
  have : QuasiSeparatedSpace (baseChangeGaloisModel hM b hb v hv).total :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd b v)
  have : CompactSpace (baseChangeSpecial b v).left :=
    QuasiCompact.compactSpace_of_compactSpace (baseChangeSpecial b v).hom
  have : QuasiSeparatedSpace (baseChangeSpecial b v).left :=
    quasiSeparatedSpace_of_quasiSeparated (baseChangeSpecial b v).hom
  have hC := boundedConstructible_leftDerivedUpperStar_obj_of_factorization
    (Z := (baseChangeGaloisModel hM b hb v hv).generic)
    ((baseChangeHom hM b hb v hv).traitChangeThickening (traitGenericField K)
      (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
      (baseChangeHom_total_comp hM b hb v hv) ≫ pullback.fst _ _)
    M.ε (baseChangeGaloisModel hM b hb v hv).ε (Category.assoc _ _ _)
    (Profinite.padicAlgClRingObj ℓ) A hA
  refine (exists_integralModel_baseChangeGaloisModel hM b hb v hv hB eB hC).elim fun E hE ↦ ?_
  refine hE.elim fun K₀ hK₀ ↦ ?_
  refine hK₀.elim fun e htors ↦ ?_
  obtain ⟨L₁, htriv, hSA⟩ := (baseChangeGaloisModel hM b hb v hv)
    |>.exists_retraction_pullbackExchange_galoisLayerHom_of_integralModel
      (baseChangeGaloisResidue hM b hb v hv) _ ℓ
      (fun M' _ ↦ IntermediateField.not_dvd_finrank_of_forall_finiteGalois
        (not_dvd_finrank_traitTensorCompositum (K := K) (Fact.out : ringChar k' ≠ ℓ) Fact.out) M')
      A hC E K₀ e htors
  have htriv' (σ : GenericAut k' K)
      (hσ : GenericAut.galoisEquiv σ ∈ L₁.toIntermediateField.fixingSubgroup) :
      (baseChangeAut hM b hb v hv σ).autAction (Profinite.padicAlgClRingObj ℓ)
        (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) = 𝟙 _ := by
    have h₂ : ((baseChangeGaloisModel hM b hb v hv).galoisLayerAut
        (baseChangeGaloisResidue hM b hb v hv) (traitTensorCompositumSep (PowerSeries K)
            (traitGenericField k') (traitGenericField K)) (GenericAut.galoisEquiv σ)).autAction
          (Profinite.padicAlgClRingObj ℓ) A = 𝟙 _ :=
      eq_id_of_naturality_of_iso _ (fun g ↦ Hom.autAction_naturality _ _ g)
        ((leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) X).app A).symm (htriv _ hσ)
    have := isIso_pullbackExchange_baseChangeToGaloisLayer hM b hb v hv
      (Profinite.padicAlgClRingObj ℓ) A
    have key := pullbackExchange_baseChangeToGaloisLayer_app_comp_autAction hM b hb v hv
      (Profinite.padicAlgClRingObj ℓ) σ A
    rw [h₂, CategoryTheory.Functor.map_id, Category.id_comp] at key
    exact (cancel_epi _).1 (key.trans (Category.comp_id _).symm)
  obtain ⟨r, hr, havg⟩ := exists_retraction_pullbackExchange_of_comp_galoisLayer
    (Profinite.padicAlgClRingObj ℓ) (baseChangeToGaloisLayer hM b hb v hv)
    ((baseChangeGaloisModel hM b hb v hv).galoisLayerHom (baseChangeGaloisResidue hM b hb v hv)
      (traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K)))
    (((baseChangeHom hM b hb v hv).traitChangeModelHom (traitGenericField K)
      (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
      (baseChangeHom_total_comp hM b hb v hv)).comp (baseChangeHom hM b hb v hv).fromCartesian)
    (baseChangeHom hM b hb v hv) (baseChangeToGaloisModel_comp_total hM b hb v hv)
    (baseChangeToGaloisModel_comp_generic hM b hb v hv) A
    (isIso_pullbackExchange_baseChangeToGaloisLayer hM b hb v hv _) (by transport_exact hM1)
    Finset.univ
    (fun τ : L₁.toIntermediateField ≃ₐ[traitTensorCompositum (PowerSeries K)
        (traitGenericField k') (traitGenericField K)] L₁.toIntermediateField ↦
      baseChangeAut hM b hb v hv (GenericAut.galoisEquiv.symm (τ.liftNormal _)))
    (fun τ ↦ (baseChangeGaloisModel hM b hb v hv).galoisLayerAut
      (baseChangeGaloisResidue hM b hb v hv)
      (traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K))
      (τ.liftNormal _))
    (Fintype.card _) (by exact_mod_proofs hSA)
    (fun τ D ↦ pullbackExchange_baseChangeToGaloisLayer_app_comp_autAction_symm hM b hb v hv
      (Profinite.padicAlgClRingObj ℓ) (τ.liftNormal _) D)
  obtain ⟨π, hπdef⟩ : ∃ π : GenericAut k' K →* (L₁.toIntermediateField ≃ₐ[traitTensorCompositum
      (PowerSeries K) (traitGenericField k') (traitGenericField K)] L₁.toIntermediateField),
      π = (AlgEquiv.restrictNormalHom L₁.toIntermediateField).comp
        (GenericAut.galoisEquiv (k' := k') (K := K)).toMonoidHom := ⟨_, rfl⟩
  have hπ : Function.Surjective π := by
    rw [hπdef]
    exact (AlgEquiv.restrictNormalHom_surjective _).comp (GenericAut.galoisEquiv).surjective
  have hker (σ : GenericAut k' K) (hσ : σ ∈ π.ker) :
      GenericAut.galoisEquiv σ ∈ L₁.toIntermediateField.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]
    rw [hπdef] at hσ
    exact hσ
  have _ : Fintype (GenericAut k' K ⧸ π.ker) :=
    Fintype.ofEquiv _ (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv.symm
  refine ⟨π.ker, inferInstance, fun σ hσ ↦ htriv' σ (hker σ hσ), r, by transport_exact hr, ?_⟩
  have key := MonoidHom.card_nsmul_eq_sum_quotient_ker' havg π hπ
    (fun σ ↦ (baseChangeAut hM b hb v hv σ).autAction (Profinite.padicAlgClRingObj ℓ) _)
    (fun σ w hw ↦ by
      rw [autAction_baseChangeAut_mul]
      refine (congrArg (· ≫ _) ?_).trans (Category.id_comp _)
      exact_mod_proofs htriv' w (hker w hw))
    (fun τ ↦ GenericAut.galoisEquiv.symm (τ.liftNormal _))
    (fun τ ↦ by
      simp only [hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact τ.restrict_liftNormal _) (fun _ ↦ rfl)
  transport_exact key

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
