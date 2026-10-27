/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DeformationTraceSpecialization
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityExchange
public import WeilConjectures.Tactic.MatchTactic

/-!

# Nearby cycles of the universal kernel, abstractly

Let `S_X`, `S_{X×X}` be nearby cycles on `X` and `X ×_S X`, `Δ` the diagonal, `K` a complex on the
generic fibre and `K' = S_X K`. With the external product comparison
`Π : K' ⊠ S_X D K ⟶ S_{X×X}(K ⊠ D K)` and the duality map `δ_K : S_X D K ⟶ D K'` invertible, put
`ρ = (1 ⊠ δ_K) ∘ Π⁻¹ : S_{X×X}(K ⊠ D K) ⟶ K' ⊠ D K'`. The second identity of blueprint
`det-tf-sp-universal-kernel` is

`e_{K'} ∘ ρ = RΔ_{s*} θ_X ∘ χ_Δ ∘ S(e_K)`,

for the evaluation kernels `e_K : K ⊠ D K ⟶ RΔ_* ω_X`. This file proves it for abstract
adjunctions and monoidal closed categories:

* `CategoryTheory.comp_homEquiv_eq_map_homEquiv_comp_exchange`: both sides are the adjoints of
  the same map, given the mate property of `χ_Δ` and the restriction of `ρ` to the diagonal;
* `CategoryTheory.map_comp_ev_eq_of_kunneth`: the restriction of `ρ` to the diagonal is the
  pairing `θ ∘ S(ev) ∘ μ` defining `δ_K`, given that `Δ_s^* Π` is the lax tensor map `μ_X` (the
  composition law and monoidality of the pullback exchanges, with `p_i ∘ Δ = 1`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {CP CX CP' CX' : Type*} [Category CP] [Category CX] [Category CP'] [Category CX']

/-- **The evaluation kernel identity**, abstractly: for adjunctions `U ⊣ R` (`Δ_η^* ⊣ RΔ_{η*}`)
and `U' ⊣ R'`, a transformation `α : S_P ⋙ U' ⟶ U ⋙ S_X` and its mate `χ : R ⋙ S_P ⟶ S_X ⋙ R'`,
if the restriction of `ρ : S_P P ⟶ P'` along `U'` composed with `ev'` is `α ≫ S_X(ev) ≫ θ`, then
`ρ` followed by the adjoint of `ev'` is `S_P` of the adjoint of `ev` followed by `χ` and
`R'(θ)`. -/
theorem comp_homEquiv_eq_map_homEquiv_comp_exchange {U : CP ⥤ CX} {R : CX ⥤ CP} (a : U ⊣ R)
    {U' : CP' ⥤ CX'} {R' : CX' ⥤ CP'} (a' : U' ⊣ R') {SP : CP ⥤ CP'} {SX : CX ⥤ CX'}
    (α : SP ⋙ U' ⟶ U ⋙ SX) (χ : R ⋙ SP ⟶ SX ⋙ R')
    (hχ : ∀ A, U'.map (χ.app A) ≫ a'.counit.app _ = α.app (R.obj A) ≫ SX.map (a.counit.app A))
    {P : CP} {P' : CP'} {ω : CX} {ω' : CX'} (ev : U.obj P ⟶ ω) (ev' : U'.obj P' ⟶ ω')
    (θ : SX.obj ω ⟶ ω') (ρ : SP.obj P ⟶ P')
    (hρ : U'.map ρ ≫ ev' = α.app P ≫ SX.map ev ≫ θ) :
    ρ ≫ a'.homEquiv _ _ ev' = SP.map (a.homEquiv _ _ ev) ≫ χ.app ω ≫ R'.map θ := by
  apply (a'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, hρ,
    Adjunction.homEquiv_counit, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, Adjunction.counit_naturality, ← Category.assoc (U'.map (χ.app ω)),
    hχ]
  have hn := α.naturality (a.homEquiv _ _ ev)
  simp only [Functor.comp_map] at hn
  have he : U.map (a.homEquiv _ _ ev) ≫ a.counit.app ω = ev := by
    simp [Adjunction.homEquiv_unit]
  rw [Category.assoc, reassoc_of% hn, ← SX.map_comp_assoc, he]

variable [MonoidalCategory CX] [MonoidalCategory CX'] [MonoidalClosed CX']

/-- **The restriction of `ρ` to the diagonal**, abstractly: let `Km = Π : Q' ⟶ S_P P` be invertible,
`b : Q' ⟶ P'` (the map `1 ⊠ δ`), and `εP : U P ≅ K ⊗ N`, `εQ : U' Q' ≅ S_X K ⊗ N'`,
`εP' : U' P' ≅ S_X K ⊗ D'` the restrictions of the external products to the diagonal. If
`U'(Π)` is the lax tensor map `μ` along these identifications, `U'(b)` is `S_X K ◁ δ`, and `δ` is
the adjoint of the pairing `θ ∘ S_X(ev) ∘ μ`, then `U'(Π⁻¹ ≫ b)` followed by the evaluation is
`α ≫ S_X(εP ≫ ev) ≫ θ`. -/
theorem map_comp_ev_eq_of_kunneth {U : CP ⥤ CX} {U' : CP' ⥤ CX'} {SP : CP ⥤ CP'}
    {SX : CX ⥤ CX'} (α : SP ⋙ U' ⟶ U ⋙ SX) {P : CP} {Q' P' : CP'} {K N ω : CX} {N' : CX'}
    {ω' : CX'} (εP : U.obj P ≅ K ⊗ N) (εQ : U'.obj Q' ≅ SX.obj K ⊗ N')
    (εP' : U'.obj P' ≅ SX.obj K ⊗ (ihom (SX.obj K)).obj ω')
    (μ : SX.obj K ⊗ N' ⟶ SX.obj (K ⊗ N)) (ev : K ⊗ N ⟶ ω) (θ : SX.obj ω ⟶ ω')
    (δ : N' ⟶ (ihom (SX.obj K)).obj ω')
    (hδ : SX.obj K ◁ δ ≫ (ihom.ev (SX.obj K)).app ω' = μ ≫ SX.map ev ≫ θ)
    (Km : Q' ⟶ SP.obj P) [IsIso Km]
    (hKm : U'.map Km ≫ α.app P ≫ SX.map εP.hom = εQ.hom ≫ μ)
    (b : Q' ⟶ P') (hb : U'.map b ≫ εP'.hom = εQ.hom ≫ SX.obj K ◁ δ) :
    U'.map (inv Km ≫ b) ≫ εP'.hom ≫ (ihom.ev (SX.obj K)).app ω' =
      α.app P ≫ SX.map (εP.hom ≫ ev) ≫ θ := by
  rw [Functor.map_comp, Category.assoc, reassoc_of% hb, hδ]
  have h : U'.map (inv Km) ≫ εQ.hom ≫ μ = α.app P ≫ SX.map εP.hom := by
    rw [← hKm, ← U'.map_comp_assoc, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [reassoc_of% h, SX.map_comp, Category.assoc]

end CategoryTheory

open Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (x : RationalPoint X)

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k).Prime] in
/-- The deformation to the normal cone of `x` is a trait model over the base. -/
lemma isTraitModelOfBase_deformationModel :
    (deformationModel X x.left.ker k').IsTraitModelOfBase k
      (deformationTotalToTrait X x.left.ker k') (deformationGenericToPoint X x.left.ker k') :=
  .of_isPullback ⟨inferInstance, inferInstance, inferInstance, IsPullback.of_hasPullback _ _,
      isPullback_deformationSpecialFibre X _ k'⟩ ⟨deformationTotalToBase X _ k', rfl,
        deformationTotalToBase_hom X _ k'⟩
    (isPullback_deformationModel_ε k' x.left.ker)

variable (D : NearbyCyclesModel.NearbyDualizingData k k' ℓ)

/-- The duality map `δ_K : Sp_{X,x}(D K) ⟶ D Sp_{X,x}(K)` of the specialization (blueprint
`sk-prop-tf-nearby-duality-foundation`), for a family of dualizing maps `D`. -/
noncomputable def specializationDualityMap (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (specialization k' x).obj (verdierDual ℓ K) ⟶ verdierDual ℓ ((specialization k' x).obj K) :=
  NearbyCyclesModel.nearbyDualityMap ℓ D (isTraitModelOfBase_deformationModel k' x) K

/-- The comparison `ρ = (1 ⊠ δ_K) ∘ Π⁻¹ : Ψ_{X×X}(K ⊠ D K) ⟶ Ψ_X K ⊠ D Ψ_X K` of the universal
kernels (blueprint `det-tf-sp-universal-kernel`). -/
noncomputable def universalKernelSpecialization
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (specializationProd k' x).obj (externalProduct ℓ K (verdierDual ℓ K)) ⟶
      externalProduct ℓ ((specialization k' x).obj K)
        (verdierDual ℓ ((specialization k' x).obj K)) :=
  inv (specializationKunnethMap k' x K (verdierDual ℓ K)) ≫
    _ ◁ (boundedConstructibleUpperStar _ ℓ _).map (specializationDualityMap k' x D K)

/-- The restriction of the Künneth map `Π_{K,L}` to the diagonal is the lax tensor map `μ_X` of
the specialization, through the pullback exchange `α_Δ` and the identifications
`LΔ^*(M ⊠ N) ≅ M ⊗ N` (the composition law and monoidality of the pullback exchanges, with
`p_i ∘ Δ = 1`). -/
lemma map_specializationKunnethMap_comp_pullbackExchange
    (K L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ (diag (deformationSpecialFibre X x.left.ker k'))).map
        (specializationKunnethMap k' x K L) ≫
      ((deformationDiagModelHom X x.left.ker k').boundedConstructiblePullbackExchange ℓ
        ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
          (isTraitModel_deformationModel X x.left.ker k')
          (deformationModel_exists_comp_ε X x.left.ker k'))
        (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
          (deformationProdModel X x.left.ker X x.left.ker k')
          (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
          (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k'))).app
        (externalProduct ℓ K L) ≫
      (specialization k' x).map (diagUpperStarExternalProductIso ℓ K L).hom =
    (diagUpperStarExternalProductIso ℓ _ _).hom ≫
      NearbyCyclesModel.boundedConstructibleTensorMap
        ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
          (isTraitModel_deformationModel X x.left.ker k')
          (deformationModel_exists_comp_ε X x.left.ker k')) K L := by
  sorry

set_option maxHeartbeats 1000000 in
-- matching the abstract statements against the concrete functors
/-- **Nearby cycles of the universal kernel**, second identity (blueprint
`det-tf-sp-universal-kernel`): for `ρ = (1 ⊠ δ_K) ∘ Π⁻¹`, the evaluation kernels satisfy
`e_{K'} ∘ ρ = RΔ_{s*} θ_X ∘ χ_Δ ∘ S(e_K)`, with `K' = Sp_{X,x}(K)`. -/
theorem universalKernelSpecialization_comp_evaluationKernel
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    universalKernelSpecialization k' x D K ≫ evaluationKernel ℓ ((specialization k' x).obj K) =
      (specializationProd k' x).map (evaluationKernel ℓ K) ≫
        (Correspondence.IsContractingAt.diagPushforwardExchange ℓ X k' x).app
          (dualizingComplex' ℓ X) ≫
        (boundedConstructibleLowerStar ℓ (diag (deformationSpecialFibre X x.left.ker k'))).map
          (D.θ (isTraitModelOfBase_deformationModel k' x)) := by
  have hρ := CategoryTheory.map_comp_ev_eq_of_kunneth
    ((deformationDiagModelHom X x.left.ker k').boundedConstructiblePullbackExchange ℓ
      ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
        (isTraitModel_deformationModel X x.left.ker k')
        (deformationModel_exists_comp_ε X x.left.ker k'))
      (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
        (deformationProdModel X x.left.ker X x.left.ker k')
        (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
        (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k')))
    (diagUpperStarExternalProductIso ℓ K (verdierDual ℓ K))
    (diagUpperStarExternalProductIso ℓ ((specialization k' x).obj K)
      ((specialization k' x).obj (verdierDual ℓ K)))
    (diagUpperStarExternalProductIso ℓ ((specialization k' x).obj K)
      (verdierDual ℓ ((specialization k' x).obj K)))
    (NearbyCyclesModel.boundedConstructibleTensorMap
        ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
          (isTraitModel_deformationModel X x.left.ker k')
          (deformationModel_exists_comp_ε X x.left.ker k')) K (verdierDual ℓ K))
    ((ihom.ev K).app (dualizingComplex' ℓ X)) (D.θ (isTraitModelOfBase_deformationModel k' x))
    (specializationDualityMap k' x D K)
    (Verdier.whiskerLeft_nearbyDualityMap_comp_ev _ _ K)
    (specializationKunnethMap k' x K (verdierDual ℓ K))
    (map_specializationKunnethMap_comp_pullbackExchange k' x K (verdierDual ℓ K))
    (_ ◁ (boundedConstructibleUpperStar _ ℓ _).map (specializationDualityMap k' x D K))
    (diagUpperStarExternalProductIso_hom_naturality_right ℓ _ (specializationDualityMap k' x D K))
  have hχ :=
    NearbyCyclesModel.Hom.map_boundedConstructiblePushforwardExchange_app_comp_counit_app (ℓ := ℓ)
    (deformationDiagModelHom X x.left.ker k')
    ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel X x.left.ker k')
      (deformationModel_exists_comp_ε X x.left.ker k'))
    (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
      (deformationProdModel X x.left.ker X x.left.ker k')
      (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
      (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k'))
  unfold universalKernelSpecialization evaluationKernel
  apply_by_match CategoryTheory.comp_homEquiv_eq_map_homEquiv_comp_exchange [hχ := hχ, hρ := hρ]

end AlgebraicGeometry.ProEtale.CondensedRing
