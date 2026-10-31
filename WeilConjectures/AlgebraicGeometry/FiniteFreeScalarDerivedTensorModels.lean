/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeScalarCalculusData
import Mathlib.Tactic.Convert
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo

/-! # Normalized finite-free scalar constructions

Source: Stacks Project, Tags 03CZ, 05V4, 06YU and 05RT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

section ScalarDerivedModels

universe a v
variable {CA : Type a} {CB : Type a} [Category.{v} CA] [Category.{v} CB]
  [Abelian CA] [Abelian CB]
  [IsGrothendieckAbelian.{v} CA] [IsGrothendieckAbelian.{v} CB]
  [HasDerivedCategory.{v} CA] [HasDerivedCategory.{v} CB]
  [MonoidalCategory CA] [MonoidalCategory CB]
  [MonoidalPreadditive CA] [MonoidalPreadditive CB]
  [MonoidalClosed CA] [MonoidalClosed CB] [BraidedCategory CA] [BraidedCategory CB]
  [Abelian.HasFunctorialFlatResolution CA] [Abelian.HasFunctorialFlatResolution CB]
  [HasColimitsOfSize.{0, 0} CA] [HasColimitsOfSize.{0, 0} CB]
  (E : CA ⥤ CB) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  (U : CB ⥤ CA) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [∀ I : Type, PreservesColimitsOfShape (Discrete I) U]
  (β : E ⋙ curriedTensor CB ⋙ (Functor.whiskeringRight _ _ _).obj U ≅
    curriedTensor CA ⋙ (Functor.whiskeringLeft _ _ _).obj U)

private instance scalarTensor_preservesZero (M : CA) :
    ((E ⋙ curriedTensor CB).obj M).PreservesZeroMorphisms :=
  inferInstanceAs (((curriedTensor CB).obj (E.obj M)).PreservesZeroMorphisms)

private def scalarChainIso (P : CochainComplex CA ℤ) (Q : CochainComplex CB ℤ) :
    (U.mapHomologicalComplex (.up ℤ)).obj
      ((E.mapHomologicalComplex (.up ℤ)).obj P ⊗ Q) ≅
      P ⊗ (U.mapHomologicalComplex (.up ℤ)).obj Q := by
  exact asIso (HomologicalComplex.mapBifunctorComparison
    (F := E ⋙ curriedTensor CB) (F' := curriedTensor CA)
    (G₁ := 𝟭 CA) (G₂ := U) (G := U) β.hom (.up ℤ) P Q)

omit [HasDerivedCategory CA] [HasDerivedCategory CB]
  [Abelian.HasFunctorialFlatResolution CA] [Abelian.HasFunctorialFlatResolution CB]
  [HasColimitsOfSize.{0, 0} CA] [HasColimitsOfSize.{0, 0} CB]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U] in
private theorem scalarChain_natural {P P' : CochainComplex CA ℤ}
    {Q Q' : CochainComplex CB ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    (U.mapHomologicalComplex (.up ℤ)).map
        ((E.mapHomologicalComplex (.up ℤ)).map f ⊗ₘ g) ≫
        (scalarChainIso E U β P' Q').hom =
      (scalarChainIso E U β P Q).hom ≫
        (f ⊗ₘ (U.mapHomologicalComplex (.up ℤ)).map g) := by
  exact HomologicalComplex.mapBifunctorComparison_naturality
    (F := E ⋙ curriedTensor CB) (F' := curriedTensor CA)
    (G₁ := 𝟭 CA) (G₂ := U) (G := U) β.hom (.up ℤ) f g

private def scalarChainNatIso :
    E.mapHomologicalComplex (.up ℤ) ⋙ curriedTensor (CochainComplex CB ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj (U.mapHomologicalComplex (.up ℤ)) ≅
    curriedTensor (CochainComplex CA ℤ) ⋙
      (Functor.whiskeringLeft _ _ _).obj (U.mapHomologicalComplex (.up ℤ)) :=
  NatIso.ofComponents
    (fun P ↦ NatIso.ofComponents (fun Q ↦ scalarChainIso E U β P Q) (by
      intro Q Q' g
      simpa using scalarChain_natural E U β (𝟙 P) g)) (by
    intro P P' f
    ext Q : 2
    simpa using scalarChain_natural E U β f (𝟙 Q))

/-- The canonical localization tensorator is invertible if its first factor is K-flat. -/
private theorem scalarTensorator_isIso (P Q : CochainComplex CA ℤ)
    (hP : (HomologicalComplex.quasiIso CA (.up ℤ)).kFlat P) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) := by
  have := DerivedMonoidal.isIso_counit_app_app_of_kFlat_left
    DerivedCategory.Qh (HomotopyCategory.quasiIso CA (.up ℤ))
    ((HomotopyCategory.quotient _ _).obj P)
    ((HomotopyCategory.quotient _ _).obj Q)
    ((HomotopyCategory.kFlat_quotient_obj_iff P).2 hP)
  change IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
    ((HomotopyCategory.quotient _ _).obj P)
    ((HomotopyCategory.quotient _ _).obj Q)) at this
  change IsIso ((_ ⊗ₘ _) ≫
    (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ _) ≫ _)
  infer_instance

private theorem scalarDerivedModels
    (hE : ∀ P : CochainComplex CA ℤ,
      (HomologicalComplex.quasiIso CA (.up ℤ)).kFlat P →
      (HomologicalComplex.quasiIso CB (.up ℤ)).kFlat
        ((E.mapHomologicalComplex (.up ℤ)).obj P)) :
    Nonempty (FiniteScalarDerivedTensorModels E U (fun M N ↦ (β.app M).app N)) := by
  let Ec := E.mapHomologicalComplex (.up ℤ)
  let Uc := U.mapHomologicalComplex (.up ℤ)
  let ED := E.mapDerivedCategory
  let UD := U.mapDerivedCategory
  let T := ED ⋙ curriedTensor (DerivedCategory CB) ⋙
    (Functor.whiskeringRight _ _ _).obj UD
  let V := curriedTensor (DerivedCategory CA) ⋙
    (Functor.whiskeringLeft _ _ _).obj UD
  let F := Ec ⋙ curriedTensor (CochainComplex CB ℤ)
  let G := curriedTensor (CochainComplex CA ℤ) ⋙
    (Functor.whiskeringLeft _ _ _).obj Uc
  let a : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj
      DerivedCategory.Q).obj T ⟶
      (Functor.postcompose₂.obj (Uc ⋙ DerivedCategory.Q)).obj F :=
    (Functor.postcompose₂.obj UD).map
      ((((Functor.whiskeringLeft₂ _).map E.mapDerivedCategoryFactors.hom).app
        DerivedCategory.Q).app (curriedTensor _) ≫
          (((Functor.whiskeringLeft₂ _).obj Ec).obj (𝟭 _)).map
            (Functor.LaxMonoidal.μNatTrans DerivedCategory.Q)) ≫
      (Functor.postcompose₂.map U.mapDerivedCategoryFactors.hom).app F
  let b : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).obj
      DerivedCategory.Q).obj V ⟶ (Functor.postcompose₂.obj DerivedCategory.Q).obj G :=
    (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q).map
      U.mapDerivedCategoryFactors.hom).app (curriedTensor _) ≫
        (((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj Uc).map
          (Functor.LaxMonoidal.μNatTrans DerivedCategory.Q)
  have ha (P : CochainComplex CA ℤ) (Q : CochainComplex CB ℤ) :
      (a.app P).app Q = UD.map
        ((E.mapDerivedCategoryFactors.hom.app P ▷ DerivedCategory.Q.obj Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q (Ec.obj P) Q) ≫
        U.mapDerivedCategoryFactors.hom.app (Ec.obj P ⊗ Q) := rfl
  have hb (P : CochainComplex CA ℤ) (Q : CochainComplex CB ℤ) :
      (b.app P).app Q =
        (DerivedCategory.Q.obj P ◁ U.mapDerivedCategoryFactors.hom.app Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q P (Uc.obj Q) := rfl
  -- Resolve only the first variable; the second complex can be arbitrary.
  have : T.IsLeftDerivedFunctor₂ a
      (HomologicalComplex.quasiIso CA (.up ℤ))
      (HomologicalComplex.quasiIso CB (.up ℤ)) := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      (HomologicalComplex.quasiIso CA (.up ℤ)).localizerMorphismKFlat
      (LocalizerMorphism.id (HomologicalComplex.quasiIso CB (.up ℤ)))
    intro P Q
    let := scalarTensorator_isIso (Ec.obj P.obj) Q (hE P.obj P.property)
    rw [ha]
    change IsIso (UD.map ((E.mapDerivedCategoryFactors.hom.app P.obj ▷
      DerivedCategory.Q.obj Q) ≫ Functor.LaxMonoidal.μ DerivedCategory.Q
        (Ec.obj P.obj) Q) ≫ U.mapDerivedCategoryFactors.hom.app (Ec.obj P.obj ⊗ Q))
    rw [Functor.map_comp]
    infer_instance
  have : V.IsLeftDerivedFunctor₂ b
      (HomologicalComplex.quasiIso CA (.up ℤ))
      (HomologicalComplex.quasiIso CB (.up ℤ)) := by
    apply LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
      (HomologicalComplex.quasiIso CA (.up ℤ)).localizerMorphismKFlat
      (LocalizerMorphism.id (HomologicalComplex.quasiIso CB (.up ℤ)))
    intro P Q
    let := scalarTensorator_isIso P.obj (Uc.obj Q) P.property
    rw [hb]
    change IsIso ((DerivedCategory.Q.obj P.obj ◁
      U.mapDerivedCategoryFactors.hom.app Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q P.obj (Uc.obj Q))
    infer_instance
  let c := scalarChainNatIso E U β
  let cQ : (Functor.postcompose₂.obj (Uc ⋙ DerivedCategory.Q)).obj F ≅
      (Functor.postcompose₂.obj DerivedCategory.Q).obj G :=
    (Functor.postcompose₂.obj DerivedCategory.Q).mapIso c
  -- The derived comparison is fixed by its canonical counit equation.
  let δ := Functor.leftDerived₂NatIso V b
    (HomologicalComplex.quasiIso CA (.up ℤ))
    (HomologicalComplex.quasiIso CB (.up ℤ)) T a cQ
  refine ⟨{
    tensor_iso := fun K N ↦ (δ.app K).app N
    tensor_natural := ?_
    tensor_normalized := ?_ }⟩
  · intro K K' N N' f g
    have h₁ := congr_app (δ.hom.naturality f) N
    have h₂ := (δ.hom.app K').naturality g
    change UD.map (ED.map f ▷ N) ≫ (δ.hom.app K').app N =
      (δ.hom.app K).app N ≫ (f ▷ UD.obj N) at h₁
    change UD.map (ED.obj K' ◁ g) ≫ (δ.hom.app K').app N' =
      (δ.hom.app K').app N ≫ (K' ◁ UD.map g) at h₂
    simp only [Iso.app_hom]
    dsimp only [ED, UD] at h₁ h₂
    rw [MonoidalCategory.tensorHom_def, Functor.map_comp, Category.assoc, h₂]
    rw [← Category.assoc, h₁, Category.assoc, ← MonoidalCategory.tensorHom_def]
  · intro P Q hP hQ
    refine ⟨scalarChainIso E U β P Q, ?_, ?_⟩
    · intro i j n h
      exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
        (F := E ⋙ curriedTensor CB) (F' := curriedTensor CA)
        (G₁ := 𝟭 CA) (G₂ := U) (G := U) β.hom (.up ℤ) P Q i j n h
    · have h := Functor.leftDerived₂NatTrans_app_app V b
        (HomologicalComplex.quasiIso CA (.up ℤ))
        (HomologicalComplex.quasiIso CB (.up ℤ)) T a cQ.hom P Q
      have hc : (cQ.hom.app P).app Q =
          DerivedCategory.Q.map (scalarChainIso E U β P Q).hom := rfl
      rw [ha, hb, hc] at h
      dsimp [T, V, F, G, Ec, Uc, ED, UD] at h
      simp only [Category.assoc] at h
      simp only [δ, T, V, ED, UD, Functor.comp_obj,
        Functor.leftDerived₂NatIso_hom, Iso.app_hom]
      convert h.symm using 1 <;> rfl

end ScalarDerivedModels

end CategoryTheory

namespace AlgebraicGeometry

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
  [Algebra A B] (r : ℕ) (basis : Module.Basis (Fin r) A B)

private theorem tensorPure_map (R : Type (u + 1)) [CommRing R]
    {M M' N N' : Sheaf J (ModuleCat.{u + 1} R)}
    (f : M ⟶ M') (g : N ⟶ N') (V : Cᵒᵖ)
    (m : M.obj.obj V) (n : N.obj.obj V) :
    (f ⊗ₘ g).hom.app V (finiteScalarTensorPure J R M N V m n) =
      finiteScalarTensorPure J R M' N' V (f.hom.app V m) (g.hom.app V n) := by
  have h := congr_app
    (Functor.LaxMonoidal.μ_natural (sheafToPresheaf J (ModuleCat.{u + 1} R)) f g) V
  exact (congrArg (fun k ↦ k (m ⊗ₜ[R] n)) h).symm

private theorem tensorPure_ext (R : Type (u + 1)) [CommRing R]
    (M N T : Sheaf J (ModuleCat.{u + 1} R)) {f g : M ⊗ N ⟶ T}
    (h : ∀ V m n, f.hom.app V (finiteScalarTensorPure J R M N V m n) =
      g.hom.app V (finiteScalarTensorPure J R M N V m n)) : f = g := by
  let adj := sheafificationAdjunction J (ModuleCat.{u + 1} R)
  let μ := Functor.LaxMonoidal.μ (sheafToPresheaf J (ModuleCat.{u + 1} R)) M N
  have he : (adj.homEquiv _ _).symm μ =
      Functor.OplaxMonoidal.δ (presheafToSheaf J (ModuleCat.{u + 1} R)) M.obj N.obj ≫
        (adj.counit.app M ⊗ₘ adj.counit.app N) := by
    exact (adj.homEquiv _ _).symm_apply_apply _
  have : IsIso ((adj.homEquiv _ _).symm μ) := by rw [he]; infer_instance
  apply (cancel_epi ((adj.homEquiv _ _).symm μ)).mp
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  apply ModuleCat.MonoidalCategory.tensor_ext
  exact h V

omit [EssentiallySmall.{u + 1} C] in
private theorem scalarPure_map {M M' : Sheaf J (ModuleCat.{u + 1} A)}
    (f : M ⟶ M') (V : Cᵒᵖ) (b : B) (m : M.obj.obj V) :
    ((finiteScalarExtension J (algebraMap A B)).map f).hom.app V
        (finiteScalarPure J (algebraMap A B) M V b m) =
      finiteScalarPure J (algebraMap A B) M' V b (f.hom.app V m) := by
  have h := congr_app ((sheafificationAdjunction J (ModuleCat.{u + 1} B)).unit.naturality
    (Functor.whiskerRight f.hom (ModuleCat.extendScalars (algebraMap A B)))) V
  exact (congrArg (fun k ↦ k (b ⊗ₜ[A] m)) h).symm

private theorem balance_natural (s : FiniteFreeScalarTensorCalculus J r basis)
    {M M' : Sheaf J (ModuleCat.{u + 1} A)}
    {N N' : Sheaf J (ModuleCat.{u + 1} B)} (f : M ⟶ M') (g : N ⟶ N') :
    (Sheaf.restrictScalars J (algebraMap A B)).map
        ((finiteScalarExtension J (algebraMap A B)).map f ⊗ₘ g) ≫
        (s.sheaf_balance M' N').hom =
      (s.sheaf_balance M N).hom ≫
        (f ⊗ₘ (Sheaf.restrictScalars J (algebraMap A B)).map g) := by
  apply (cancel_epi (s.sheaf_balance M N).inv).mp
  apply (cancel_mono (s.sheaf_balance M' N').inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc]
  symm
  apply tensorPure_ext J A
  intro V m n
  change (s.sheaf_balance M' N').inv.hom.app V
      ((f ⊗ₘ (Sheaf.restrictScalars J (algebraMap A B)).map g).hom.app V
        (finiteScalarTensorPure J A M _ V m n)) =
    ((finiteScalarExtension J (algebraMap A B)).map f ⊗ₘ g).hom.app V
      ((s.sheaf_balance M N).inv.hom.app V (finiteScalarTensorPure J A M _ V m n))
  rw [tensorPure_map, s.balance_inverse, s.balance_inverse, tensorPure_map, scalarPure_map]
  rfl

private def balanceIso (s : FiniteFreeScalarTensorCalculus J r basis) :
    finiteScalarExtension J (algebraMap A B) ⋙ curriedTensor _ ⋙
      (Functor.whiskeringRight _ _ _).obj (Sheaf.restrictScalars J (algebraMap A B)) ≅
    curriedTensor _ ⋙
      (Functor.whiskeringLeft _ _ _).obj (Sheaf.restrictScalars J (algebraMap A B)) :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents (fun N ↦ s.sheaf_balance M N) (by
      intro N N' g
      simpa using balance_natural J r basis s (𝟙 M) g)) (by
    intro M M' f
    ext N : 2
    simpa using balance_natural J r basis s f (𝟙 N))

/-- The normalized ordinary scalar balancing maps descend on K-flat cochain models.
Source: Stacks 06YU and 05V4; step 7 of lem-sf-finite-free-derived-scalar-calculus.
(blueprint: lem-sf-finite-free-scalar-derived-tensor-models).

Proof: let P and Q be K-flat A- and B-complexes. Exact extension and cancellation show
that UQ is K-flat: for acyclic H, its tensor with UQ is the restriction of EH tensor Q,
which is acyclic. Extension preserves K-flatness by the supplied descent. Restriction
preserves the coproducts in each total degree. Apply the sheaf balancing maps on each
homogeneous summand; the normalized formulas commute with both differentials, including
the sign in the second one, since the coefficient b has degree zero. The inverse formulas
give inverse chain maps. Naturality holds on pure tensors and hence after sheafification
and totalization. Descend this natural isomorphism through the two K-flat localization
equivalences. The defining localization equation is the tensor_normalized square with
the canonical mapDerivedCategoryFactors and localization tensorators. Its component
formula on each summand is precisely the first clause of that normalization. The same
localization equation proves independence of representatives and joint naturality. -/
theorem finiteFreeScalarDerivedTensorModels (s : FiniteFreeScalarTensorCalculus J r basis) :
    letI := s.extension_limits
    letI := s.extension_colimits
    letI := s.restriction_limits
    letI := s.restriction_colimits
    Nonempty (FiniteScalarDerivedTensorModels
      (finiteScalarExtension J (algebraMap A B)) (Sheaf.restrictScalars J (algebraMap A B))
      s.sheaf_balance) := by
  let := s.extension_limits
  let := s.extension_colimits
  let := s.restriction_limits
  let := s.restriction_colimits
  exact scalarDerivedModels (finiteScalarExtension J (algebraMap A B))
    (Sheaf.restrictScalars J (algebraMap A B)) (balanceIso J r basis s) s.kflat_extension

end AlgebraicGeometry
