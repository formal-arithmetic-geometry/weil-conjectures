/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.CategoryTheory.Adjunction.ScalarClosedProjectionData
import all WeilConjectures.CategoryTheory.ModuleObjects.KFlatScalarTower.InternalKFlatScalarTowerRealizationSupplement
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
import all WeilConjectures.CategoryTheory.Adjunction.ScalarUnitProjectionComplexes
import WeilConjectures.CategoryTheory.ModuleObjects.ScalarUnitProjectionOrdinary
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-! # The canonical projection for native principal scalar extension -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory.Adjunction

private theorem projection_localization_square
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D]
    {F₀ : A ⥤ B} {U₀ : B ⥤ A} [F₀.OplaxMonoidal]
    {F : C ⥤ D} {U : D ⥤ C} [F.Monoidal]
    (adj₀ : F₀ ⊣ U₀) (adj : F ⊣ U)
    (q : A ⥤ C) (r : B ⥤ D) [q.LaxMonoidal] [r.LaxMonoidal]
    (c : q ⋙ F ⟶ F₀ ⋙ r) (h : r ⋙ U ≅ U₀ ⋙ q)
    (hη : ∀ X, adj.unit.app (q.obj X) ≫ U.map (c.app X) ≫
      h.hom.app (F₀.obj X) = q.map (adj₀.unit.app X))
    (hδ : ∀ X Y, Functor.OplaxMonoidal.δ F (q.obj X) (q.obj Y) ≫
      (c.app X ⊗ₘ c.app Y) ≫ Functor.LaxMonoidal.μ r (F₀.obj X) (F₀.obj Y) =
        F.map (Functor.LaxMonoidal.μ q X Y) ≫ c.app (X ⊗ Y) ≫
          r.map (Functor.OplaxMonoidal.δ F₀ X Y))
    [IsIso (Functor.LaxMonoidal.ε r)] (P : A) :
    q.obj P ◁ (h.inv.app (𝟙_ B) ≫ U.map (inv (Functor.LaxMonoidal.ε r))) ≫
        scalarUnitProjection adj (q.obj P) ≫ U.map (c.app P) ≫
          h.hom.app (F₀.obj P) =
      Functor.LaxMonoidal.μ q P (U₀.obj (𝟙_ B)) ≫
        q.map (scalarUnitProjection adj₀ P) := by
  have ht (X : A) (Y : B) (f : F₀.obj X ⟶ Y) :
      adj.homEquiv _ _ (c.app X ≫ r.map f) ≫ h.hom.app Y =
        q.map (adj₀.homEquiv _ _ f) := by
    rw [homEquiv_unit, U.map_comp]
    simp only [Category.assoc]
    have hn := h.hom.naturality f
    change U.map (r.map f) ≫ h.hom.app Y =
      h.hom.app (F₀.obj X) ≫ q.map (U₀.map f) at hn
    rw [hn, reassoc_of% hη X, ← q.map_comp, homEquiv_unit]
  have he : F.map (h.inv.app (𝟙_ B)) ≫ adj.counit.app (r.obj (𝟙_ B)) =
      c.app (U₀.obj (𝟙_ B)) ≫ r.map (adj₀.counit.app (𝟙_ B)) := by
    have hh := ht (U₀.obj (𝟙_ B)) (𝟙_ B) (adj₀.counit.app (𝟙_ B))
    have hzero : adj₀.homEquiv (U₀.obj (𝟙_ B)) (𝟙_ B)
        (adj₀.counit.app (𝟙_ B)) = 𝟙 _ := by
      rw [← adj₀.homEquiv_symm_id]
      exact (adj₀.homEquiv _ _).apply_symm_apply _
    rw [hzero, q.map_id] at hh
    have hh' : adj.homEquiv (q.obj (U₀.obj (𝟙_ B))) (r.obj (𝟙_ B))
        (c.app (U₀.obj (𝟙_ B)) ≫ r.map (adj₀.counit.app (𝟙_ B))) =
          h.inv.app (𝟙_ B) := by
      rw [← cancel_mono (h.hom.app (𝟙_ B)), hh, Iso.inv_hom_id_app]
      rfl
    simpa only [homEquiv_counit, Equiv.symm_apply_apply,
      Functor.id_obj, Functor.comp_obj] using
      (congrArg (adj.homEquiv _ _).symm hh').symm
  have htp := ht (P ⊗ U₀.obj (𝟙_ B)) (F₀.obj P)
    (Functor.OplaxMonoidal.δ F₀ P (U₀.obj (𝟙_ B)) ≫
      F₀.obj P ◁ adj₀.counit.app (𝟙_ B) ≫ (ρ_ (F₀.obj P)).hom)
  change _ = q.map (scalarUnitProjection adj₀ P) at htp
  apply (cancel_mono (h.inv.app (F₀.obj P))).1
  dsimp only [Functor.comp_obj]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  simp only [Category.comp_id]
  rw [← htp]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  simp only [Category.comp_id]
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_naturality_left_symm, homEquiv_naturality_right_symm]
  rw [scalarUnitProjection]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [Equiv.symm_apply_apply]
  rw [homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  simp only [Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc]
  simp only [F.map_comp, whiskerLeft_comp, Category.assoc]
  rw [← whiskerLeft_comp_assoc (F.obj (q.obj P))
    (F.map (U.map (inv (Functor.LaxMonoidal.ε r)))) (adj.counit.app (𝟙_ D))]
  erw [adj.counit_naturality]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← whiskerLeft_comp_assoc (F.obj (q.obj P)) (F.map (h.inv.app (𝟙_ B)))
    (adj.counit.app (r.obj (𝟙_ B))), he]
  simp only [whiskerLeft_comp, Category.assoc]
  erw [← rightUnitor_naturality]
  erw [whisker_exchange_assoc, whisker_exchange_assoc, whisker_exchange_assoc]
  have hu : r.obj (F₀.obj P) ◁ inv (Functor.LaxMonoidal.ε r) ≫
      (ρ_ (r.obj (F₀.obj P))).hom =
        Functor.LaxMonoidal.μ r (F₀.obj P) (𝟙_ B) ≫
          r.map (ρ_ (F₀.obj P)).hom := by
    apply (cancel_epi (r.obj (F₀.obj P) ◁ Functor.LaxMonoidal.ε r)).1
    simp only [← whiskerLeft_comp_assoc, IsIso.hom_inv_id,
      whiskerLeft_id, Category.id_comp]
    exact Functor.LaxMonoidal.right_unitality r (F₀.obj P)
  rw [hu]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  erw [Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [← tensorHom_def_assoc, reassoc_of% hδ P (U₀.obj (𝟙_ B))]
  simp only [r.map_comp]

end CategoryTheory.Adjunction

namespace CategoryTheory.Mod

set_option maxHeartbeats 400000 in
-- Check the localization square and its K-flat tensor comparison instances.
private theorem projection_generic
    {C : Type*} [Category.{u + 1} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] (K : DerivedCategory (Mod C R)) :
    letI := Mod.extendScalarsMonoidal φ
    letI := (Mod.extendScalars φ).leftDerivedFunctorMonoidal
    IsIso (Adjunction.scalarUnitProjection
      (Mod.derivedExtendMapDerivedCategoryAdjunction φ) K) := by
  let A := Mod C R
  let B := Mod C S
  let F : A ⥤ B := Mod.extendScalars φ
  let U₀ : B ⥤ A := Mod.comap φ
  let := Mod.extendScalarsMonoidal φ
  let := F.leftDerivedFunctorMonoidal
  let adj : F.leftDerivedFunctor ⊣ U₀.mapDerivedCategory :=
    Mod.derivedExtendMapDerivedCategoryAdjunction φ
  change IsIso (Adjunction.scalarUnitProjection adj K)
  obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_kFlat_iso K
  have hp : IsIso (Adjunction.scalarUnitProjection adj (DerivedCategory.Qh.obj P)) := by
    let a₀ : F ⊣ U₀ := Mod.extendRestrictAdjunction φ
    let ah := a₀.mapHomotopyCategory (.up ℤ)
    have ho (M : A) :
        IsIso (Adjunction.scalarUnitProjection a₀ M) :=
      Mod.scalarUnitProjection_isIso φ M
    have hhp : IsIso (Adjunction.scalarUnitProjection ah P) :=
      Adjunction.scalarUnitProjection_homotopy_isIso a₀ ho P
    have hc : IsIso (F.leftDerivedFunctorCounit.app P) :=
      F.isIso_leftDerivedFunctorCounit_app_of_kFlat' P hP
    have hμ : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh P
        ((U₀.mapHomotopyCategory (.up ℤ)).obj (𝟙_ (HomotopyCategory B (.up ℤ))))) :=
      DerivedMonoidal.isIso_counit_app_app_of_kFlat_left DerivedCategory.Qh
        (HomotopyCategory.quasiIso _ (.up ℤ)) P _ hP
    have := DerivedCategory.isIso_ε_Qh B
    have hs := Adjunction.projection_localization_square ah adj
      DerivedCategory.Qh DerivedCategory.Qh F.leftDerivedFunctorCounit
      U₀.mapDerivedCategoryFactorsh (Mod.KFlatScalarTower.derivedUnit_homotopy φ)
      (fun A B ↦ F.leftDerivedTensorComparison_app_app_comp_tensorHom A B) P
    have ht : IsIso
        (DerivedCategory.Qh.obj P ◁
          (U₀.mapDerivedCategoryFactorsh.inv.app (𝟙_ (HomotopyCategory B (.up ℤ))) ≫
            U₀.mapDerivedCategory.map (inv (Functor.LaxMonoidal.ε DerivedCategory.Qh))) ≫
          Adjunction.scalarUnitProjection adj (DerivedCategory.Qh.obj P) ≫
          U₀.mapDerivedCategory.map (F.leftDerivedFunctorCounit.app P) ≫
          U₀.mapDerivedCategoryFactorsh.hom.app
            ((F.mapHomotopyCategory (.up ℤ)).obj P)) := by
      rw [hs]
      infer_instance
    have ht' := (isIso_comp_left_iff _ _).mp ht
    exact (isIso_comp_right_iff _
      (U₀.mapDerivedCategory.map (F.leftDerivedFunctorCounit.app P) ≫
        U₀.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (.up ℤ)).obj P))).mp ht'
  have hn := (Adjunction.projectionNat adj).naturality e.hom
  dsimp only [Adjunction.projectionNat] at hn
  have ht : IsIso ((tensorRight _).map e.hom ≫
      Adjunction.scalarUnitProjection adj K) := by
    rw [hn]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp ht

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.CoefficientHomComparison

private theorem normalized_scalar_monoidal_eq (X : Scheme.{u})
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] :
    CondensedRing.internalScalarMonoidal a X =
      Mod.extendScalarsMonoidal (coefficientMap a X) := by
  apply CondensedRing.normalized_unique a X
  · exact (CondensedRing.internalScalarMonoidalNormalized_existsUnique a X).exists.choose_spec
  · intro M N
    let φ := coefficientMap a X
    let := Mod.extendScalarsMonoidal φ
    change Mod.tensorObjπ M N ≫ Mod.extendUnitHom φ (M ⊗ N) ≫
      (Functor.OplaxMonoidal.δ (Mod.extendScalars φ) M N).hom = _
    rw [Mod.extendScalarsOplaxMonoidal_δ]
    rw [Mod.extendUnitHom_extendHom]
    rw [tensorHom_def (Mod.extendUnit φ M) (Mod.extendUnit φ N)]
    simp only [Mod.comp_hom', Category.assoc]
    erw [Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft_assoc,
      Mod.tensorObjπ_comapTensorHom_hom]
    rfl

private theorem normalized_derived_scalar_monoidal_eq (X : Scheme.{u})
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] :
    scalarMonoidal X a = (letI := Mod.extendScalarsMonoidal (coefficientMap a X)
      (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorMonoidal) := by
  unfold scalarMonoidal
  rw [normalized_scalar_monoidal_eq]


set_option maxHeartbeats 1600000 in
-- Compare the normalized derived tensor structures on K-flat representatives.
/-- The canonical projection against the restricted finite scalar unit is invertible.
Source: the balanced scalar tensor computation, Stacks 07A4 and 06YY.
Proof: represent K by a K-flat complex P. Extension sends P to a K-flat complex
over the quotient. Exact restriction commutes with localization. The balanced
projection for ordinary modules identifies P tensor the restricted quotient
with the restriction of its extension; its inverse sends the balanced scalar
generator to the same tensor generator. The scalar derived-adjunction unit
normalization and the derived tensorator counit equation identify this
balanced comparison with the displayed adjunction transpose, including its
right unitor. The comparison is invertible on P. Naturality transports the
result along the chosen quasi-isomorphism to K. No flatness of the quotient
is used: P is K-flat in the first tensor factor.
(blueprint: lem-per-principal-scalar-unit-projection). -/
theorem principal_scalar_unit_projection (X : Scheme.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ)
    (K : D X (integral.{u} ℓ E)) :
    letI := scalarMonoidal X (reductionMap ℓ E n)
    IsIso (Adjunction.scalarUnitProjection
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (reductionMap ℓ E n) X)) K) := by
  simpa +instances only [normalized_derived_scalar_monoidal_eq] using
    (Mod.projection_generic (coefficientMap (reductionMap ℓ E n) X) K)

end AlgebraicGeometry.ProEtale.CoefficientHomComparison
