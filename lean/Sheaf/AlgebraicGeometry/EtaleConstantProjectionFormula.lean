/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal

/-!
# Tensoring derived global sections with a constant complex

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-sf-kunneth-ordinary/
lem-kun-0f12.md; Stacks Project, etale-cohomology.tex, Tag 0F12
(blueprint: lem-kun-0f12).
-/

@[expose] public section

universe u uC uD uA

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

section ExactTensorComparison

variable {C : Type uC} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type uD} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

omit [Abelian.HasFunctorialFlatResolution D] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.Monoidal] in
private theorem commonFlat_iso_aux
    (K : DerivedCategory C) :
    ∃ P : HomotopyCategory C (.up ℤ),
      (HomotopyCategory.quasiIso C (.up ℤ)).kFlat P ∧ F.kFlatMap P ∧
        Nonempty (K ≅ DerivedCategory.Qh.obj P) := by
  let resolution := (inferInstance : Abelian.HasFunctorialFlatResolution C).some.reduced
  let K₀ := DerivedCategory.Q.objPreimage K
  refine ⟨(HomotopyCategory.quotient _ _).obj (resolution.resolutionFunctor.obj K₀),
    (HomotopyCategory.kFlat_quotient_obj_iff _).mpr
      (resolution.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K₀),
    F.kFlatMap_quotient_obj_resolutionFunctor_obj resolution K₀, ?_⟩
  exact ⟨(DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    (asIso (DerivedCategory.Q.map (resolution.resolutionNatTrans.app K₀))).symm⟩

private noncomputable def derivedUnitComparison :
    F.leftDerivedFunctor.obj (𝟙_ _) ⟶ 𝟙_ (DerivedCategory D) := by
  have := DerivedCategory.isIso_ε_Qh.{u + 1, u + 1, uD} D
  exact F.leftDerivedFunctor.map (Functor.LaxMonoidal.ε DerivedCategory.Qh) ≫
    F.leftDerivedFunctorCounit.app (𝟙_ _) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map
      F.mapCochainComplexεIso.inv) ≫
    inv (Functor.LaxMonoidal.ε DerivedCategory.Qh)

omit [F.PreservesFlat] [F.IsLeftAdjoint] in
private theorem derivedUnitComparison_isIso : IsIso (derivedUnitComparison F) := by
  have := DerivedCategory.isIso_ε_Qh.{u + 1, u + 1, uC} C
  have := DerivedCategory.isIso_ε_Qh.{u + 1, u + 1, uD} D
  unfold derivedUnitComparison
  infer_instance

private theorem derivedComparison_rightUnit (K : DerivedCategory C) :
    (F.leftDerivedTensorComparison.app K).app (𝟙_ _) ≫
      F.leftDerivedFunctor.obj K ◁ derivedUnitComparison F ≫
        (ρ_ (F.leftDerivedFunctor.obj K)).hom = F.leftDerivedFunctor.map (ρ_ K).hom := by
  generalize hcomp : F.leftDerivedTensorComparison = φ
  have := DerivedCategory.isIso_ε_Qh.{u + 1, u + 1, uD} D
  obtain ⟨P, _, _, ⟨e⟩⟩ := commonFlat_iso_aux F K
  have := Functor.LaxMonoidal.isIso_μ_tensorUnit_right DerivedCategory.Qh
    ((F.mapHomotopyCategory (.up ℤ)).obj P)
  have h : (ρ_ (F.leftDerivedFunctor.obj K)).inv =
      F.leftDerivedFunctor.map (ρ_ K).inv ≫ (φ.app K).app (𝟙_ _) ≫
        F.leftDerivedFunctor.obj K ◁ derivedUnitComparison F := by
    apply Functor.OplaxMonoidal.oplax_right_unitality_of_iso φ e.symm
    have hδ := F.leftDerivedTensorComparison_app_app_comp_tensorHom
    rw [hcomp] at hδ
    have hsource := Functor.OplaxMonoidal.oplax_right_unitality_of_lax_square
      (Q₁ := DerivedCategory.Qh) (Q₂ := DerivedCategory.Qh)
      (F := F.mapHomotopyCategory (.up ℤ)) φ
      (fun P ↦ F.leftDerivedFunctorCounit.app P)
      (fun _ _ f ↦ F.leftDerivedFunctorCounit.naturality f) hδ P
    simpa only [derivedUnitComparison, Functor.mapHomotopyCategory_η F,
      Functor.mapCochainComplex_η F] using hsource
  apply (cancel_epi (F.leftDerivedFunctor.map (ρ_ K).inv)).mp
  rw [← F.leftDerivedFunctor.map_comp, Iso.inv_hom_id, F.leftDerivedFunctor.map_id]
  simpa only [Category.assoc, Iso.inv_hom_id] using
    congrArg (fun f ↦ f ≫ (ρ_ (F.leftDerivedFunctor.obj K)).hom) h.symm

variable [F.leftDerivedFunctor.CommShift ℤ]
  [NatTrans.CommShift
    (F₁ := DerivedCategory.Qh ⋙ F.leftDerivedFunctor)
    (F₂ := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    F.leftDerivedFunctorCounit ℤ]

private theorem exactComparison_commShift_aux
    (K : DerivedCategory C) :
    NatTrans.CommShift
      (F₁ := tensorLeft K ⋙ F.leftDerivedFunctor)
      (F₂ := F.leftDerivedFunctor ⋙ tensorLeft (F.leftDerivedFunctor.obj K))
      (F.leftDerivedTensorComparison.app K) ℤ := by
  generalize hcomp : F.leftDerivedTensorComparison = φ
  obtain ⟨P, hP, hFP, ⟨e⟩⟩ := commonFlat_iso_aux F K
  let τP : tensorLeft (DerivedCategory.Qh.obj P) ⋙ F.leftDerivedFunctor ⟶
      F.leftDerivedFunctor ⋙ tensorLeft (F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P)) :=
    φ.app (DerivedCategory.Qh.obj P)
  have : NatTrans.CommShift τP ℤ := by
    apply DerivedCategory.commShift_of_tensorLeft_fac F F.leftDerivedFunctor
      F.leftDerivedFunctorCounit P hP hFP
    intro M
    have h := F.leftDerivedTensorComparison_app_app_comp_tensorHom P M
    rw [hcomp] at h
    simpa only [τP, Functor.leftDerivedDerivedTensor, Functor.comp_obj,
      DerivedCategory.tensorLeftCounit, Functor.bifunctorCounit₁_app,
      Functor.LaxMonoidal.μNatTrans_app_app,
      MonoidalCategory.tensorHom_def, Category.assoc] using h
  have he : φ.app K =
      Functor.whiskerRight ((curriedTensor _).map e.hom) F.leftDerivedFunctor ≫ τP ≫
        Functor.whiskerLeft F.leftDerivedFunctor
          ((curriedTensor _).map (F.leftDerivedFunctor.map e.inv)) := by
    ext M
    have h := NatTrans.congr_app (φ.naturality e.hom) M
    dsimp [τP] at h ⊢
    rw [← Category.assoc, h, Category.assoc]
    simp [← comp_whiskerRight, ← Functor.map_comp]
  have : NatTrans.CommShift ((curriedTensor (DerivedCategory C)).map e.hom) ℤ :=
    Functor.CommShift₂.commShift_map
      (G := curriedTensor (DerivedCategory C)) (h := .int) e.hom
  have : NatTrans.CommShift
      ((curriedTensor (DerivedCategory D)).map (F.leftDerivedFunctor.map e.inv)) ℤ :=
    Functor.CommShift₂.commShift_map
      (G := curriedTensor (DerivedCategory D)) (h := .int) (F.leftDerivedFunctor.map e.inv)
  rw [he]
  infer_instance

end ExactTensorComparison

section Generation

variable (C : Type uC) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

/-- Closure under shifts of the tensor unit, coproducts, triangles, and retracts. -/
private def UnitGeneration : Prop :=
  ∀ (P : ObjectProperty (DerivedCategory C)),
    (∀ n : ℤ, P ((𝟙_ (DerivedCategory C))⟦n⟧)) →
    (∀ {I : Type (u + 1)} (Y : I → DerivedCategory C) (S : DerivedCategory C)
      (ι : ∀ i, Y i ⟶ S), IsColimit (Cofan.mk S ι) → (∀ i, P (Y i)) → P S) →
    (∀ T : Pretriangulated.Triangle (DerivedCategory C),
      T ∈ Pretriangulated.distinguishedTriangles → P T.obj₁ → P T.obj₂ → P T.obj₃) →
    (∀ {X Y : DerivedCategory C}, Retract X Y → P Y → P X) →
    ∀ K : DerivedCategory C, P K

variable {C}
  {D : Type uD} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]

private theorem projection_isIso_of_generation_aux (hgen : UnitGeneration C)
    (L : DerivedCategory C ⥤ DerivedCategory D)
    [L.CommShift ℤ] [L.IsTriangulated] [L.IsLeftAdjoint]
    (R : DerivedCategory D ⥤ DerivedCategory C)
    [R.CommShift ℤ] [R.IsTriangulated]
    [∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) R]
    (E : DerivedCategory D)
    (τ : tensorLeft (R.obj E) ⟶ (L ⋙ tensorLeft E) ⋙ R)
    [NatTrans.CommShift τ ℤ] (hunit : IsIso (τ.app (𝟙_ _)))
    (K : DerivedCategory C) : IsIso (τ.app K) := by
  apply hgen (fun K ↦ IsIso (τ.app K)) _ _ _ _ K
  · intro n
    exact (NatTrans.isIso_app_shift_iff τ _ n).mpr hunit
  · intro I Y S ι hc hY
    have : IsIso (Functor.whiskerLeft (Discrete.functor Y) τ) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro i
      exact hY i.as
    exact isIso_app_coconePt_of_preservesColimit (Discrete.functor Y) τ (Cofan.mk S ι) hc
  · intro T hT h₁ h₂
    exact NatTrans.isIso_app_obj₃_of_isIso_app_obj₁₂ τ hT h₁ h₂
  · intro Y Z h hZ
    have := hZ
    exact NatTrans.isIso_app_of_retract τ h

attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory in
private theorem module_unitGeneration_aux (Λ : Type (u + 1)) [CommRing Λ] :
    UnitGeneration (ModuleCat.{u + 1} Λ) := by
  intro P hshift hcop htri hret K
  apply derivedModuleFreeGeneration.{u + 1, 0} Λ K P _ hcop htri hret
  intro n
  apply hret (Retract.ofIso ?_) (hshift n)
  apply (shiftFunctor _ n).mapIso
  exact (DerivedCategory.singleFunctor _ 0).mapIso
    (ULift.moduleEquiv : ULift.{0} Λ ≃ₗ[Λ] Λ).toModuleIso ≪≫
      DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ)

end Generation

section ProjectionData

variable {C : Type uC} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type uD} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

private theorem projection_data_aux
    (R : DerivedCategory D ⥤ DerivedCategory C) (adj : F.leftDerivedFunctor ⊣ R)
    (E : DerivedCategory D) :
    ∃ sL : F.leftDerivedFunctor.CommShift ℤ, letI := sL
      ∃ sR : R.CommShift ℤ, letI := sR
        F.leftDerivedFunctor.IsTriangulated ∧ R.IsTriangulated ∧
        (let τ : tensorLeft (R.obj E) ⟶ (F.leftDerivedFunctor ⋙ tensorLeft E) ⋙ R :=
          (adj.rightAdjointProjectionMap F.cachedDerivedTensorComparison).app E
        NatTrans.CommShift τ ℤ ∧ IsIso (τ.app (𝟙_ _))) := by
  rw [Functor.cachedDerivedTensorComparison_eq]
  generalize he : F.leftDerivedFunctorIsoMapDerivedCategory = e
  let := Functor.CommShift.ofIso e.symm ℤ
  have := Functor.CommShift.ofIso_compatibility
    e.symm ℤ
  have : NatTrans.CommShift e.hom ℤ :=
    inferInstanceAs
      (NatTrans.CommShift e.symm.inv ℤ)
  have : F.leftDerivedFunctor.IsTriangulated :=
    Functor.isTriangulated_of_iso e.symm
  have : NatTrans.CommShift F.leftDerivedFunctorCounit ℤ := by
    have hfac := F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    rw [he] at hfac
    rw [← hfac]
    infer_instance
  let := adj.rightAdjointCommShift ℤ
  have := Adjunction.commShift_of_leftAdjoint adj ℤ
  have := Adjunction.isTriangulated_rightAdjoint adj
  have : F.leftDerivedFunctor.IsLeftAdjoint := adj.isLeftAdjoint
  let τ : tensorLeft (R.obj E) ⟶ (F.leftDerivedFunctor ⋙ tensorLeft E) ⋙ R :=
    (adj.rightAdjointProjectionMap F.leftDerivedTensorComparison).app E
  have := exactComparison_commShift_aux F (R.obj E)
  have : NatTrans.CommShift τ ℤ :=
    Adjunction.commShift_rightAdjointProjectionMap_app adj F.leftDerivedTensorComparison E
  have hunit : IsIso (τ.app (𝟙_ _)) := by
    have := derivedUnitComparison_isIso F
    have hη := derivedComparison_rightUnit F
    have h := adj.rightAdjointProjectionMap_rightUnitality
      F.leftDerivedTensorComparison (derivedUnitComparison F) hη E
    let g := R.map (E ◁ derivedUnitComparison F) ≫ R.map (ρ_ E).hom
    have : IsIso g := by dsimp only [g]; infer_instance
    have : IsIso (τ.app (𝟙_ _) ≫ g) := by
      change IsIso (_ ≫ R.map (E ◁ derivedUnitComparison F) ≫ R.map (ρ_ E).hom)
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right (τ.app (𝟙_ _)) g
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hunit⟩

end ProjectionData

namespace AlgebraicGeometry.Etale
private theorem module_isZero_of_underlying_iso
    {Λ : Type (u + 1)} [CommRing Λ] (A : ModuleCat.{u + 1} Λ)
    (B : AddCommGrpCat.{u + 1})
    (e : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj A ≅ B)
    (hB : Subsingleton B) : IsZero A := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact @Function.Injective.subsingleton _ _ _
    (ConcreteCategory.bijective_of_isIso e.hom).1 hB

private theorem finite_module_cd_aux
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hcd : X.torsionEtaleCohomologicalDimension < ⊤)
    (hΛ : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0) :
    HasFiniteCohomologicalDimension Λ X := by
  obtain ⟨d, hd, hdt⟩ := (sInf_lt_iff).mp hcd
  obtain ⟨n, rfl, hn⟩ := hd
  refine ⟨n, fun M q hq ↦ ?_⟩
  obtain ⟨r, hr, hΛr⟩ := hΛ
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have hM : (U.obj M).IsTorsion := by
    apply Sheaf.IsTorsion.of_forall_isAddTorsion
    intro V
    change IsAddTorsion (M.obj.obj V)
    intro x
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    refine ⟨r, hr, ?_⟩
    have hx : (r : Λ) • (x : M.obj.obj V) = 0 := by
      rw [hΛr, zero_smul]
    simpa only [Nat.cast_smul_eq_nsmul] using hx
  have hq0 : 0 ≤ q := (Int.natCast_nonneg n).trans hq.le
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = (k : ℤ) :=
    ⟨q.toNat, (Int.toNat_of_nonneg hq0).symm⟩
  have hzero := hn (U.obj M) hM k (Int.ofNat_lt.mp hq)
  obtain ⟨e⟩ := Scheme.nonempty_etaleModuleCohomology_forgetIso X Λ k
  exact module_isZero_of_underlying_iso _ _ (e.app M) hzero

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

omit [HasSmallSiteSheafify A] in
private theorem constant_projection_map_isIso_aux (hgen : UnitGeneration A)
    (X : Scheme.{u}) [(constantSheaf X.smallEtaleTopology A).Monoidal]
    [(constantSheaf X.smallEtaleTopology A).PreservesFlat]
    [∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) (rightDerivedGlobalSections A X)]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) (K : DerivedCategory A) :
    IsIso (constantDerivedProjectionMap A X E K) := by
  let F := constantSheaf X.smallEtaleTopology A
  let R := rightDerivedGlobalSections A X
  let L := F.leftDerivedFunctor
  unfold constantDerivedProjectionMap
  generalize derivedConstantGlobalSectionsAdjunction A X = adj
  obtain ⟨sL, sR, hL, hR, hs, hu⟩ := projection_data_aux F R adj E
  let := sL
  let := sR
  have := hL
  have := hR
  let τ : tensorLeft (R.obj E) ⟶ (L ⋙ tensorLeft E) ⋙ R :=
    (adj.rightAdjointProjectionMap F.cachedDerivedTensorComparison).app E
  have := hs
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  exact projection_isIso_of_generation_aux hgen L R E τ hu K
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- On a quasi-compact quasi-separated scheme of finite torsion etale cohomological
dimension, the canonical constant-complex projection map is invertible for all unbounded
complexes over any torsion commutative coefficient ring. Torsion of a unital ring is
expressed by a positive integer annihilating its unit; it then annihilates every element.
Source: Stacks Tag 0F12 (blueprint: lem-kun-0f12).

Proof:
1. Choose a natural cohomological-dimension bound from the defining infimum. A positive
integer annihilating the coefficient ring annihilates every section of every module sheaf.
Thus the underlying abelian sheaf is torsion. The coefficient-forgetting cohomology
isomorphism transfers its vanishing above the bound to module-valued cohomology.
2. Apply the source library's finite-cohomological-dimension coproduct theorem (Stacks
0F11) to obtain preservation of all coproducts by derived global sections.
3. Work with the actual derived constant/global-sections adjunction defining the map.
Exactness identifies the left derived functor with the termwise derived functor, giving
its shift structure and triangulatedness. The right adjoint inherits compatible shifts
and is triangulated. To check the derived tensor comparison against shifts, choose a
flat resolution whose source and constant image are K-flat. Its defining tensor/counit
square gives shift compatibility on that representative; naturality transports it across
the representative's isomorphism to an arbitrary first input. Taking the adjunction mate
therefore gives the required shift-compatible projection transformation.
4. Both functors in that transformation preserve coproducts: tensoring is a left adjoint
in the closed derived monoidal categories, derived constants are a left adjoint, and
Step 2 handles derived global sections. Construct the unit comparison from the localization
unit and the derived counit. Its right-unit law follows on common K-flat representatives
and then by naturality. The adjunction's unitality identity gives invertibility at the unit.
5. The isomorphism locus contains every shift of the rank-one free module, using its
identification with the derived tensor unit. Naturality and preservation of coproducts
give coproduct closure; the third-isomorphism triangle theorem gives triangle closure;
naturality gives retract closure. Apply derived-module free generation (Stacks 09PB) to
conclude invertibility at every complex. No boundedness restriction is imposed.
-/
theorem isIso_constantDerivedProjectionMap_of_finite_torsion_cd
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hcd : X.torsionEtaleCohomologicalDimension < ⊤)
    (hΛ : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0)
    (E : DerivedCategoryModule Λ X) (K : DerivedCategory (ModuleCat.{u + 1} Λ)) :
    IsIso (constantDerivedProjectionMap (ModuleCat.{u + 1} Λ) X E K) := by
  have (J : Type (u + 1)) : PreservesColimitsOfShape (Discrete J)
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X) :=
    preservesCoproducts_rightDerivedGlobalSections Λ X (finite_module_cd_aux Λ X hcd hΛ) J
  exact constant_projection_map_isIso_aux (ModuleCat.{u + 1} Λ)
    (module_unitGeneration_aux Λ) X E K

end AlgebraicGeometry.Etale
