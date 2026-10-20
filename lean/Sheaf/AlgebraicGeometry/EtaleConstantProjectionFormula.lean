/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
import WeilConjectures.CategoryTheory.DerivedCategory.ModuleCatGeneration
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapUnit
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift

/-!
# Tensoring derived global sections with a constant complex

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-sf-kunneth-ordinary/
lem-kun-0f12.md; Stacks Project, etale-cohomology.tex, Tag 0F12
(blueprint: lem-kun-0f12).
-/

@[expose] public section

set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

universe v

private theorem projection_unit
    (D C : Type*) [Category.{u + 1} D] [Category.{u + 1} C]
    [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution D]
    [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (f : D ⥤ C) [f.Additive] [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [f.PreservesFlat] [f.IsLeftAdjoint] [f.Monoidal]
    (R : DerivedCategory C ⥤ DerivedCategory D) (adj : f.leftDerivedFunctor ⊣ R)
    (E : DerivedCategory C) :
    IsIso (((adj.rightAdjointProjectionMap f.leftDerivedTensorComparison).app E).app (𝟙_ _)) := by
  let L := f.leftDerivedFunctor
  have hrep (Z : DerivedCategory D) :
      ∃ P, f.kFlatMap P ∧ Nonempty (DerivedCategory.Qh.obj P ≅ Z) := by
    let B := (inferInstance : Abelian.HasFunctorialFlatResolution D).some.reduced
    let Z₀ := DerivedCategory.Q.objPreimage Z
    let P := B.resolutionFunctor.obj Z₀
    refine ⟨(HomotopyCategory.quotient _ _).obj P,
      f.kFlatMap_quotient_obj_resolutionFunctor_obj B Z₀, ⟨?_⟩⟩
    exact (DerivedCategory.quotientCompQhIso _).app P ≪≫
      asIso (DerivedCategory.Q.map (B.resolutionNatTrans.app Z₀)) ≪≫
      DerivedCategory.Q.objObjPreimageIso Z
  let oplax : L.OplaxMonoidal := by
    have := DerivedCategory.isIso_ε_Qh C
    exact Functor.OplaxMonoidal.ofLaxSquare
      (Q₁ := DerivedCategory.Qh) (Q₂ := DerivedCategory.Qh)
      (F := f.mapHomotopyCategory (.up ℤ)) f.leftDerivedTensorComparison
      (fun a ↦ f.leftDerivedFunctorCounit.app a)
      (fun _ _ q ↦ f.leftDerivedFunctorCounit.naturality q)
      f.leftDerivedTensorComparison_app_app_comp_tensorHom f.kFlatMap hrep
      (fun a _ hb ↦ Functor.isIso_μNatTrans_Qh_app_app_of_kFlat a _ hb)
  let := oplax
  have : IsIso (Functor.OplaxMonoidal.η L) := by
    have := DerivedCategory.isIso_ε_Qh (D)
    have := DerivedCategory.isIso_ε_Qh C
    have : IsIso (Functor.OplaxMonoidal.η (f.mapHomotopyCategory (.up ℤ))) := by
      rw [Functor.mapHomotopyCategory_η]
      infer_instance
    exact inferInstanceAs (IsIso (L.map (Functor.LaxMonoidal.ε DerivedCategory.Qh) ≫
      f.leftDerivedFunctorCounit.app (𝟙_ _) ≫
      DerivedCategory.Qh.map (Functor.OplaxMonoidal.η (f.mapHomotopyCategory (.up ℤ))) ≫
      inv (Functor.LaxMonoidal.ε DerivedCategory.Qh)))
  exact Adjunction.isIso_rightAdjointProjectionMap_app_app_tensorUnit adj
    f.leftDerivedTensorComparison (fun _ _ ↦ rfl) E

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.leftDerivedTensorComparison

private theorem tensor_comparison_shift
    (D C : Type*) [Category.{u + 1} D] [Category.{u + 1} C]
    [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution D]
    [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (f : D ⥤ C) [f.Additive] [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [f.PreservesFlat] [f.IsLeftAdjoint] [f.Monoidal]
    [f.leftDerivedFunctor.CommShift ℤ]
    [NatTrans.CommShift f.leftDerivedFunctorCounit ℤ]
    (Z : DerivedCategory D) :
    let φ : (curriedTensor (DerivedCategory D)).obj Z ⋙ f.leftDerivedFunctor ⟶
      f.leftDerivedFunctor ⋙
        (curriedTensor (DerivedCategory C)).obj (f.leftDerivedFunctor.obj Z) :=
      f.leftDerivedTensorComparison.app Z
    NatTrans.CommShift φ ℤ := by
  let L := f.leftDerivedFunctor
  let B := (inferInstance : Abelian.HasFunctorialFlatResolution
    (D)).some.reduced
  let Z₀ := DerivedCategory.Q.objPreimage Z
  let P := B.resolutionFunctor.obj Z₀
  have hP := B.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le Z₀
  have hfP := f.kFlatMap_quotient_obj_resolutionFunctor_obj B Z₀
  let z : Z ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P) :=
    (DerivedCategory.Q.objObjPreimageIso Z).symm ≪≫
      (asIso (DerivedCategory.Q.map (B.resolutionNatTrans.app Z₀))).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app P
  have hp : NatTrans.CommShift
      (F₁ := (curriedTensor (DerivedCategory D)).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ⋙ L)
      (F₂ := L ⋙ (curriedTensor (DerivedCategory C)).obj
        (L.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))))
      (f.leftDerivedTensorComparison.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) ℤ := by
    apply DerivedCategory.commShift_of_tensorLeft_fac f L f.leftDerivedFunctorCounit
      ((HomotopyCategory.quotient _ _).obj P)
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hP) hfP
    intro M
    simpa only [MonoidalCategory.tensorHom_def, Category.assoc,
      DerivedCategory.tensorLeftCounit, Functor.bifunctorCounit₁_app,
      Functor.LaxMonoidal.μNatTrans_app_app, L, Functor.comp_obj,
      Functor.leftDerivedDerivedTensor, Functor.postcompose₂_obj_obj_obj_obj,
      curriedTensor_obj_obj] using
      f.leftDerivedTensorComparison_app_app_comp_tensorHom
        ((HomotopyCategory.quotient _ _).obj P) M
  have heq : f.leftDerivedTensorComparison.app Z =
      Functor.whiskerRight ((curriedTensor _).map z.hom) L ≫
        f.leftDerivedTensorComparison.app _ ≫
        Functor.whiskerLeft L ((curriedTensor _).map (L.map z.inv)) := by
    ext M
    have hn := congr_app (f.leftDerivedTensorComparison.naturality z.hom) M
    dsimp at hn ⊢
    rw [reassoc_of% hn, ← MonoidalCategory.comp_whiskerRight, ← Functor.map_comp,
      z.hom_inv_id]
    simp
  have : NatTrans.CommShift ((curriedTensor (DerivedCategory D)).map z.hom) ℤ :=
    Functor.CommShift₂.commShift_map (h := .int) _
  have : NatTrans.CommShift ((curriedTensor (DerivedCategory C)).map (L.map z.inv)) ℤ :=
    Functor.CommShift₂.commShift_map (h := .int) _
  let δ : (curriedTensor (DerivedCategory D)).obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ⋙ L ⟶
      L ⋙ (curriedTensor (DerivedCategory C)).obj
        (L.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) :=
    f.leftDerivedTensorComparison.app _
  have : NatTrans.CommShift δ ℤ := hp
  have hδ : NatTrans.CommShift
      (Functor.whiskerRight ((curriedTensor (DerivedCategory D)).map z.hom) L ≫ δ ≫
        Functor.whiskerLeft L ((curriedTensor (DerivedCategory C)).map (L.map z.inv))) ℤ :=
    inferInstance
  rw [heq]
  exact hδ

private theorem projection_exact
    (D C : Type*) [Category.{u + 1} D] [Category.{u + 1} C]
    [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution D]
    [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (f : D ⥤ C) [f.Additive] [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [f.PreservesFlat] [f.IsLeftAdjoint] [f.Monoidal]
    (R : DerivedCategory C ⥤ DerivedCategory D) (adj : f.leftDerivedFunctor ⊣ R)
    (E : DerivedCategory C) :
    ∃ (_ : f.leftDerivedFunctor.CommShift ℤ) (_ : R.CommShift ℤ),
      f.leftDerivedFunctor.IsTriangulated ∧ R.IsTriangulated ∧
      NatTrans.CommShift
        (F₁ := (curriedTensor (DerivedCategory D)).obj (R.obj E))
        (F₂ := (f.leftDerivedFunctor ⋙ (curriedTensor (DerivedCategory C)).obj E) ⋙ R)
        ((adj.rightAdjointProjectionMap f.leftDerivedTensorComparison).app E) ℤ := by
  let L := f.leftDerivedFunctor
  let e := f.leftDerivedFunctorIsoMapDerivedCategory
  let : L.CommShift ℤ := Functor.CommShift.ofIso e.symm ℤ
  have : NatTrans.CommShift e.symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility e.symm ℤ
  have : NatTrans.CommShift e.hom ℤ := NatTrans.CommShift.of_iso_inv e.symm ℤ
  have : L.IsTriangulated := Functor.isTriangulated_of_iso e.symm
  let : R.CommShift ℤ := adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : R.IsTriangulated := adj.isTriangulated_rightAdjoint
  have : NatTrans.CommShift f.leftDerivedFunctorCounit ℤ := by
    have : NatTrans.CommShift f.leftDerivedFunctorIsoMapDerivedCategory.hom ℤ :=
      inferInstanceAs (NatTrans.CommShift e.hom ℤ)
    rw [← f.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
    infer_instance
  let τ : (curriedTensor (DerivedCategory (D))).obj (R.obj E) ⟶
      (L ⋙ (curriedTensor _).obj E) ⋙ R :=
    (adj.rightAdjointProjectionMap f.leftDerivedTensorComparison).app E
  have : NatTrans.CommShift τ ℤ := by
    have := tensor_comparison_shift _ C f (R.obj E)
    have : NatTrans.CommShift
        ((curriedTensor (DerivedCategory C)).map (adj.counit.app E)) ℤ :=
      Functor.CommShift₂.commShift_map (h := .int) _
    exact Adjunction.commShift_rightAdjointProjectionMap_app
      (F := L) (G := R) (T_D := curriedTensor (DerivedCategory D))
      (T_C := curriedTensor (DerivedCategory C)) adj f.leftDerivedTensorComparison E
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

private def projectionIsIso
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D ⥤ D} (τ : F ⟶ G) : Prop :=
  ∀ (E : C) (K : D), IsIso ((τ.app E).app K)

private theorem projection_from_generator
    (D C : Type*) [Category.{u + 1} D] [Category.{u + 1} C]
    [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution D]
    [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (hgen : ∀ (F G : DerivedCategory D ⥤ DerivedCategory D)
      [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
      [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F]
      [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G]
      (τ : F ⟶ G) [NatTrans.CommShift τ ℤ], IsIso (τ.app (𝟙_ _)) → IsIso τ)
    (f : D ⥤ C) [f.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [f.PreservesFlat] [f.IsLeftAdjoint] [f.Monoidal]
    (R : DerivedCategory C ⥤ DerivedCategory D)
    (adj : f.leftDerivedFunctor ⊣ R)
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) R]
    : projectionIsIso (adj.rightAdjointProjectionMap f.leftDerivedTensorComparison) := by
  intro E K
  obtain ⟨sL, sR, hL, hR, hτ⟩ := projection_exact D C f R adj E
  let := sL
  let := sR
  let := hL
  let := hR
  let L := f.leftDerivedFunctor
  let τ : (curriedTensor (DerivedCategory D)).obj (R.obj E) ⟶
      (L ⋙ (curriedTensor _).obj E) ⋙ R :=
    (adj.rightAdjointProjectionMap f.leftDerivedTensorComparison).app E
  have : NatTrans.CommShift τ ℤ := hτ
  have (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) L :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : IsIso τ := hgen _ _ τ (projection_unit D C f R adj E)
  exact inferInstanceAs (IsIso (τ.app K))

private theorem module_generator (Λ : Type (u + 1)) [CommRing Λ]
    (F G : DerivedCategory (ModuleCat.{u + 1} Λ) ⥤
      DerivedCategory (ModuleCat.{u + 1} Λ))
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ] (h : IsIso (τ.app (𝟙_ _))) :
    IsIso τ := by
  apply DerivedCategory.isIso_of_isIso_app_singleFunctor_obj_self τ
  let e : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj
      (ModuleCat.of Λ Λ) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u + 1} Λ)) :=
    DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ)
  exact (NatTrans.isIso_app_iff_of_iso τ e).2 h

private theorem module_zero_of_forget_iso (Λ : Type (u + 1)) [CommRing Λ]
    (M : ModuleCat.{u + 1} Λ) (A : AddCommGrpCat.{u + 1})
    (e : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M ≅ A)
    [Subsingleton A] : IsZero M := by
  have : Subsingleton M := e.addCommGroupIsoToAddEquiv.injective.subsingleton
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

private theorem module_functor_zero_of_forget_iso (Λ : Type (u + 1)) [CommRing Λ]
    {C : Type*} [Category* C] (F : C ⥤ ModuleCat.{u + 1} Λ)
    (G : C ⥤ AddCommGrpCat.{u + 1})
    (e : F ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅ G)
    (M : C) (h : Subsingleton (G.obj M)) : IsZero (F.obj M) := by
  have := h
  exact module_zero_of_forget_iso Λ _ _ (e.app M)

private theorem constant_projection_from_generator
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (hgen : ∀ (F G : DerivedCategory A ⥤ DerivedCategory A)
      [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
      [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F]
      [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G]
      (τ : F ⟶ G) [NatTrans.CommShift τ ℤ], IsIso (τ.app (𝟙_ _)) → IsIso τ)
    (X : Scheme.{u}) [(constantSheaf X.smallEtaleTopology A).Monoidal]
    [(constantSheaf X.smallEtaleTopology A).PreservesFlat]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (rightDerivedGlobalSections A X)] :
    ∀ (E : DerivedCategory (Sheaf X.smallEtaleTopology A)) (K : DerivedCategory A),
      IsIso (constantDerivedProjectionMap A X E K) := by
  exact (constantProjectionComponents A X).isIso
    (projection_from_generator _ _ hgen (constantSheaf X.smallEtaleTopology A) _
      (derivedConstantGlobalSectionsAdjunction A X))

private theorem torsion_of_torsion_ring (Λ : Type (u + 1)) [CommRing Λ]
    (M : Type*) [AddCommGroup M] [Module Λ M]
    (hΛ : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0) : IsAddTorsion M := by
  intro s
  obtain ⟨m, hm, hz⟩ := hΛ
  apply (isOfFinAddOrder_iff_nsmul_eq_zero).mpr
  refine ⟨m, hm, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul Λ, hz, zero_smul]

private theorem integer_bound_of_natural_bound (P : ℤ → Prop) (n : ℕ)
    (h : ∀ q : ℕ, n < q → P q) : ∀ q : ℤ, (n : ℤ) < q → P q := by
  intro q hq
  obtain ⟨q, rfl⟩ : ∃ k : ℕ, q = k := ⟨q.toNat, by omega⟩
  exact h q (by omega)

private theorem module_functors_bound_of_forget_iso (Λ : Type (u + 1)) [CommRing Λ]
    {C : Type*} [Category* C] (F : ℤ → C ⥤ ModuleCat.{u + 1} Λ)
    (G : ℤ → C ⥤ AddCommGrpCat.{u + 1}) (n : ℕ)
    (hG : ∀ (M : C) (q : ℕ), n < q → Subsingleton ((G q).obj M))
    (e : ∀ q : ℕ, Nonempty
      (F q ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅ G q)) :
    ∀ (M : C) (q : ℤ), (n : ℤ) < q → IsZero ((F q).obj M) := by
  intro M
  refine integer_bound_of_natural_bound (fun q ↦ IsZero ((F q).obj M)) n ?_
  intro q hq
  obtain ⟨e⟩ := e q
  exact module_functor_zero_of_forget_iso Λ _ _ e M (hG M q hq)

private theorem exists_natural_bound (P : ℕ → Prop)
    (h : sInf {d : ℕ∞ | ∃ n : ℕ, d = (n : ℕ∞) ∧ P n} < ⊤) : ∃ n, P n := by
  obtain ⟨d, ⟨n, rfl, hn⟩, _⟩ := sInf_lt_iff.mp h
  exact ⟨n, hn⟩

private theorem finite_coefficient_dimension
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hcd : X.torsionEtaleCohomologicalDimension < ⊤)
    (hΛ : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0) :
    HasFiniteCohomologicalDimension Λ X := by
  classical
  obtain ⟨n, hn⟩ := exists_natural_bound _ hcd
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have ht (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      (U.obj M).IsTorsion := by
    apply Sheaf.IsTorsion.of_forall_isAddTorsion
    intro V
    exact torsion_of_torsion_ring Λ (M.obj.obj V) hΛ
  refine ⟨n, module_functors_bound_of_forget_iso Λ
    (fun q ↦ DerivedCategory.singleFunctor _ 0 ⋙ cohomology (ModuleCat.{u + 1} Λ) X q)
    (fun q ↦ U ⋙ DerivedCategory.singleFunctor _ 0 ⋙ cohomology AddCommGrpCat.{u + 1} X q)
    n (fun M q hq ↦ hn (U.obj M) (ht M) q hq)
    (Scheme.nonempty_etaleModuleCohomology_forgetIso X Λ)⟩



/-- On a quasi-compact quasi-separated scheme of finite torsion etale cohomological
dimension, the canonical constant-complex projection map is invertible for all unbounded
complexes over any torsion commutative coefficient ring. Torsion of a unital ring is
expressed by a positive integer annihilating its unit; it then annihilates every element.
Source: Stacks Tag 0F12 (blueprint: lem-kun-0f12).

Proof plan from the DAG:
1. Write $\mathcal A=\operatorname{Mod}(X_{\Et},\Lambda)$ and $\Gamma=\Gamma(X,-):\mathcal
A\to\operatorname{Mod}(\Lambda)$. The category $\mathcal A$ is Grothendieck abelian. Sections are
additive and preserve kernels, so $\Gamma$ is left exact. Put $d=\kuncd(X)<\infty$. A torsion
unital ring has some integer $n\ge1$ with $n1=0$, hence every $\Lambda$-module sheaf is a torsion
abelian sheaf. The coefficient-forgetting cohomology comparison therefore gives $R^q\Gamma(M)=0$
for all $M\in\mathcal A$ and $q>d$. For any set-indexed family $(M_i)$, its sum is the filtered
colimit of its finite subsums, in both module sheaves and underlying abelian sheaves. Finite sums
of injective resolutions are injective resolutions (extend a map into each coordinate separately),
and additivity gives $R^q\Gamma(\bigoplus_{i\in J}M_i)=\bigoplus_{i\in J}R^q\Gamma(M_i)$ for
finite $J$. Cohomology commutes with this filtered colimit on the qcqs scheme $X$, including
constant-ring module coefficients. Thus the canonical map $\bigoplus_iR^q\Gamma(M_i)\to
R^q\Gamma(\bigoplus_iM_i)$ is an isomorphism for every $q\ge0$. This proves the sheaf-level input
of Stacks 0F11 for the actual ring $\Lambda$, rather than assuming its stated $\mathbf Z/n$
conclusion also covers $\Lambda$.
Dependencies: lem-weil-pbc-module-sheaves-grothendieck-abelian,
def-weil-pbc-global-sections-functor, def-kun-cd, lem-weil-pbc-etale-module-cohomology-forget,
lem-weil-pbc-module-sheaves-colimits-forgetful, lem-weil-pbc-cohomology-filtered-colimit.

2. For an arbitrary family $(E_i)$ in $D(\mathcal A)$ choose K-injective representatives
$I_i^\bullet$ with injective terms. The termwise sum $J^\bullet=\bigoplus_i I_i^\bullet$
represents $\bigoplus_iE_i$. Each injective term is $\Gamma$-acyclic: the resolution concentrated
in degree zero computes its higher derived sections as zero. Step 1 gives
$R^q\Gamma(J^r)=\bigoplus_i R^q\Gamma(I_i^r)=0$ for $q>0$. The unbounded acyclic-complex theorem
applies, with the uniform bound $d$, and computes $R\Gamma(E_i)$ and $R\Gamma(\bigoplus_iE_i)$ by
$\Gamma(I_i^\bullet)$ and $\Gamma(J^\bullet)$ respectively, naturally on all coprojections. The
$q=0$ comparison of Step 1 gives a termwise isomorphism
$\theta^r:\bigoplus_i\Gamma(I_i^r)\to\Gamma(J^r)$. Since $d_J\iota_i=\iota_i d_{I_i}$, equality on
every coprojection gives $\Gamma(d_J)\theta^r=\theta^{r+1}(\bigoplus_i\Gamma(d_{I_i}))$. Thus
$\theta$ is a complex isomorphism preserving coprojections. Termwise sums compute coproducts in
$D(\Lambda)$, proving that the canonical comparison $\bigoplus_iR\Gamma(E_i)\to
R\Gamma(\bigoplus_iE_i)$ is invertible. No assertion that $J^\bullet$ is K-injective is needed.
Dependencies: lem-pur-kinjective-degreewise-existence, lem-kun-grothendieck-derived-coproducts,
lem-kun-finite-cd-acyclic-complex, lem-pc-derived-module-direct-sums.

3. Let $a:(\operatorname{Sh}(X_{\Et}),\Lambda_X)\to(\operatorname{Sets},\Lambda)$ be the terminal
geometric morphism, presented using the small etale site and the one-object point site. Its module
inverse image is the constant-sheaf functor: a presheaf map from the constant presheaf $M$ to a
sheaf $F$ is determined by its component $M\to F(X)$ at the terminal object, and conversely
restriction of that component defines every component on $U\to X$. For the constant presheaf of
rings $\mathcal O(U)=\Lambda$, the component maps are $\Lambda$-linear. The module-sheafification
interface, applied to this presheaf ring and the constant presheaf module $M$, extends its action
to $\mathcal O^\#=\Lambda_X$ and identifies $\Lambda_X$-linear maps $\underline M\to F$ with these
presheaf $\Lambda$-linear maps, hence with module maps $M\to\Gamma(X,F)$, and its coefficient ring
map is the identity $a^{-1}\Lambda=\Lambda_X$. The constant-complex construction preserves
quasi-isomorphisms, so $La^*K=\underline K$. The derived ringed-topos adjunction identifies $Ra_*$
with $R\Gamma$. Apply the ringed projection-mate statement to this morphism and the fixed $E$. It
supplies exact functors $F(K)=R\Gamma(E)\otimes^L_\Lambda K$ and $G(K)=R\Gamma(E\otimes^L_\Lambda
La^*K)$ and a natural transformation $\alpha:F\to G$, compatible with shifts and distinguished
triangles. Its component is adjoint to $(\varepsilon_E\otimes1)\mu_{R\Gamma(E),K}$, hence is
exactly the canonical map in the item, including its connecting-square compatibility.
Dependencies: def-kun-constant-sheaf, lem-weil-pbc-ringed-projection-mate-exact,
lem-pc-sites-module-sheafification-interface.

4. The functor $F$ preserves set-indexed coproducts. Here is the module-complex argument, so that
no etale-sheaf tensor lemma is misapplied to $D(\Lambda)$. On the point site choose K-flat
flat-term models $P$ of $R\Gamma(E)$ and $C_i$ of $K_i$. The canonical distribution map
$\operatorname{Tot}(P\otimes\bigoplus_i C_i)\cong\bigoplus_i\operatorname{Tot}(P\otimes C_i)$
sends $p\otimes(c_i)_i$ to $(p\otimes c_i)_i$ on finite-support tensors; its inverse uses the
coprojections. Both maps respect $d_P\otimes1+(-1)^p1\otimes d_C$. For an acyclic complex $B$, the
degree-$n$ distribution isomorphism is $\bigoplus_{p+q=n}B^p\otimes(\bigoplus_i
C_i^q)\cong\bigoplus_i\bigoplus_{p+q=n}B^p\otimes C_i^q$, with the displayed signed differentials.
Thus $\operatorname{Tot}(B\otimes(\bigoplus_i C_i))$ is the sum of the acyclic
$\operatorname{Tot}(B\otimes C_i)$, whose cycles and boundaries are respectively the sums of
cycles and boundaries. The terms of $\bigoplus_i C_i$ are flat, since tensoring a module short
exact sequence with a sum is the sum of the exact tensor sequences. The derived-tensor descent
statement now computes both sides by these total complexes. Termwise module sums compute derived
coproducts, so the displayed isomorphism localizes to the canonical coproduct comparison for $F$.
This also includes the empty family.
Dependencies: lem-pc-kflat-resolution, def-pc-kflat-complex, def-pc-flat-sheaf-modules,
def-pc-tensor-complex-sheaves, lem-weil-pbc-site-derived-tensor-descent,
lem-pc-derived-module-direct-sums.

5. The functor $G$ preserves set-indexed coproducts as well. The derived adjunction of Step 3
makes $L=La^*$ a left adjoint to $R=R\Gamma$. Explicitly
Hom(L(⨁ᵢ Kᵢ), H) = Hom(⨁ᵢ Kᵢ, RH) = ∏ᵢ Hom(Kᵢ, RH) = ∏ᵢ Hom(LKᵢ, H),
naturally in $H$, and the bijections take the legs to $L$ of the original coprojections. This is
the coproduct universal property, so $L$ preserves these sums. Tensor with $E$ in the etale
derived category preserves sums by the cited tensor theorem. Applying the coproduct comparison for
$R\Gamma$ proved in Step 2 proves the assertion for their composite $G$. Under the two functors'
coproduct comparisons, naturality on each coprojection identifies $\alpha_{\bigoplus_iK_i}$ with
$\bigoplus_i\alpha_{K_i}$. Thus if every $\alpha_{K_i}$ is invertible, the direct sum of their
inverses is an inverse of this component.
Dependencies: lem-weil-pbc-ringed-projection-mate-exact, lem-kun-derived-tensor-direct-sums.

6. Let $\mathcal C$ be the full subcategory of $D(\Lambda)$ consisting of $K$ for which $\alpha_K$
is invertible. Under the tensor-unit identifications the projection mate satisfies
$\alpha_\Lambda=1_{R\Gamma(E)}$. Its compatibility with integer shifts identifies
$\alpha_{\Lambda[k]}$ with the shift of that identity, so $\Lambda[k]\in\mathcal C$ for every
integer $k$. Dependency: lem-weil-pbc-ringed-projection-mate-exact.

7. For a distinguished triangle in $D(\Lambda)$, Step 3 produces a morphism between its images
under $F$ and $G$, including the shifted connecting square. The third-isomorphism triangle theorem
shows that if two vertices lie in $\mathcal C$, then the third does too. The class is also closed
under isomorphisms by naturality and under retracts: if $i:K\to H$, $r:H\to K$ satisfy $ri=1$ and
$\alpha_H$ is invertible, then $F(r)\alpha_H^{-1}G(i):G(K)\to F(K)$ is inverse to $\alpha_K$.
Indeed naturality gives $\alpha_K F(r)=G(r)\alpha_H$ and $G(i)\alpha_K=\alpha_H F(i)$, so the two
composites reduce to $G(ri)$ and $F(ri)$. Together with Steps 4-5 this proves all required closure
properties.
Dependencies: lem-weil-pbc-ringed-projection-mate-exact, lem-sf-triangle-morphism-iso.

8. Apply derived-module free generation with $A=\Lambda$. The subcategory $\mathcal C$ contains
all shifts $\Lambda[k]$ by Step 6 and is closed under set-indexed direct sums, third vertices of
distinguished triangles, and retracts by Steps 5 and 7. It therefore contains every object of
$D(\Lambda)$. Hence $\alpha_K$ is invertible for the arbitrary complex $K$ in the statement. This
is precisely the canonical tensor-with-constant-complex map identified in Step 3.
Dependency: lem-pc-derived-module-free-generation.
-/
theorem isIso_constantDerivedProjectionMap_of_finite_torsion_cd
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hcd : X.torsionEtaleCohomologicalDimension < ⊤)
    (hΛ : ∃ n : ℕ, 0 < n ∧ (n : Λ) = 0)
    (E : DerivedCategoryModule Λ X) (K : DerivedCategory (ModuleCat.{u + 1} Λ)) :
    IsIso (constantDerivedProjectionMap (ModuleCat.{u + 1} Λ) X E K) := by
  classical
  have hdim := finite_coefficient_dimension Λ X hcd hΛ
  have (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I)
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X) :=
    preservesCoproducts_rightDerivedGlobalSections Λ X hdim I
  exact constant_projection_from_generator (ModuleCat.{u + 1} Λ) (module_generator Λ) X E K

end AlgebraicGeometry.Etale
