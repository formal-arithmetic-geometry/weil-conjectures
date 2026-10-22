/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.IntegralDerivedCoefficientData
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Paper.FormalClosedSupportDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Triangulated.Triangulated
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Data.Fin.Tuple.Basic
import all Sheaf.Paper.FormalClosedSupportSheaves
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality
import Sheaf.Paper.IntegralHeartLocalDualityDescent
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Sheaf.Paper.IntegralConstantModelLocalResolution
import Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
import Sheaf.Paper.FiniteConstantModelsCommonStratification
import Sheaf.Paper.FiniteConstantModelStrataGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Integral stratum filtrations and the global derived Hom formula

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-ext,
sk-lem-int-ext-formula.md and its proof, clauses (1)--(2)
(blueprint: det-lem-int-ext-formula).

The coefficients, constructibility, ordinary relative derived tensor and internal Hom
are the recorded constructions. Global sections are Hom from the regular module,
as in the ringed-site hypercohomology definition, here in the module-object encoding.
The inverse-limit clause uses strict towers of complexes and the recorded Roos triangle.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u v w w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj
open ZeroObject

attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory

private theorem triangleFiltration_of_extensionProductIter
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C]
    (P : ObjectProperty C) (n : ℕ) (X : C) (hX : P.extensionProductIter n X) :
    ∃ (m : ℕ) (F : Fin (m + 1) → C) (T : Fin m → Triangle C),
      IsZero (F 0) ∧ F (Fin.last m) = X ∧ ∀ r : Fin m,
        T r ∈ distTriang C ∧ (T r).obj₁ = F r.castSucc ∧
          (T r).obj₂ = F r.succ ∧ P (T r).obj₃ := by
  induction n generalizing X with
  | zero =>
    let F : Fin 2 → C := Fin.cases (0 : C) (fun _ ↦ X)
    refine ⟨1, F, fun _ ↦ Triangle.mk (0 : 0 ⟶ X) (𝟙 X) 0,
      isZero_zero C, rfl, ?_⟩
    intro r
    have hr : r = 0 := Subsingleton.elim _ _
    subst r
    exact ⟨contractible_distinguished₁ X, rfl, rfl, hX⟩
  | succ n ih =>
    rw [ObjectProperty.extensionProductIter_succ'] at hX
    obtain ⟨Y, Z, f, g, h, hT, hY, hZ⟩ := hX
    obtain ⟨m, F, T, hF0, hFlast, hsteps⟩ := ih Y hY
    let F' : Fin (m + 2) → C := Fin.snoc F X
    let T' : Fin (m + 1) → Triangle C := Fin.snoc T (Triangle.mk f g h)
    refine ⟨m + 1, F', T', ?_, (by simp [F']), ?_⟩
    · simpa only [F', Fin.snoc_apply_zero] using hF0
    · intro r
      induction r using Fin.lastCases with
      | last =>
        have he : (Fin.last m).succ = Fin.last (m + 1) := Fin.ext rfl
        simpa [T', F', he, hFlast] using
          (show Triangle.mk f g h ∈ distTriang C ∧ Y = Y ∧ X = X ∧ P Z from
            ⟨hT, rfl, rfl, hZ⟩)
      | cast r =>
        simpa only [T', F', Fin.snoc_castSucc, Fin.succ_castSucc] using hsteps r

private theorem extensionHull_triangle
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsZero T.obj₁ ∨ ∃ n, P.extensionProductIter n T.obj₁)
    (h₃ : IsZero T.obj₃ ∨ ∃ n, P.extensionProductIter n T.obj₃) :
    IsZero T.obj₂ ∨ ∃ n, P.extensionProductIter n T.obj₂ := by
  have hi (n : ℕ) : (P.extensionProductIter n).IsClosedUnderIsomorphisms := by
    cases n with
    | zero => exact inferInstanceAs P.IsClosedUnderIsomorphisms
    | succ n => rw [ObjectProperty.extensionProductIter_succ]; infer_instance
  rcases h₁ with hz | ⟨n, hn⟩
  · have := (T.isZero₁_iff_isIso₂ hT).mp hz
    rcases h₃ with hz' | ⟨n, hn⟩
    · exact Or.inl (hz'.of_iso (asIso T.mor₂))
    · exact Or.inr ⟨n, (P.extensionProductIter n).prop_of_iso
        (asIso T.mor₂).symm hn⟩
  · rcases h₃ with hz | ⟨m, hm⟩
    · have := (T.isZero₃_iff_isIso₁ hT).mp hz
      exact Or.inr ⟨n, (P.extensionProductIter n).prop_of_iso (asIso T.mor₁) hn⟩
    · refine Or.inr ⟨n + 1 + m, ?_⟩
      rw [ObjectProperty.extensionProductIter_add P (show n + 1 = n + 1 from rfl)]
      exact ⟨T.obj₁, T.obj₃, T.mor₁, T.mor₂, T.mor₃, hT, hn, hm⟩

private theorem mapDerivedLimitTriangle
    {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (K : ℕ → C) [HasProduct K] [HasProduct (fun n ↦ F.obj (K n))]
    [PreservesLimit (Discrete.functor K) F]
    (f : ∀ n, K (n + 1) ⟶ K n) (A : C) (p : A ⟶ ∏ᶜ K)
    (δ : ∏ᶜ K ⟶ A⟦(1 : ℤ)⟧) (h : IsDerivedLimitTriangle f A p δ) :
    ∃ ε : (∏ᶜ fun n ↦ F.obj (K n)) ⟶ (F.obj A) ⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle (fun n ↦ F.map (f n)) (F.obj A)
        (Pi.lift (fun n ↦ F.map (p ≫ Pi.π K n))) ε := by
  let e := PreservesProduct.iso F K
  let ε := e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app A
  refine ⟨ε, ?_⟩
  have he (n : ℕ) : e.hom ≫ Pi.π (fun n ↦ F.obj (K n)) n =
      F.map (Pi.π K n) := piComparison_comp_π F K n
  have hp : F.map p ≫ e.hom = Pi.lift (fun n ↦ F.map (p ≫ Pi.π K n)) := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, he, ← F.map_comp, Pi.lift_π]
  have ht : F.map (towerTransitionEndomorphism f) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (fun n ↦ F.map (f n)) := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, he, ← F.map_comp]
    rw [(towerTransitionEndomorphism_eq_iff f _).mp rfl n, F.map_sub, F.map_comp]
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
      Preadditive.comp_sub, Category.comp_id, Category.assoc, Pi.lift_π]
    simp only [← Category.assoc, he]
  change Triangle.mk _ _ ε ∈ distinguishedTriangles
  let t := Triangle.mk p (towerTransitionEndomorphism f) δ
  let t' := Triangle.mk (Pi.lift (fun n ↦ F.map (p ≫ Pi.π K n)))
    (towerTransitionEndomorphism (fun n ↦ F.map (f n))) ε
  have et : F.mapTriangle.obj t ≅ t' :=
    Triangle.isoMk _ _ (Iso.refl _) e e
      (by simpa only [t, t', Functor.mapTriangle, Triangle.mk_mor₁,
          Iso.refl_hom, Category.id_comp] using hp)
      (by exact ht)
      (by
        change (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app A) ≫
          (shiftFunctor D (1 : ℤ)).map (𝟙 (F.obj A)) = e.hom ≫ ε
        simp [ε])
  exact isomorphic_distinguished _ (F.map_distinguished t h) _ et.symm

private theorem shortExact_dualizable_tor {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [MonoidalClosed A] [BraidedCategory A] [HasDerivedCategory.{v} A]
    [Abelian.HasFunctorialFlatResolution A]
    {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : IsDualizable S.X₁) (h₂ : IsDualizable S.X₂) :
    IsDualizable ((DerivedCategory.singleFunctor A 0).obj S.X₃) ∧
    DerivedCategory.torAmplitudeIn A (-1) 0
      ((DerivedCategory.singleFunctor A 0).obj S.X₃) := by
  refine ⟨DerivedCategory.isDualizable_singleFunctor_obj_of_shortExact hS h₁ h₂, ?_⟩
  let S' := S.map (HomologicalComplex.single A (.up ℤ) 0)
  have hS' : S'.ShortExact := hS.map_of_exact _
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS'
  have : (CochainComplex.mappingCone S'.f).IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  have : (CochainComplex.mappingCone S'.f).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  let e := asIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S')) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ A 0).app S.X₃).symm
  exact (DerivedCategory.torAmplitudeIn A (-1) 0).prop_of_iso e
    (DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ (-1) 0
      (fun n ↦ (DerivedCategory.isDualizable_mappingCone_single_X h₁ h₂ S'.f n).flat))

private theorem shortExact_dualizable_tor_of_iso
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]
    {T : ShortComplex A} (hT : T.ShortExact)
    (h₁ : IsDualizable T.X₁) (h₂ : IsDualizable T.X₂)
    {M : A} (e : T.X₃ ≅ M) :
    IsDualizable ((DerivedCategory.singleFunctor A 0).obj M) ∧
      DerivedCategory.torAmplitudeIn A (-1) 0
        ((DerivedCategory.singleFunctor A 0).obj M) := by
  have h := shortExact_dualizable_tor hT h₁ h₂
  let e' := (DerivedCategory.singleFunctor A 0).mapIso e
  exact ⟨h.1.of_iso e', (DerivedCategory.torAmplitudeIn A (-1) 0).prop_of_iso e' h.2⟩

private theorem complexTensor_preservesColimits
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    (P : CochainComplex A ℤ) :
    PreservesColimitsOfSize.{v, v} ((curriedTensor (CochainComplex A ℤ)).obj P) := by
  exact (CochainComplex.tensorHomAdjunction P).leftAdjoint_preservesColimits

private theorem tensorKFlatModel
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]
    (D : DerivedCategory A) :
    ∃ P : CochainComplex.KFlat A,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ D) ∧
      Nonempty (DerivedCategory.Q ⋙ (curriedTensor (DerivedCategory A)).obj D ≅
        (curriedTensor (CochainComplex A ℤ)).obj P.obj ⋙ DerivedCategory.Q) := by
  classical
  let Aflat := DerivedCategory.TensorCommShift₂.LKFlat A
  have : Aflat.EssSurj := Localization.essSurj Aflat
    (HomologicalComplex.quasiIso A (.up ℤ)).WKFlat
  have hP : ∃ P : CochainComplex.KFlat A, Nonempty (Aflat.obj P ≅ D) :=
    ⟨Aflat.objPreimage D, ⟨Aflat.objObjPreimageIso D⟩⟩
  obtain ⟨P, ⟨e⟩⟩ := hP
  let q := DerivedCategory.quotientCompQhIso A
  let t := (asIso (DerivedCategory.TensorCommShift₂.liftingIsoHom A)).app P
  refine ⟨P, ⟨(q.app P.obj).symm ≪≫ e⟩, ⟨?_⟩⟩
  exact Functor.isoWhiskerRight q.symm ((curriedTensor (DerivedCategory A)).obj D) ≪≫
    Functor.isoWhiskerLeft
      (HomotopyCategory.quotient A (.up ℤ) ⋙ DerivedCategory.Qh)
      ((curriedTensor (DerivedCategory A)).mapIso e.symm) ≪≫ t ≪≫
    Functor.isoWhiskerLeft ((curriedTensor (CochainComplex A ℤ)).obj P.obj) q

private abbrev rootMonoidal
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] :
    MonoidalCategory (DerivedCategory C) := inferInstance

private abbrev rootDualizable
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (K : DerivedCategory C) := IsDualizable K

private theorem rootDualizable_of_iso
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (K L : DerivedCategory C) (e : K ≅ L) (h : rootDualizable K) :
    rootDualizable L := h.of_iso e

private abbrev rootComplexMonoidal
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] :
    MonoidalCategory (CochainComplex C ℤ) := inferInstance

private abbrev rootComplexTensor
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] :=
  curriedTensor (CochainComplex C ℤ)

private theorem pairTensorLimits
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (D K : C) [ExactPairing D K] :
    PreservesLimitsOfSize.{w, w'} (tensorLeft D) :=
  (tensorLeftAdjunction D K).rightAdjoint_preservesLimits

private abbrev rootTensor
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (D : DerivedCategory C) := tensorLeft D

private abbrev rootUnit
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C] :
    DerivedCategory C := 𝟙_ (DerivedCategory C)

private theorem dualConsequences
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (K D : DerivedCategory C)
    (H F : DerivedCategory C ⥤ DerivedCategory C)
    (TC : CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (eTC : TC = rootComplexTensor (C := C))
    (adjH : rootTensor K ⊣ H) (eF : F = rootTensor D)
    (eD : D ≅ H.obj (rootUnit (C := C)))
    (hdual : IsDualizable K)
    (hK : DerivedCategory.torAmplitudeIn C (-1) 0 K) :
    DerivedCategory.torAmplitudeIn C 0 1 D ∧ Nonempty (H ≅ F) ∧
    (∃ P : CochainComplex.KFlat C,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ D) ∧
      Nonempty (DerivedCategory.Q ⋙ F ≅
        TC.obj P.obj ⋙ DerivedCategory.Q) ∧
      ∀ (I : Type v) [SmallCategory I] [IsFiltered I],
        PreservesColimitsOfShape I (TC.obj P.obj)) ∧
    (∀ (B : ℕᵒᵖ ⥤ CochainComplex C ℤ)
      [HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n)))]
      [HasProduct (fun n : ℕ ↦ F.obj (DerivedCategory.Q.obj (B.obj (op n))))]
      (A : DerivedCategory C)
      (p : A ⟶ ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n))))
      (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n)))) ⟶ A⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ DerivedCategory.Q.map (B.map (homOfLE (Nat.le_succ n)).op)) A p δ →
      ∃ ε : (∏ᶜ (fun n : ℕ ↦ F.obj (DerivedCategory.Q.obj (B.obj (op n))))) ⟶
          (F.obj A)⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle
          (fun n : ℕ ↦ F.map
            (DerivedCategory.Q.map (B.map (homOfLE (Nat.le_succ n)).op)))
          (F.obj A) (Pi.lift (fun n : ℕ ↦ F.map
            (p ≫ Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n))) n))) ε) := by
  subst TC
  subst F
  obtain ⟨d⟩ := hdual
  let := d
  obtain ⟨braid⟩ := DerivedCategory.nonempty_braidedCategory C
  let := braid
  let D₀ := Kᘁ
  let := BraidedCategory.exactPairing_swap K D₀
  let eh : H ≅ tensorLeft D₀ := adjH.rightAdjointUniq (tensorLeftAdjunction D₀ K)
  let ed : D ≅ D₀ := eD ≪≫ eh.app _ ≪≫ ρ_ D₀
  let pairD : ExactPairing D K := exactPairingCongrLeft ed
  let F := tensorLeft D
  let := pairD
  have hD₀ : DerivedCategory.torAmplitudeIn C 0 1 D₀ :=
    DerivedCategory.torAmplitudeIn_of_exactPairing hK
  have hD := (DerivedCategory.torAmplitudeIn C 0 1).prop_of_iso ed.symm hD₀
  have : PreservesLimitsOfSize.{0, 0} F := pairTensorLimits D K
  obtain ⟨P, eP, eT⟩ := tensorKFlatModel D
  have hPcolim (I : Type v) [SmallCategory I] [IsFiltered I] :
      PreservesColimitsOfShape I ((curriedTensor (CochainComplex C ℤ)).obj P.obj) := by
    have := complexTensor_preservesColimits P.obj
    infer_instance
  refine ⟨hD, ⟨eh ≪≫ (curriedTensor _).mapIso ed.symm⟩,
    ⟨P, eP, eT, hPcolim⟩, ?_⟩
  intro B _ _ A p δ h
  exact mapDerivedLimitTriangle F
    (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n)))
    (fun n ↦ DerivedCategory.Q.map (B.map (homOfLE (Nat.le_succ n)).op)) A p δ h

private def composeStratumSectionsIso
    {C₀ : Type*} {C₁ : Type*} {C₂ : Type*} {C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    {H₀ : C₀ ⥤ C₀} {R R' : C₀ ⥤ C₁} {H₁ : C₁ ⥤ C₁} {I : C₁ ⥤ C₀}
    {P U : C₁ ⥤ C₂} {H₂ T : C₂ ⥤ C₂} {V : C₂ ⥤ C₁}
    {Γ₀ : C₀ ⥤ C₃} {Γ₁ : C₁ ⥤ C₃} {Γ₂ : C₂ ⥤ C₃}
    (ec : H₀ ≅ R ⋙ H₁ ⋙ I) (eo : H₁ ≅ P ⋙ H₂ ⋙ V)
    (ei : I ⋙ Γ₀ ≅ Γ₁) (ev : V ⋙ Γ₁ ≅ Γ₂)
    (es : R ≅ R') (ep : P ≅ U) (ed : H₂ ≅ T) :
    H₀ ⋙ Γ₀ ≅ R' ⋙ U ⋙ T ⋙ Γ₂ :=
  Functor.isoWhiskerRight ec Γ₀ ≪≫
    Functor.isoWhiskerLeft (R ⋙ H₁) ei ≪≫
    Functor.isoWhiskerLeft R
      (Functor.isoWhiskerRight eo Γ₁ ≪≫ Functor.isoWhiskerLeft (P ⋙ H₂) ev) ≪≫
    Functor.isoWhiskerRight es (P ⋙ H₂ ⋙ Γ₂) ≪≫
    Functor.isoWhiskerLeft R'
      (Functor.isoWhiskerRight ep (H₂ ⋙ Γ₂) ≪≫
        Functor.isoWhiskerLeft U (Functor.isoWhiskerRight ed Γ₂))

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarComp lowerStarComp
  openImmersionLowerShriek




/-- Derived global sections for modules over a condensed coefficient ring.
Source: blueprint det-lem-int-ext-formula, global-sections convention
(blueprint: det-lem-int-ext-formula). -/
abbrev stratumModuleDerivedSections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] (X : Scheme.{u}) :=
  (preadditiveCoyoneda.obj (op (Mod.regular (condensedRingObj Λ X))) :
    supportModules Λ X ⥤ Ab.{u + 1}).rightDerivedFunctor

/-- The uncompleted derived dual, with the coefficient ring kept abstract.
Source: blueprint det-lem-int-ext-formula, clause (2)
(blueprint: det-lem-int-ext-formula). -/
def stratumModuleDual
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) (L : supportModules Λ S) :=
  ((derivedHom Λ S).obj (op ((DerivedCategory.singleFunctor _ 0).obj L))).obj
    (𝟙_ (DerivedCategory (supportModules Λ S)))

/-- Tensor by the uncompleted derived dual over an abstract coefficient ring.
Source: blueprint det-lem-int-ext-formula, clause (2)
(blueprint: det-lem-int-ext-formula). -/
def stratumModuleDualTensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) (L : supportModules Λ S) :=
  (derivedTensor Λ S).obj (stratumModuleDual Λ S L)


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Global sections are Hom from the regular integral module. This is the same
`Hom(O,-)` construction as def-pur-ringed-site-zeroth-hypercohomology, specialized
using preadditiveCoyoneda to the recorded module-object category.
Source: blueprint det-lem-int-ext-formula, opening convention for global derived Hom
(blueprint: det-lem-int-ext-formula). -/
abbrev integralStratumSections (X : Scheme.{u}) :
    pulledBackModuleObjects (integralCoefficientRing l E) X ⥤ Ab.{u + 1} :=
  preadditiveCoyoneda.obj (op (Mod.regular (condensedRingObj (integralCoefficientRing l E) X)))

/-- Full derived sections, computed by the canonical K-injective replacement, before
applying any homology functor. Source: blueprint det-lem-int-ext-formula, opening convention;
Stacks Project, Section 07A5 (blueprint: det-lem-int-ext-formula). -/
def integralStratumDerivedSections (X : Scheme.{u}) :
    integralDerived l E X ⥤ DerivedCategory Ab.{u + 1} :=
  stratumModuleDerivedSections (integralCoefficientRing l E) X

/-- The derived dual of a stratum sheaf, including torsion sheaves, with values in the
ordinary uncompleted module derived category.
Source: blueprint det-lem-int-ext-formula, clause (2)
(blueprint: det-lem-int-ext-formula). -/
def integralStratumDual (S : Scheme.{u})
    (L : pulledBackModuleObjects (integralCoefficientRing l E) S) : integralDerived l E S :=
  stratumModuleDual (integralCoefficientRing l E) S L

/-- Tensoring by the recorded derived dual, using the existing uncompleted relative tensor.
Source: blueprint det-lem-int-ext-formula, clause (2)
(blueprint: det-lem-int-ext-formula). -/
def integralStratumDualTensor (S : Scheme.{u})
    (L : pulledBackModuleObjects (integralCoefficientRing l E) S) :
    integralDerived l E S ⥤ integralDerived l E S :=
  stratumModuleDualTensor (integralCoefficientRing l E) S L

private theorem finiteModelOfIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y : Scheme.{u}}
    {M N : supportModules Λ Y} (e : M ≅ N)
    (hM : HasFiniteConstantLocalModel Λ Y M) : HasFiniteConstantLocalModel Λ Y N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun a ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU a
  exact ⟨P, hP, ⟨(upperStar Λ (U.f a)).mapIso e.symm ≪≫ eP⟩⟩

private theorem finiteModel_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
    (M : supportModules Λ Y) (hm : HasFiniteConstantLocalModel Λ Y M) :
    IsConstantModelConstructible Λ Y M := by
  classical
  let R : Scheme.Stratification Y := {
    n := 1
    stratum := fun _ ↦ Set.univ
    isLocallyClosed_stratum := fun _ ↦ isClosed_univ.isLocallyClosed
    isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
    iUnion_stratum_eq_univ := by ext x; simp
    pairwise_disjoint_stratum := by
      intro i j h
      exact (h (Subsingleton.elim i j)).elim
    domain := fun _ ↦ Y
    immersion := fun _ ↦ 𝟙 Y
    range_immersion := fun _ ↦ by simp }
  have hY : CompactSpace Y ∧ QuasiSeparatedSpace Y := ⟨inferInstance, inferInstance⟩
  change (if CompactSpace Y ∧ QuasiSeparatedSpace Y then _ else _)
  rw [if_pos hY]
  refine ⟨R, fun r ↦ ?_⟩
  exact finiteModelOfIso Λ ((upperStarId Λ Y).symm.app M) hm

private theorem genericStratumFiltration
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (C : DerivedCategory (supportModules Λ X))
    (hC : constantModelBoundedConstructible Λ X C) :
    ∃ (S : X.FiniteLocallyClosedStratification) (m : ℕ)
      (F : Fin (m + 1) → DerivedCategory (supportModules Λ X))
      (T : Fin m → Triangle (DerivedCategory (supportModules Λ X))),
      IsZero (F 0) ∧ Nonempty (F (Fin.last m) ≅ C) ∧
      ∀ r : Fin m,
        T r ∈ Pretriangulated.distinguishedTriangles ∧
        (T r).obj₁ = F r.castSucc ∧ (T r).obj₂ = F r.succ ∧
        ∃ (a : Fin S.n) (Z : Scheme.{u}) (v : S.domain a ⟶ Z) (i : Z ⟶ X)
          (_ : IsOpenImmersion v) (_ : IsClosedImmersion i),
          v ≫ i = S.immersion a ∧
          ∃ (L : supportModules Λ (S.domain a)) (n : ℤ),
            IsConstantModelConstructible Λ (S.domain a) L ∧
            HasFiniteConstantLocalModel Λ (S.domain a) L ∧
            (DerivedCategory.homologyConcentratedIn 0 0 C → n = 0) ∧
            Nonempty ((T r).obj₃ ≅
              ((DerivedCategory.singleFunctor _ 0).obj
                ((lowerStar Λ i).obj
                  ((openImmersionLowerShriek Λ v).obj L))) ⟦n⟧) := by
  classical
  let A := supportModules Λ X
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hC.1
  let N := (b - a + 1).toNat
  let M (j : Fin N) := (DerivedCategory.homologyFunctor A (a + j.val)).obj C
  obtain ⟨R, hred, ⟨Z, i, v, hi, hv, hr⟩, hmodels, _⟩ :=
    finiteConstantModels_commonReducedStratification Λ X N M (fun j ↦ hC.2 _)
  let P : ObjectProperty (DerivedCategory A) := fun D ↦
    ∃ (a : Fin R.n) (Z : Scheme.{u}) (v : R.domain a ⟶ Z) (i : Z ⟶ X)
      (_ : IsOpenImmersion v) (_ : IsClosedImmersion i),
      v ≫ i = R.immersion a ∧
      ∃ (L : supportModules Λ (R.domain a)) (n : ℤ),
        IsConstantModelConstructible Λ (R.domain a) L ∧
        HasFiniteConstantLocalModel Λ (R.domain a) L ∧
        (DerivedCategory.homologyConcentratedIn 0 0 C → n = 0) ∧
        Nonempty (D ≅ ((DerivedCategory.singleFunctor _ 0).obj
          ((lowerStar Λ i).obj ((openImmersionLowerShriek Λ v).obj L))) ⟦n⟧)
  have : P.IsClosedUnderIsomorphisms := by
    refine ⟨?_⟩
    intro D D' e h
    obtain ⟨r, W, u, t, hu, ht, he, L, n, hL, hm, hn, ⟨ei⟩⟩ := h
    exact ⟨r, W, u, t, hu, ht, he, L, n, hL, hm, hn, ⟨e.symm ≪≫ ei⟩⟩
  let Q : ObjectProperty (DerivedCategory A) := fun D ↦
    IsZero D ∨ ∃ n, P.extensionProductIter n D
  have hiP (n : ℕ) : (P.extensionProductIter n).IsClosedUnderIsomorphisms := by
    cases n with
    | zero => exact inferInstanceAs P.IsClosedUnderIsomorphisms
    | succ n => rw [ObjectProperty.extensionProductIter_succ]; infer_instance
  have : Q.IsClosedUnderIsomorphisms := by
    refine ⟨?_⟩
    intro D D' e h
    rcases h with hz | ⟨n, hn⟩
    · exact Or.inl (hz.of_iso e.symm)
    · exact Or.inr ⟨n, (P.extensionProductIter n).prop_of_iso e hn⟩
  let B : ℤ → ObjectProperty A := fun q F ↦
    IsZero F ∨ ∃ j : Fin N, a + j.val = q ∧ Nonempty (F ≅ M j)
  have (q : ℤ) : (B q).IsClosedUnderIsomorphisms := by
    refine ⟨?_⟩
    intro F G e h
    rcases h with hz | ⟨j, hj, ⟨ej⟩⟩
    · exact Or.inl (hz.of_iso e.symm)
    · exact Or.inr ⟨j, hj, ⟨e.symm ≪≫ ej⟩⟩
  have hQ : Q C := by
    apply DerivedCategory.prop_of_bounded_of_degreewise Q
      (fun _ hz ↦ Or.inl hz) (fun T hT h₁ h₃ ↦ extensionHull_triangle P T hT h₁ h₃)
      B (fun q F hF ↦ ?_) C hC.1 (fun q ↦ ?_)
    · rcases hF with hz | ⟨j, hj, ⟨ej⟩⟩
      · exact Or.inl ((DerivedCategory.singleFunctor A q).map_isZero hz)
      have hq (hc : DerivedCategory.homologyConcentratedIn 0 0 C) (hn : q ≠ 0) :
          IsZero F := by
        have hz : IsZero ((DerivedCategory.homologyFunctor A q).obj C) := by
          rcases lt_or_gt_of_ne hn with h | h
          · exact (DerivedCategory.isGE_iff _ _).mp hc.1 q h
          · exact (DerivedCategory.isLE_iff _ _).mp hc.2 q h
        have eq : M j ≅ (DerivedCategory.homologyFunctor A q).obj C :=
          eqToIso (by simp only [M, hj])
        exact hz.of_iso (ej ≪≫ eq)
      by_cases hh : DerivedCategory.homologyConcentratedIn 0 0 C ∧ q ≠ 0
      · exact Or.inl ((DerivedCategory.singleFunctor A q).map_isZero (hq hh.1 hh.2))
      have hqn : DerivedCategory.homologyConcentratedIn 0 0 C → -q = 0 := by
        intro hc
        have : q = 0 := by by_contra hn; exact hh ⟨hc, hn⟩
        simp only [this, neg_zero]
      let Q' : ObjectProperty (DerivedCategory A) := fun D ↦ Q (D⟦-q⟧)
      have : Q'.IsClosedUnderIsomorphisms :=
        ⟨fun e h ↦ Q.prop_of_iso ((shiftFunctor _ (-q)).mapIso e) h⟩
      have hF' : Q' ((DerivedCategory.singleFunctor A 0).obj F) := by
        apply finiteConstantModel_fixedStrata_generation Λ X R Z i v hi hv hr Q'
          (fun D hz ↦ Or.inl ((shiftFunctor _ (-q)).map_isZero hz))
          (fun T hT h₁ h₃ ↦ extensionHull_triangle P
            ((shiftFunctor _ (-q)).mapTriangle.obj T)
            ((shiftFunctor _ (-q)).map_distinguished T hT) h₁ h₃) F
        intro r
        have := (hi r.castSucc).1
        have := (hv r).1
        have := R.isImmersion r
        have : TopologicalSpace.NoetherianSpace (R.domain r) :=
          (R.immersion r).isEmbedding.isInducing.noetherianSpace
        have hm : HasFiniteConstantLocalModel Λ (R.domain r)
            ((upperStar Λ (R.immersion r)).obj F) :=
          finiteModelOfIso Λ ((upperStar Λ (R.immersion r)).mapIso ej.symm) (hmodels j r)
        exact Or.inr ⟨0, r, Z r.castSucc, v r, i r.castSucc,
          inferInstance, inferInstance, (hv r).2,
          (upperStar Λ (R.immersion r)).obj F, -q,
          finiteModel_constructible Λ _ _ hm, hm, hqn, ⟨Iso.refl _⟩⟩
      exact Q.prop_of_iso (((DerivedCategory.singleFunctors A).shiftIso
        (-q) q 0 (by omega)).app F) hF'
    · by_cases hq : a ≤ q ∧ q ≤ b
      · let j : Fin N := ⟨(q - a).toNat, by dsimp [N]; omega⟩
        have hj : a + (j.val : ℤ) = q := by dsimp [j]; omega
        exact Or.inr ⟨j, hj, ⟨eqToIso (by simp only [M, hj])⟩⟩
      · apply Or.inl
        rcases lt_or_ge q a with h | h
        · exact (DerivedCategory.isGE_iff _ _).mp ha q h
        · exact (DerivedCategory.isLE_iff _ _).mp hb q (by omega)
  rcases hQ with hz | ⟨n, hn⟩
  · refine ⟨R, 0, fun _ ↦ C, Fin.elim0, hz, ⟨Iso.refl C⟩, fun r ↦ Fin.elim0 r⟩
  · obtain ⟨m, F, T, hF0, hFlast, hsteps⟩ :=
      triangleFiltration_of_extensionProductIter P n C hn
    exact ⟨R, m, F, T, hF0, ⟨eqToIso hFlast⟩, hsteps⟩


/-- Finite distinguished-triangle filtration by shifts of integral stratum sheaves;
if the input is a sheaf in degree zero, every shift can be zero.
Source: blueprint det-lem-int-ext-formula, clause (1)
(blueprint: det-lem-int-ext-formula).

Proof: finite type over the field makes X Noetherian. Bounded constructibility gives
finitely many nonzero cohomology sheaves. Choose a common ordered reduced stratification
for these sheaves, with open strata in successive reduced closed tails. Localization
on these tails expresses each cohomology sheaf as a finite extension of its stratum
restrictions extended by zero. Shift this extension property by minus the cohomological
degree. If C is concentrated in degree zero, every other cohomology sheaf is zero, so
all retained shifts are zero. Bounded derived devissage puts C in the extension closure
of the shifted stratum pieces. Associativity of triangle extensions flattens this
closure into an actual finite chain of distinguished triangles. The zero object is
handled by a chain of length zero; the constructions also include the empty scheme. -/
theorem integral_stratum_filtration
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (C : integralDerived l E X)
    (hC : constantModelBoundedConstructible (integralCoefficientRing l E) X C) :
    ∃ (S : X.FiniteLocallyClosedStratification) (m : ℕ)
      (F : Fin (m + 1) → integralDerived l E X)
      (T : Fin m → Triangle (integralDerived l E X)),
      IsZero (F 0) ∧ Nonempty (F (Fin.last m) ≅ C) ∧
      ∀ r : Fin m,
        T r ∈ Pretriangulated.distinguishedTriangles ∧
        (T r).obj₁ = F r.castSucc ∧ (T r).obj₂ = F r.succ ∧
        ∃ (a : Fin S.n) (Z : Scheme.{u}) (v : S.domain a ⟶ Z) (i : Z ⟶ X)
          (_ : IsOpenImmersion v) (_ : IsClosedImmersion i),
          v ≫ i = S.immersion a ∧
          ∃ (L : pulledBackModuleObjects (integralCoefficientRing l E) (S.domain a)) (n : ℤ),
            IsConstantModelConstructible (integralCoefficientRing l E) (S.domain a) L ∧
            HasFiniteConstantLocalModel (integralCoefficientRing l E) (S.domain a) L ∧
            (DerivedCategory.homologyConcentratedIn 0 0 C → n = 0) ∧
            Nonempty ((T r).obj₃ ≅
              ((DerivedCategory.singleFunctor _ 0).obj
                ((lowerStar (integralCoefficientRing l E) i).obj
                  ((openImmersionLowerShriek (integralCoefficientRing l E) v).obj L))) ⟦n⟧) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  exact genericStratumFiltration (integralCoefficientRing l E) X C hC


private abbrev genericDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] (X : Scheme.{u}) :=
  DerivedCategory (supportModules Λ X)

private theorem kernelClosedAdjunction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z V : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : V ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (hij : Set.range j = (Set.range i)ᶜ) :
    PreservesFiniteColimits (lowerStar Λ i) ∧
      Nonempty (lowerStar Λ i ⊣ closedModuleSectionsWithSupport Λ i j) := by
  obtain ⟨hAb, hAbsupport⟩ := ProEtale.abelian_closed_support i j hij
  have hi := moduleCounitOfAbelian Λ i hAb
  have hzero := openRestrictionPushforwardZero Λ i j hij
  have hsupport : ∀ M : pulledBackModuleObjects Λ X,
      IsZero ((upperStar Λ j).obj M) →
        IsIso ((upperStarLowerStarAdjunction Λ i).unit.app M) := by
    intro M hjM
    apply moduleUnitOfAbelian Λ i M
    apply hAbsupport
    exact ((Mod.forget _).map_isZero hjM).of_iso
      ((profinitePointModuleForgetPullbackIso Λ j).app M).symm
  have hjAb : IsIso (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j).counit := by
    have ff :=
      (ProEtale.openImmersionRestrictionLowerStarAdjunction Ab.{u + 1} j
        ).fullyFaithfulROfIsIsoCounit
    have := ff.full
    have := ff.faithful
    exact (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} j
      ).counit_isIso_of_R_fully_faithful
  have hjcounit := moduleCounitOfAbelian Λ j hjAb
  have hjoint : ∀ M : pulledBackModuleObjects Λ X,
      IsZero ((upperStar Λ i).obj M) → IsZero ((upperStar Λ j).obj M) → IsZero M := by
    intro M hiM hjM
    have := hsupport M hjM
    exact ((lowerStar Λ i).map_isZero hiM).of_iso
      (asIso ((upperStarLowerStarAdjunction Λ i).unit.app M))
  have hclosedExact := exactClosedOfDetection (upperStar Λ i) (lowerStar Λ i)
    (upperStar Λ j) (upperStarLowerStarAdjunction Λ i) hzero hjoint
  have ff := (upperStarLowerStarAdjunction Λ i).fullyFaithfulROfIsIsoCounit
  have := ff.full
  have := ff.faithful
  obtain ⟨_, ⟨adj⟩⟩ := kernelSupportAdjunction
    (upperStar Λ i) (lowerStar Λ i) (upperStar Λ j) (lowerStar Λ j)
    (upperStarLowerStarAdjunction Λ i) (upperStarLowerStarAdjunction Λ j) hzero hsupport
  change lowerStar Λ i ⊣ closedModuleSectionsWithSupport Λ i j at adj
  exact ⟨hclosedExact, ⟨adj⟩⟩

attribute [local irreducible] closedModuleSectionsWithSupport moduleSectionsWithSupport

private theorem closedHom_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z V : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : V ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] [PreservesFiniteColimits (lowerStar Λ i)]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (P : DerivedCategory (supportModules Λ Z)) :
    Nonempty ((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P)) ≅
      (closedSupport Λ i j).rightDerivedFunctor ⋙ (derivedHom Λ Z).obj (op P) ⋙
        (lowerStar Λ i).mapDerivedCategory) := by
  obtain ⟨_, _, c, _, _, _, _, cnat⟩ := openClosedInternalHomFormulas Λ i j hij
  exact ⟨NatIso.ofComponents (fun N ↦ c P N) (by
    intro N N' f
    simpa only [(lowerStar Λ i).mapDerivedCategory.map_id, op_id,
      (derivedHom Λ X).map_id, NatTrans.id_app, Category.id_comp,
      Functor.comp_obj, Functor.comp_map,
      (derivedHom Λ Z).map_id] using cnat P P N N' (𝟙 P) f)⟩

private theorem openHom_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z V : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : V ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : DerivedCategory (supportModules Λ V)) :
    Nonempty ((derivedHom Λ X).obj
        (op ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K)) ≅
      (supportPullback Λ j).mapDerivedCategory ⋙ (derivedHom Λ V).obj (op K) ⋙
        (lowerStar Λ j).rightDerivedFunctor) := by
  obtain ⟨_, o, _, _, _, _, onat, _⟩ := openClosedInternalHomFormulas Λ i j hij
  exact ⟨NatIso.ofComponents (fun N ↦ o K N) (by
    intro N N' f
    simpa only [(openImmersionLowerShriek Λ j).mapDerivedCategory.map_id, op_id,
      (derivedHom Λ X).map_id, NatTrans.id_app, Category.id_comp,
      Functor.comp_obj, Functor.comp_map,
      (derivedHom Λ V).map_id] using onat K K N N' (𝟙 K) f)⟩



-- Compare the structures before projecting their tensor functors. Direct functor
-- reduction expands the chosen localization and tensor totalization constructions.
private theorem monoidalRootEq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) :
    (inferInstance : MonoidalCategory (DerivedCategory (supportModules Λ S))) =
      rootMonoidal (C := supportModules Λ S) := rfl

private theorem tensorRootEq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (D : DerivedCategory (supportModules Λ S)) :
    (derivedTensor Λ S).obj D = rootTensor D := by
  exact congrArg
    (fun M ↦ @tensorLeft (DerivedCategory (supportModules Λ S)) inferInstance M D)
    (monoidalRootEq Λ S)

private theorem unitRootEq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) :
    (𝟙_ (DerivedCategory (supportModules Λ S))) = rootUnit (C := supportModules Λ S) := by
  exact congrArg
    (fun M : MonoidalCategory (DerivedCategory (supportModules Λ S)) ↦
      @MonoidalCategoryStruct.tensorUnit (DerivedCategory (supportModules Λ S))
        inferInstance M.toMonoidalCategoryStruct)
    (monoidalRootEq Λ S)

private theorem dualizableRootOfSource
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (K : DerivedCategory (supportModules Λ S))
    (h : IsDualizable K) : rootDualizable K := by
  exact Eq.mp (congrArg
    (fun M : MonoidalCategory (DerivedCategory (supportModules Λ S)) ↦
      @IsDualizable (DerivedCategory (supportModules Λ S)) inferInstance M K)
    (monoidalRootEq Λ S)) h

private theorem dualizableRootTransport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (K : DerivedCategory (supportModules Λ S))
    (h : rootDualizable K) : IsDualizable K := by
  exact Eq.mpr (congrArg
    (fun M : MonoidalCategory (DerivedCategory (supportModules Λ S)) ↦
      @IsDualizable (DerivedCategory (supportModules Λ S)) inferInstance M K)
    (monoidalRootEq Λ S)) h

-- The same comparison keeps tensor totalization abstract in the K-flat model clause.
private theorem complexMonoidalRootEq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) :
    (inferInstance : MonoidalCategory (CochainComplex (supportModules Λ S) ℤ)) =
      rootComplexMonoidal (C := supportModules Λ S) := rfl

private theorem complexTensorRootEq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) :
    curriedTensor (CochainComplex (supportModules Λ S) ℤ) =
      rootComplexTensor (C := supportModules Λ S) := by
  exact congrArg
    (fun M : MonoidalCategory (CochainComplex (supportModules Λ S) ℤ) ↦
      @curriedTensor (CochainComplex (supportModules Λ S) ℤ) inferInstance M)
    (complexMonoidalRootEq Λ S)

-- The preceding equations expose the needed comparisons without expanding chosen functors.
attribute [local irreducible] derivedHom derivedTensor

/-
Keep the full conclusion abstract across case motives and coefficient specialization.
-/
private def StratumHomResult
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z S V : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (v : S ⟶ Z) [IsOpenImmersion v]
    (j : V ⟶ X) [IsOpenImmersion j] (L : supportModules Λ S) : Prop :=
  ∃ (_ : (closedModuleSectionsWithSupport Λ i j).Additive),
    Nonempty
      ((derivedHom (Λ) X).obj
          (op ((DerivedCategory.singleFunctor _ 0).obj
            ((lowerStar (Λ) i).obj
              ((openImmersionLowerShriek (Λ) v).obj L)))) ⋙
            stratumModuleDerivedSections Λ X ≅
        (closedModuleSectionsWithSupport (Λ) i j).rightDerivedFunctor ⋙
          (upperStar (Λ) v).mapDerivedCategory ⋙
            stratumModuleDualTensor Λ S L ⋙
              stratumModuleDerivedSections Λ S) ∧
    DerivedCategory.torAmplitudeIn _ 0 1 (stratumModuleDual Λ S L) ∧
    (∃ P : CochainComplex.KFlat
        (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (Λ) S)),
      Nonempty (DerivedCategory.Q.obj P.obj ≅ stratumModuleDual Λ S L) ∧
      Nonempty (DerivedCategory.Q ⋙
          stratumModuleDualTensor Λ S L ≅
        (curriedTensor (CochainComplex
          (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
            (condensedRingObj (Λ) S)) ℤ)).obj P.obj ⋙
            DerivedCategory.Q) ∧
      ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I],
        PreservesColimitsOfShape I
          ((curriedTensor (CochainComplex
            (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
              (condensedRingObj (Λ) S)) ℤ)).obj P.obj)) ∧
    (∀ (B : ℕᵒᵖ ⥤ CochainComplex
        (pulledBackModuleObjects (Λ) S) ℤ)
      [HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n)))]
      [HasProduct (fun n : ℕ ↦
        (stratumModuleDualTensor Λ S L).obj
          (DerivedCategory.Q.obj (B.obj (op n))))]
      (A : genericDerived Λ S)
      (p : A ⟶ ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n))))
      (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n)))) ⟶ A⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ DerivedCategory.Q.map (B.map (homOfLE (Nat.le_succ n)).op)) A p δ →
      ∃ ε : (∏ᶜ (fun n : ℕ ↦
          (stratumModuleDualTensor Λ S L).obj (DerivedCategory.Q.obj (B.obj (op n))))) ⟶
        ((stratumModuleDualTensor Λ S L).obj A) ⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle
          (fun n : ℕ ↦
            (stratumModuleDualTensor Λ S L).map
              (DerivedCategory.Q.map (B.map (homOfLE (Nat.le_succ n)).op)))
          ((stratumModuleDualTensor Λ S L).obj A)
          (Pi.lift (fun n : ℕ ↦
            (stratumModuleDualTensor Λ S L).map
              (p ≫ Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n))) n))) ε)

-- Keep the completed coefficient object abstract throughout the categorical argument.
set_option maxHeartbeats 300000 in
-- This proof combines the natural Hom comparison, a K-flat model and its strict-tower API.
private theorem genericStratumHomFormula
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Z S V : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i] (v : S ⟶ Z) [IsOpenImmersion v]
    (j : V ⟶ X) [IsOpenImmersion j] (hij : Set.range j = (Set.range i)ᶜ)
    (L : supportModules Λ S)
    (_hL : IsConstantModelConstructible (Λ) S L)
    (hresolution : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ a : U.I₀,
      ∃ T : ShortComplex (supportModules Λ (U.X a)),
        T.ShortExact ∧ IsDualizable T.X₁ ∧ IsDualizable T.X₂ ∧
        Nonempty (T.X₃ ≅ (upperStar Λ (U.f a)).obj L)) :
    StratumHomResult Λ i v j L := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    let C := supportModules Λ S
    have : TopologicalSpace.NoetherianSpace V :=
      j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    have : QuasiCompact j := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    have : TopologicalSpace.NoetherianSpace Z :=
      i.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
    have : TopologicalSpace.NoetherianSpace S :=
      v.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    have hclosedData : PreservesFiniteColimits (lowerStar Λ i) ∧
        Nonempty (lowerStar Λ i ⊣ closedModuleSectionsWithSupport Λ i j) :=
      by
        set_option backward.isDefEq.respectTransparency true in
          exact @kernelClosedAdjunction Λ _ _ X Z V i _ j _ _ hij
    have hclosedExact : PreservesFiniteColimits (lowerStar Λ i) := hclosedData.1
    obtain ⟨adj⟩ := hclosedData.2
    obtain ⟨U, hU⟩ := hresolution
    have hlocal (a : U.I₀) :
        IsDualizable ((DerivedCategory.singleFunctor (supportModules Λ (U.X a)) 0).obj
          ((upperStar Λ (U.f a)).obj L)) ∧
        DerivedCategory.torAmplitudeIn _ (-1) 0
          ((DerivedCategory.singleFunctor (supportModules Λ (U.X a)) 0).obj
            ((upperStar Λ (U.f a)).obj L)) := by
      obtain ⟨T, hT, h₁, h₂, ⟨e⟩⟩ := hU a
      have h := shortExact_dualizable_tor_of_iso hT h₁ h₂ e
      exact ⟨dualizableRootTransport Λ (U.X a) _ h.1, h.2⟩
    let R : Profinite.CondensedRing.{u} := ⟨Λ⟩
    let K := (DerivedCategory.singleFunctor C 0).obj L
    have hdglobal : IsDualizable K := by
      apply (condensed_dualizable_iff_proetale_cover R S U K).mpr
      intro a
      let e := ((upperStar Λ (U.f a)).mapDerivedCategorySingleFunctor 0).app L
      have hr := dualizableRootOfSource Λ (U.X a) _ (hlocal a).1
      exact dualizableRootTransport Λ (U.X a) _
        (rootDualizable_of_iso _ _ e.symm hr)
    have hK := (integralHeart_local_duality_descent Λ S L U (-1) 0 hlocal).2
    let D := stratumModuleDual Λ S L
    let H := (derivedHom Λ S).obj (op K)
    have adjH : rootTensor K ⊣ H :=
      (derivedTensorHomAdjunction Λ K).ofNatIsoLeft (eqToIso (tensorRootEq Λ S K))
    have hDdef : D = H.obj (rootUnit (C := C)) :=
      congrArg H.obj (unitRootEq Λ S)
    have hdual := dualizableRootOfSource Λ S K hdglobal
    have hcon := dualConsequences (C := C) K D H (stratumModuleDualTensor Λ S L)
      (curriedTensor (CochainComplex C ℤ)) (complexTensorRootEq Λ S)
      adjH (tensorRootEq Λ S D) (eqToIso hDdef) hdual hK
    have hD := hcon.1
    change DerivedCategory.torAmplitudeIn C 0 1 (stratumModuleDual Λ S L) at hD
    let hAdd := adj.right_adjoint_additive
    refine ⟨hAdd, ?_, hD, hcon.2.2.1, hcon.2.2.2⟩
    obtain ⟨ed⟩ := hcon.2.1
    change (derivedHom Λ S).obj (op K) ≅ stratumModuleDualTensor Λ S L at ed
    let := hclosedExact
    have hji : Set.range i.base = (Set.range j.base)ᶜ := by
      simp only [hij, compl_compl]
    let hsupp := (closedSupportAdjunction Λ i j hji).rightAdjointUniq adj
    let hsuppD := Functor.rightDerivedFunctorNatIso hsupp
    let A := (openImmersionLowerShriek Λ v).obj L
    let AZ := (DerivedCategory.singleFunctor _ 0).obj A
    let eA := ((lowerStar Λ i).mapDerivedCategorySingleFunctor 0).app A
    obtain ⟨ci⟩ := closedHom_iso Λ i j hji AZ
    let ec : (derivedHom Λ X).obj (op ((DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar Λ i).obj A))) ≅
        (closedSupport Λ i j).rightDerivedFunctor ⋙ (derivedHom Λ Z).obj (op AZ) ⋙
          (lowerStar Λ i).mapDerivedCategory :=
      (derivedHom Λ X).mapIso eA.op ≪≫ ci
    have hqcv : QuasiCompact v :=
      ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    obtain ⟨ov⟩ := openHom_iso Λ v.closedComplement v v.range_closedComplement K
    let ev := ((openImmersionLowerShriek Λ v).mapDerivedCategorySingleFunctor 0).app L
    let eo : (derivedHom Λ Z).obj (op AZ) ≅
        (supportPullback Λ v).mapDerivedCategory ⋙ (derivedHom Λ S).obj (op K) ⋙
          (lowerStar Λ v).rightDerivedFunctor :=
      (derivedHom Λ Z).mapIso ev.op ≪≫ ov
    have hpush (Y W : Scheme.{u}) (f : Y ⟶ W) :
        Nonempty ((lowerStar Λ f).rightDerivedFunctor ⋙ stratumModuleDerivedSections Λ W ≅
          stratumModuleDerivedSections Λ Y) := by
      have : (lowerStar Λ f).PreservesKInjectiveComplexes :=
        (upperStarLowerStarAdjunction Λ f).preservesKInjectiveComplexes
      let er : (upperStar Λ f).obj (Mod.regular (condensedRingObj Λ W)) ≅
          Mod.regular (condensedRingObj Λ Y) :=
        (Functor.Monoidal.εIso (upperStar Λ f)).symm
      let ΓW : supportModules Λ W ⥤ Ab.{u + 1} :=
        preadditiveCoyoneda.obj (op (Mod.regular (condensedRingObj Λ W)))
      let ΓY : supportModules Λ Y ⥤ Ab.{u + 1} :=
        preadditiveCoyoneda.obj (op (Mod.regular (condensedRingObj Λ Y)))
      have eΓ : lowerStar Λ f ⋙ ΓW ≅ ΓY :=
        ((upperStarLowerStarAdjunction Λ f).preadditiveCoyonedaObjIso _).symm ≪≫
          preadditiveCoyoneda.mapIso er.op.symm
      exact ⟨Functor.rightDerivedFunctorCompIso' (lowerStar Λ f) ΓW eΓ⟩
    obtain ⟨esi⟩ := hpush Z X i
    obtain ⟨esv⟩ := hpush S Z v
    let esi' : (lowerStar Λ i).mapDerivedCategory ⋙ stratumModuleDerivedSections Λ X ≅
        stratumModuleDerivedSections Λ Z := Functor.isoWhiskerRight
      (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.symm
      (stratumModuleDerivedSections Λ X) ≪≫ esi
    let e : (derivedHom Λ X).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj ((lowerStar Λ i).obj A))) ⋙
          stratumModuleDerivedSections Λ X ≅
        (closedModuleSectionsWithSupport Λ i j).rightDerivedFunctor ⋙
          (upperStar Λ v).mapDerivedCategory ⋙ stratumModuleDualTensor Λ S L ⋙
            stratumModuleDerivedSections Λ S :=
      composeStratumSectionsIso
        (R := (closedSupport Λ i j).rightDerivedFunctor)
        (R' := (closedModuleSectionsWithSupport Λ i j).rightDerivedFunctor)
        (H₁ := (derivedHom Λ Z).obj (op AZ))
        (I := (lowerStar Λ i).mapDerivedCategory)
        (P := (supportPullback Λ v).mapDerivedCategory)
        (U := (upperStar Λ v).mapDerivedCategory)
        (H₂ := (derivedHom Λ S).obj (op K))
        (T := stratumModuleDualTensor Λ S L)
        (V := (lowerStar Λ v).rightDerivedFunctor)
        (Γ₀ := stratumModuleDerivedSections Λ X) (Γ₁ := stratumModuleDerivedSections Λ Z)
        (Γ₂ := stratumModuleDerivedSections Λ S) ec eo esi' esv hsuppD
        (Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ v)) ed
    exact ⟨e⟩

/-- Global derived Hom from a stratum extension is derived sections of the tensor of
its derived dual with restricted derived support. The dual has Tor amplitude [0,1],
and tensoring with it preserves small filtered degreewise colimits and countable
strict derived inverse limits, with their projection maps.
Source: blueprint det-lem-int-ext-formula, clause (2)
(blueprint: det-lem-int-ext-formula).

Proof: a finite constant integral model admits a local two-term resolution whose first
two terms are dualizable. Its derived cone is locally dualizable with Tor amplitude
[-1,0]. Dualizability descends over the cover, and exact monoidal pullback with cover-local
cohomology vanishing descends the Tor bound. Braided duality gives Tor amplitude
[0,1] for the dual. Uniqueness of adjoints identifies
internal Hom from L with tensor by this dual, which therefore preserves small limits.
The kernel support construction is right adjoint to exact closed pushforward and is
additive. Compare it with the canonical support adjunction. The closed and open internal
Hom formulas, together with the derived global-sections comparison for pushforward,
give the stated natural isomorphism. Localization of the monoidal K-flat model gives
a representative P and its natural tensor comparison. Tensor by a complex is a left
adjoint, hence preserves filtered degreewise colimits. Finally dual tensor is exact,
commutes with shifts and preserves countable products. Applying it to a strict-tower
Roos triangle and using the product comparison gives the specified projection maps
and the resulting distinguished derived-limit triangle. -/
theorem integral_stratum_hom_formula
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X Z S V : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] (v : S ⟶ Z) [IsOpenImmersion v]
    (j : V ⟶ X) [IsOpenImmersion j] (hij : Set.range j = (Set.range i)ᶜ)
    (L : pulledBackModuleObjects (integralCoefficientRing l E) S)
    (hL : IsConstantModelConstructible (integralCoefficientRing l E) S L)
    (hmodel : HasFiniteConstantLocalModel (integralCoefficientRing l E) S L) :
    ∃ (_ : (closedModuleSectionsWithSupport (integralCoefficientRing l E) i j).Additive),
      Nonempty
        ((derivedHom (integralCoefficientRing l E) X).obj
            (op ((DerivedCategory.singleFunctor _ 0).obj
              ((lowerStar (integralCoefficientRing l E) i).obj
                ((openImmersionLowerShriek (integralCoefficientRing l E) v).obj L)))) ⋙
              integralStratumDerivedSections l E X ≅
          (closedModuleSectionsWithSupport (integralCoefficientRing l E) i j).rightDerivedFunctor ⋙
            (upperStar (integralCoefficientRing l E) v).mapDerivedCategory ⋙
              integralStratumDualTensor l E S L ⋙
                integralStratumDerivedSections l E S) ∧
      DerivedCategory.torAmplitudeIn _ 0 1 (integralStratumDual l E S L) ∧
      (∃ P : CochainComplex.KFlat
          (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
            (condensedRingObj (integralCoefficientRing l E) S)),
        Nonempty (DerivedCategory.Q.obj P.obj ≅ integralStratumDual l E S L) ∧
        Nonempty (DerivedCategory.Q ⋙
            integralStratumDualTensor l E S L ≅
          (curriedTensor (CochainComplex
            (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
              (condensedRingObj (integralCoefficientRing l E) S)) ℤ)).obj P.obj ⋙
              DerivedCategory.Q) ∧
        ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I],
          PreservesColimitsOfShape I
            ((curriedTensor (CochainComplex
              (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
                (condensedRingObj (integralCoefficientRing l E) S)) ℤ)).obj P.obj)) ∧
      (∀ (B : ℕᵒᵖ ⥤ CochainComplex
          (pulledBackModuleObjects (integralCoefficientRing l E) S) ℤ)
        [HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n)))]
        [HasProduct (fun n : ℕ ↦
          (integralStratumDualTensor l E S L).obj
            (DerivedCategory.Q.obj (B.obj (op n))))]
        (A : integralDerived l E S)
        (p : A ⟶ ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n))))
        (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n)))) ⟶ A⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle
          (fun n : ℕ ↦ DerivedCategory.Q.map (B.map (homOfLE (Nat.le_succ n)).op)) A p δ →
        ∃ ε : (∏ᶜ (fun n : ℕ ↦
            (integralStratumDualTensor l E S L).obj (DerivedCategory.Q.obj (B.obj (op n))))) ⟶
          ((integralStratumDualTensor l E S L).obj A) ⟦(1 : ℤ)⟧,
          IsDerivedLimitTriangle
            (fun n : ℕ ↦
              (integralStratumDualTensor l E S L).map
                (DerivedCategory.Q.map (B.map (homOfLE (Nat.le_succ n)).op)))
            ((integralStratumDualTensor l E S L).obj A)
            (Pi.lift (fun n : ℕ ↦
              (integralStratumDualTensor l E S L).map
                (p ≫ Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (B.obj (op n))) n))) ε) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : TopologicalSpace.NoetherianSpace Z :=
    i.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace S :=
    v.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  exact genericStratumHomFormula (integralCoefficientRing l E) i v j hij L hL
    (integral_constantModel_localResolution l E S L hmodel)

end AlgebraicGeometry.ProEtale.CondensedRing
