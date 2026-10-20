/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.PointDerivedHomEvaluation
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Paper.ConstantCoefficientObjectsConstructible
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
import Sheaf.Paper.ProEtaleConstantModuleEncoding
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import WeilConjectures.ConstructibleSheaf.InternalHom
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.LinearAlgebra.FreeModule.PID
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingTriangleClosure
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Module.FinitePresentation
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.DerivedCategory.PerfectCohomologyAssembly
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.FiniteRingConstructibleSheafOrigin
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Paper.PointSectionsDerivedReduction
import Sheaf.Paper.PointSectionsFiniteness
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant

/-!
# Point sections and constant-sheaf reconstruction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
`sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md`, second sentence
(blueprint: lem-pod-point-sections-reconstruction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PointDerivedHom
namespace WeilConjectures

/-- Reconstruction for the specified ordinary tensor extension and its explicit adjunction.
The Boolean selects the finite or completed integral coefficient sheaf. The local
instance only supplies the additivity implied by that adjunction; it chooses no data.
Source: blueprint point-dualizing proof, second sentence
(blueprint: lem-pod-point-sections-reconstruction). -/
def pointSectionsReconstructionResult
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) (integral : Bool) :
    ∀ (L : ModuleCat.{u + 1} (coefficientRing.{u, u} l E n integral) ⥤
      PointDerivedHom.Modules.{u, u} k (coefficientSheaf.{u, u} k l E n integral))
    (_adj : L ⊣ sections.{u, u} k (coefficientSheaf.{u, u} k l E n integral)
      (coefficientMap.{u, u} k l E n integral))
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits (sections.{u, u} k (coefficientSheaf.{u, u} k l E n integral)
      (coefficientMap.{u, u} k l E n integral))]
    [PreservesFiniteColimits (sections.{u, u} k (coefficientSheaf.{u, u} k l E n integral)
      (coefficientMap.{u, u} k l E n integral))], Prop :=
  match integral with
  | false => fun L adj hLl hLc hRl hRc ↦
    letI := hLl
    letI := hLc
    letI := hRl
    letI := hRc
    letI := adj.left_adjoint_additive
    (∀ c : (DerivedCategory.pointFiniteCohomology
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))).FullSubcategory,
      IsIso (adj.mapDerivedCategoryAdjunction.unit.app c.obj) ∧
        intrinsicFiniteTorsionConstructible l E n hn (Spec (.of k))
          (L.mapDerivedCategory.obj c.obj)) ∧
    (∀ C : (Spec (.of k)).proEtaleDerivedCategory
        (Padic.coefficientExtensionRing l E n),
      intrinsicFiniteTorsionConstructible l E n hn (Spec (.of k)) C →
        IsIso (adj.mapDerivedCategoryAdjunction.counit.app C))
  | true => fun L adj hLl hLc hRl hRc ↦
    letI := hLl
    letI := hLc
    letI := hRl
    letI := hRc
    letI := adj.left_adjoint_additive
    (∀ c : DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))),
      (∃ s : Finset ℤ, (∀ i : ℤ, i ∉ s →
        IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionIntegers l E))) i).obj c)) ∧
        (∀ i : ℤ, Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
          ((DerivedCategory.homologyFunctor
            (ModuleCat.{u + 1} (ULift.{u + 1, u}
              (Padic.coefficientExtensionIntegers l E))) i).obj c))) →
        IsIso (adj.mapDerivedCategoryAdjunction.unit.app c) ∧
          sfIntegralConstructible l E (Spec (.of k)) (L.mapDerivedCategory.obj c) ∧
          ∃ (P : CochainComplex (ModuleCat.{u + 1}
              (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ) (a b : ℤ),
            P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
            (∀ i : ℤ, Module.Projective
              (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) (P.X i) ∧
              Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
                (P.X i)) ∧
            Nonempty (c ≅ DerivedCategory.Q.obj P) ∧
            sfIntegralConstructible l E (Spec (.of k))
              (L.mapDerivedCategory.obj (DerivedCategory.Q.obj P))) ∧
    (∀ C : sfIntegralConstructibleCategory l E (Spec (.of k)),
      IsIso (adj.mapDerivedCategoryAdjunction.counit.app C.obj))


private instance (priority := 2000) fixedDerivedSheaves (k : Type u) [Field k]
    (B : Sheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) :
    HasDerivedCategory (PointDerivedHom.Modules.{u, u} k B) := HasDerivedCategory.standard _

private def finiteSectionsEncoding
    (k A : Type u) [Field k] [CommRing A] :
    (proEtaleModuleEncoding (Spec (.of k)) A).functor ⋙
      (sheafSections (ProEt.topology (Spec (.of k)))
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj (op (finalObject k)) ≅
      sections.{u, u} k (constantRing.{u, u} k (.of (ULift.{u + 1, u} A))) (𝟙 _) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let F := (proEtaleModuleEncoding (Spec (.of k)) A).functor ⋙
      (sheafSections (ProEt.topology (Spec (.of k)))
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj (op (finalObject k))
    let G := sections.{u, u} k
      (constantRing.{u, u} k (.of (ULift.{u + 1, u} A))) (𝟙 _)
    exact (show F.obj M ≃ₗ[ULift.{u + 1, u} A] G.obj M from
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }).toModuleIso
  · intro M N f
    ext x
    rfl

private def finiteExtensionIso
    (k : Type u) [Field k] (A : Type u) [CommRing A]
    (L : ModuleCat.{u + 1} (ULift.{u + 1, u} A) ⥤
      PointDerivedHom.Modules.{u, u} k
        (constantRing.{u, u} k (.of (ULift.{u + 1, u} A))))
    (adj : L ⊣ sections.{u, u} k
      (constantRing.{u, u} k (.of (ULift.{u + 1, u} A))) (𝟙 _)) :
    L ≅ constantSheaf (ProEt.topology (Spec (.of k)))
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⋙
        (proEtaleModuleEncoding (Spec (.of k)) A).inverse := by
  let e := proEtaleModuleEncoding (Spec (.of k)) A
  let c := constantSheafAdj (ProEt.topology (Spec (.of k)))
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (ProEt.isTerminalMkId _)
  have a := c.comp e.symm.toAdjunction
  apply adj.leftAdjointUniq
  apply a.ofNatIsoRight
  exact finiteSectionsEncoding k A

private theorem finiteExtension_constructible
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Finite A]
    (L : ModuleCat.{u + 1} (ULift.{u + 1, u} A) ⥤
      PointDerivedHom.Modules.{u, u} k
        (constantRing.{u, u} k (.of (ULift.{u + 1, u} A))))
    (adj : L ⊣ sections.{u, u} k
      (constantRing.{u, u} k (.of (ULift.{u + 1, u} A))) (𝟙 _))
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) [Finite M] :
    IsConstructibleProEtaleModuleSheaf (Spec (.of k)) A (L.obj M) := by
  let T := Spec (.of k)
  let e := proEtaleModuleEncoding T A
  let c := constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  have : IsFiniteSheaf (c.obj M) := isFiniteSheaf_constantSheaf M
  have : IsLocallyConstantSheaf (c.obj M) :=
    (Sheaf.isConstant_of_iso _ (Iso.refl _)).isLocallyConstantSheaf
  have : IsFiniteLocallyConstantSheaf (c.obj M) := {}
  have : IsConstructibleSheaf (c.obj M) :=
    IsFiniteLocallyConstantSheaf.isConstructibleSheaf inferInstance
  apply (proEtaleModuleRestriction_constructible_iff T A _).mpr
  apply ProEtale.isConstructible_of_iso
    (F := (ProEtale.comparisonUpperStar _ T).obj (c.obj M))
    (G := e.functor.obj (L.obj M))
  · exact (ProEtale.comparisonUpperStarConstantSheafIso _ T).app M ≪≫
      (e.counitIso.app _).symm ≪≫
      e.functor.mapIso ((finiteExtensionIso k A L adj).app M).symm
  · exact ProEtale.isConstructible_comparisonUpperStar_obj _

private theorem etale_point_counit_isIso
    (k : Type u) [Field k] [IsAlgClosed k] (A : Type u) [CommRing A]
    (F : Sheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    IsIso ((constantSheafAdj (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) terminalIsTerminal).counit.app F) := by
  let J := (Spec (.of k)).smallEtaleTopology
  let U := forget (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  have hG : IsIso ((constantSheafAdj J (Type (u + 1)) terminalIsTerminal).counit.app
      ((sheafCompose J U).obj F)) :=
    (spec_algClosed_etale_sheaf_constant k ((sheafCompose J U).obj F)).1
  have : IsIso ((sheafCompose J U).map
      ((constantSheafAdj J (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        terminalIsTerminal).counit.app F)) := by
    rw [← constantSheafAdj_counit_w J U F terminalIsTerminal]
    infer_instance
  exact isIso_of_reflects_iso _ (sheafCompose J U)

private theorem finite_constructible_constant
    (k : Type u) [Field k] [IsAlgClosed k] (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules (Spec (.of k)) (proEtaleConstantRing (Spec (.of k)) A))
    (hF : IsConstructibleProEtaleModuleSheaf (Spec (.of k)) A F) :
    ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} A), Finite M ∧
      Nonempty (F ≅ (constantSheaf (ProEt.topology (Spec (.of k)))
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⋙
          (proEtaleModuleEncoding (Spec (.of k)) A).inverse).obj M) := by
  let T := Spec (.of k)
  let e := proEtaleModuleEncoding T A
  have h := (proEtaleModuleRestriction_constructible_iff T A F).mp hF
  obtain ⟨G, hG, ⟨iG⟩⟩ :=
    ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _ h
  have hε := etale_point_counit_isIso k A G
  let a := constantSheafAdj T.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) terminalIsTerminal
  let M := G.obj.obj (op (⊤_ T.Etale))
  let i : (constantSheaf T.smallEtaleTopology _).obj M ≅ G := asIso (a.counit.app G)
  have : IsConstructibleSheaf ((constantSheaf T.smallEtaleTopology _).obj M) :=
    IsConstructibleSheaf.of_iso i.symm
  have : IsFiniteSheaf ((constantSheaf T.smallEtaleTopology _).obj M) :=
    IsConstructibleSheaf.isFiniteSheaf inferInstance
  have : Module.Finite (ULift.{u + 1, u} A) M :=
    moduleFinite_of_isFiniteSheaf_constantSheaf (Y := T) M
  refine ⟨M, Module.finite_of_finite (ULift.{u + 1, u} A), ⟨?_⟩⟩
  exact (e.unitIso.app F) ≪≫ e.inverse.mapIso
    (iG.symm ≪≫ (ProEtale.comparisonUpperStar _ T).mapIso i.symm ≪≫
      (ProEtale.comparisonUpperStarConstantSheafIso _ T).app M)


private theorem finite_constructible_isZero
    (k : Type u) [Field k] [IsAlgClosed k] (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules (Spec (.of k)) (proEtaleConstantRing (Spec (.of k)) A))
    (hF : IsConstructibleProEtaleModuleSheaf (Spec (.of k)) A F)
    (hzero : IsZero ((sections.{u, u} k
      (constantRing.{u, u} k (.of (ULift.{u + 1, u} A))) (𝟙 _)).obj F)) :
    IsZero F := by
  obtain ⟨M, _, ⟨e⟩⟩ := finite_constructible_constant k A F hF
  let enc := proEtaleModuleEncoding (Spec (.of k)) A
  let c := constantSheafAdj (ProEt.topology (Spec (.of k)))
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (ProEt.isTerminalMkId _)
  let a := (c.comp enc.symm.toAdjunction).ofNatIsoRight (finiteSectionsEncoding k A)
  have hz := hzero.of_iso ((sections.{u, u} k
    (constantRing.{u, u} k (.of (ULift.{u + 1, u} A))) (𝟙 _)).mapIso e).symm
  let Lc := constantSheaf (ProEt.topology (Spec (.of k)))
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⋙ enc.inverse
  have hz' := Lc.map_isZero hz
  apply IsZero.of_iso _ e
  apply (IsZero.iff_id_eq_zero _).mpr
  calc
    _ = Lc.map (a.unit.app M) ≫ a.counit.app (Lc.obj M) :=
      (a.left_triangle_components M).symm
    _ = 0 := by rw [hz'.eq_of_tgt (Lc.map (a.unit.app M)) 0, zero_comp]

private theorem derived_isZero_of_homology
    {V W : Type*} [Category V] [Category W] [Abelian V] [Abelian W]
    [HasDerivedCategory V] [HasDerivedCategory W]
    (G : V ⥤ W) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory V)
    (hK : ∀ i, IsZero (G.obj ((DerivedCategory.homologyFunctor _ i).obj K)) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K))
    (hz : IsZero (G.mapDerivedCategory.obj K)) : IsZero K := by
  apply (DerivedCategory.isZero_iff K).mpr
  intro i
  apply hK i
  exact ((DerivedCategory.homologyFunctor _ i).map_isZero hz).of_iso
    ((G.mapDerivedCategoryHomologyFunctorIso i).app K)

private def integralSectionsIso (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    sections.{u, u} k (coefficientSheaf.{u, u} k l E n true)
      (coefficientMap.{u, u} k l E n true) ≅ pointIntegralSections l E k := by
  exact Iso.refl _

private def finiteSectionsIso (k A : Type u) [Field k] [CommRing A] :
    sections.{u, u} k (constantRing.{u, u} k (.of (ULift.{u + 1, u} A))) (𝟙 _) ≅
      pointFiniteSections k A := by
  exact Iso.refl _

private theorem pointTensorReduction_isZero
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (K : DerivedCategory (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))) (hK : IsZero K) :
    IsZero ((pointReductionModuleTensor l E n).obj K) := by
  let N := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
  obtain ⟨c, ht⟩ := (DerivedCategory.exists_derivedTensor_second_factor_functor
    (pointReductionQuotient l E n)).2.choose_spec.choose_spec.2.1 N
  let : (pointReductionModuleTensor l E n).CommShift ℤ := c
  have : (pointReductionModuleTensor l E n).IsTriangulated := ht
  exact (pointReductionModuleTensor l E n).map_isZero hK

private theorem integral_constructible_isZero
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (hz : IsZero ((pointIntegralSections l E D.k).mapDerivedCategory.obj K.obj)) :
    IsZero K.obj := by
  have hred (n : ℕ) : IsZero
      ((scalarReductionDerivedExtension.{u, u} l E (Spec (.of D.k)) n).obj K.obj) := by
    let A := Padic.coefficientExtensionRing l E (n + 1)
    have : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    obtain ⟨e⟩ := (point_sections_derived_reduction D l E hl n).1
    have ht := pointTensorReduction_isZero l E n _ hz
    have hs := ht.of_iso (e.app K).symm
    apply derived_isZero_of_homology (pointFiniteSections D.k A) _ ?_ hs
    intro i hi
    apply finite_constructible_isZero D.k A _ ((K.property.2.choose_spec.choose_spec.2 n).1.2 i)
    exact hi.of_iso ((finiteSectionsIso D.k A).app _)
  obtain ⟨hp, δ, hδ⟩ := K.property.1
  let := hp
  have hres (n : ℕ) : IsZero ((sfDerivedReductionRestricted l E (Spec (.of D.k)) n).obj
      K.obj) := by
    have := (scalarReductionRestriction_exact.{u, u} l E (Spec (.of D.k)) n).1
    have := (scalarReductionRestriction_exact.{u, u} l E (Spec (.of D.k)) n).2
    change IsZero
      ((scalarReductionRestriction.{u, u} l E (Spec (.of D.k)) n).mapDerivedCategory.obj _)
    let F := (scalarReductionRestriction.{u, u} l E (Spec (.of D.k)) n).mapDerivedCategory
    exact F.map_isZero (hred n)
  have hpzero : IsZero (∏ᶜ fun n ↦
      (sfDerivedReductionRestricted l E (Spec (.of D.k)) n).obj K.obj) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Pi.hom_ext
    intro n
    exact (hres n).eq_of_tgt _ _
  exact (Pretriangulated.Triangle.isZero₁_of_isZero₂₃ _ hδ hpzero hpzero)

private theorem unitHom_final_bijective
    (k : Type u) [Field k]
    (B : Sheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
    (V : PointDerivedHom.Modules.{u, u} k B) :
    Function.Bijective (fun f : SheafOfModules.unit (ring.{u, u} k B) ⟶ V ↦
      f.val.app (op (finalObject k)) (1 : B.obj.obj (op (finalObject k)))) := by
  constructor
  · intro f g h
    apply V.unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    have hf := (V.unitHomEquiv f).property (toFinal k U.unop).op
    have hg := (V.unitHomEquiv g).property (toFinal k U.unop).op
    exact hf.symm.trans ((congrArg (V.val.map (toFinal k U.unop).op) h).trans hg)
  · intro x
    let t : V.sections := PresheafOfModules.sectionsMk
      (fun U ↦ V.val.map (toFinal k U.unop).op x) (by
        intro U W i
        change V.val.presheaf.map i
          (V.val.presheaf.map (toFinal k U.unop).op x) =
            V.val.presheaf.map (toFinal k W.unop).op x
        have hw : (toFinal k U.unop).op ≫ i = (toFinal k W.unop).op := by
          apply Quiver.Hom.unop_inj
          apply MorphismProperty.Over.Hom.ext
          change i.unop.left ≫ (unop U).hom = (unop W).hom
          exact MorphismProperty.Over.w i.unop
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hw])
    refine ⟨V.unitHomEquiv.symm t, ?_⟩
    have ht := congrArg (fun z : V.sections ↦ z.val (op (finalObject k)))
      (V.unitHomEquiv.apply_symm_apply t)
    have hid : toFinal k (finalObject k) = 𝟙 _ := by
      apply MorphismProperty.Over.Hom.ext
      rfl
    change ((V.unitHomEquiv.symm t).val.app (op (finalObject k)))
      (1 : B.obj.obj (op (finalObject k))) = x
    change ((V.unitHomEquiv.symm t).val.app (op (finalObject k)))
      (1 : B.obj.obj (op (finalObject k))) =
        V.val.map (toFinal k (finalObject k)).op x at ht
    change ((V.unitHomEquiv.symm t).val.app (op (finalObject k)))
      (1 : B.obj.obj (op (finalObject k))) =
        V.val.presheaf.map (toFinal k (finalObject k)).op x at ht
    rw [hid, op_id] at ht
    exact ht.trans (congrArg (fun f ↦ f x) (V.val.presheaf.map_id _))

private theorem moduleHom_one_bijective
    (R : Type (u + 1)) [CommRing R] (M : ModuleCat.{u + 1} R) :
    Function.Bijective (fun f : ModuleCat.of R R ⟶ M ↦ f.hom 1) := by
  constructor
  · intro f g h
    apply ModuleCat.hom_ext
    exact (LinearMap.ringLmapEquivSelf R R M).injective h
  · intro x
    exact ⟨ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf R R M).symm x), by simp⟩

private theorem adjunction_rankOne_iso
    (k : Type u) [Field k] (R : CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
    (α : constantRing.{u, u} k R ⟶ B)
    (L : ModuleCat.{u + 1} R ⥤ PointDerivedHom.Modules.{u, u} k B)
    (adj : L ⊣ sections.{u, u} k B α)
    : Nonempty (L.obj (ModuleCat.of R R) ≅ SheafOfModules.unit (ring.{u, u} k B)) := by
  let f := coefficientSections.{u, u} k B α
  let h := (adj.homEquiv (ModuleCat.of R R) _).symm f
  have hh : IsIso h := by
    apply isIso_of_coyoneda_map_bijective
    intro V
    let ev := fun g : ModuleCat.of R R ⟶ (sections.{u, u} k B α).obj V ↦ g.hom 1
    have he (t : SheafOfModules.unit (ring.{u, u} k B) ⟶ V) :
        ev (adj.homEquiv _ V (h ≫ t)) =
          t.val.app (op (finalObject k)) (1 : B.obj.obj (op (finalObject k))) := by
      rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
      change t.val.app (op (finalObject k))
        (scalar.{u, u} k B α (op (finalObject k)) 1) = _
      rw [map_one]
    constructor
    · intro t t' htt
      apply (unitHom_final_bijective k B V).1
      exact (he t).symm.trans
        ((congrArg (fun q ↦ ev (adj.homEquiv _ V q)) htt).trans (he t'))
    · intro q
      obtain ⟨t, ht⟩ := (unitHom_final_bijective k B V).2 (ev (adj.homEquiv _ V q))
      refine ⟨t, (adj.homEquiv _ V).injective ?_⟩
      apply (moduleHom_one_bijective R ((sections.{u, u} k B α).obj V)).1
      exact (he t).trans ht
  exact ⟨asIso h⟩

private theorem adjunction_unit_rankOne_isIso
    (k : Type u) [Field k] (R : CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
    (α : constantRing.{u, u} k R ⟶ B)
    (L : ModuleCat.{u + 1} R ⥤ PointDerivedHom.Modules.{u, u} k B)
    (adj : L ⊣ sections.{u, u} k B α)
    (hsections : Function.Bijective (scalar.{u, u} k B α (op (finalObject k)))) :
    IsIso (adj.unit.app (ModuleCat.of R R)) := by
  let f := coefficientSections.{u, u} k B α
  let h := (adj.homEquiv (ModuleCat.of R R) _).symm f
  have hh : IsIso h := by
    apply isIso_of_coyoneda_map_bijective
    intro V
    let ev := fun g : ModuleCat.of R R ⟶ (sections.{u, u} k B α).obj V ↦ g.hom 1
    have he (t : SheafOfModules.unit (ring.{u, u} k B) ⟶ V) :
        ev (adj.homEquiv _ V (h ≫ t)) =
          t.val.app (op (finalObject k)) (1 : B.obj.obj (op (finalObject k))) := by
      rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
      change t.val.app (op (finalObject k))
        (scalar.{u, u} k B α (op (finalObject k)) 1) = _
      rw [map_one]
    constructor
    · intro t t' htt
      apply (unitHom_final_bijective k B V).1
      exact (he t).symm.trans
        ((congrArg (fun q ↦ ev (adj.homEquiv _ V q)) htt).trans (he t'))
    · intro q
      obtain ⟨t, ht⟩ := (unitHom_final_bijective k B V).2 (ev (adj.homEquiv _ V q))
      refine ⟨t, (adj.homEquiv _ V).injective ?_⟩
      apply (moduleHom_one_bijective R ((sections.{u, u} k B α).obj V)).1
      exact (he t).trans ht
  have hf : IsIso f := (ConcreteCategory.isIso_iff_bijective f).2 hsections
  have heq : adj.unit.app (ModuleCat.of R R) ≫
      (sections.{u, u} k B α).map h = f := by
    exact (adj.homEquiv _ _).apply_symm_apply f
  exact IsIso.of_isIso_fac_right heq

private theorem isoApp_of_iso
    {C V : Type*} [Category C] [Category V] {F G : C ⥤ V}
    (η : F ⟶ G) {M N : C} (e : M ≅ N) [IsIso (η.app M)] : IsIso (η.app N) := by
  exact IsIso.of_isIso_fac_left (η.naturality e.hom)

private theorem isoApp_finitePresentation
    (R : Type (u + 1)) [CommRing R]
    {V : Type*} [Category V]
    {F G : ModuleCat.{u + 1} R ⥤ V}
    [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (η : F ⟶ G) (hR : IsIso (η.app (ModuleCat.of R R)))
    (M : ModuleCat.{u + 1} R) [Module.FinitePresentation R M] :
    IsIso (η.app M) := by
  have hfree (n : ℕ) : IsIso (η.app (ModuleCat.of R (Fin n → R))) := by
    let X := fun _ : Fin n ↦ ModuleCat.of R R
    have : ∀ j : Discrete (Fin n),
        IsIso ((Functor.whiskerLeft (Discrete.functor X) η).app j) := fun _ ↦ hR
    have : IsIso (Functor.whiskerLeft (Discrete.functor X) η) :=
      NatIso.isIso_of_isIso_app _
    have : IsIso (η.app (⨁ X)) :=
      isIso_app_coconePt_of_preservesColimit (Discrete.functor X) η
        (biproduct.bicone X).toCocone (biproduct.isColimit X)
    exact isoApp_of_iso η (ModuleCat.biproductIsoPi X)
  obtain ⟨n, m, π, f, hπ, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  let S : ShortComplex (ModuleCat.{u + 1} R) :=
    ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom π)
      (ModuleCat.hom_ext (LinearMap.ext hfg.apply_apply_eq_zero))
  have hS : S.Exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hfg
  have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 hπ
  have : ∀ j : WalkingParallelPair,
      IsIso ((Functor.whiskerLeft (parallelPair S.f 0) η).app j) := by
    intro j
    cases j
    · exact hfree m
    · exact hfree n
  have : IsIso (Functor.whiskerLeft (parallelPair S.f 0) η) :=
    NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit (parallelPair S.f 0) η
    (CokernelCofork.ofπ S.g S.zero) hS.gIsCokernel

private theorem adjunction_unit_complex_quasiIso
    (R : Type (u + 1)) [CommRing R]
    {V : Type*} [Category V] [Abelian V]
    (L : ModuleCat.{u + 1} R ⥤ V) (G : V ⥤ ModuleCat.{u + 1} R)
    [L.Additive] [G.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : L ⊣ G) (C : CochainComplex (ModuleCat.{u + 1} R) ℤ)
    (hC : ∀ i : ℤ, IsIso (adj.unit.app (C.homology i))) :
    QuasiIso ((adj.mapHomologicalComplex (.up ℤ)).unit.app C) := by
  constructor
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have he : HomologicalComplex.homologyMap
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app C) i =
      ((C.sc i).mapHomologyIso (𝟭 _)).hom ≫
        adj.unit.app (C.homology i) ≫ ((C.sc i).mapHomologyIso (L ⋙ G)).inv := by
    exact ShortComplex.homologyMap_mapNatTrans (C.sc i) adj.unit
  rw [he]
  have := hC i
  infer_instance

private theorem counit_iso_of_unit_iso
    {C V : Type*} [Category C] [Category V] {L : C ⥤ V} {G : V ⥤ C}
    (adj : L ⊣ G) (M : C) [IsIso (adj.unit.app M)] :
    IsIso (adj.counit.app (L.obj M)) := by
  exact IsIso.of_isIso_fac_left (adj.left_triangle_components M)

private theorem finite_counit_isIso
    (k : Type u) [Field k] [IsAlgClosed k] (A : Type u) [CommRing A] [Finite A]
    (L : ModuleCat.{u + 1} (ULift.{u + 1, u} A) ⥤
      PointDerivedHom.Modules.{u, u} k
        (constantRing.{u, u} k (.of (ULift.{u + 1, u} A))))
    (adj : L ⊣ sections.{u, u} k
      (constantRing.{u, u} k (.of (ULift.{u + 1, u} A))) (𝟙 _))
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits (sections.{u, u} k
      (constantRing.{u, u} k (.of (ULift.{u + 1, u} A))) (𝟙 _))]
    [PreservesFiniteColimits (sections.{u, u} k
      (constantRing.{u, u} k (.of (ULift.{u + 1, u} A))) (𝟙 _))]
    (hsections : Function.Bijective (scalar.{u, u} k
      (constantRing.{u, u} k (.of (ULift.{u + 1, u} A))) (𝟙 _) (op (finalObject k))))
    (F : proEtaleRingModules (Spec (.of k)) (proEtaleConstantRing (Spec (.of k)) A))
    (hF : IsConstructibleProEtaleModuleSheaf (Spec (.of k)) A F) :
    IsIso (adj.counit.app F) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := finite_constructible_constant k A F hF
  let := hM
  let e' : F ≅ L.obj M := e ≪≫ ((finiteExtensionIso k A L adj).app M).symm
  have : Module.FinitePresentation (ULift.{u + 1, u} A) M :=
    Module.finitePresentation_of_finite _ _
  have : IsIso (adj.unit.app M) := isoApp_finitePresentation _ adj.unit
    (adjunction_unit_rankOne_isIso k _ _ _ L adj hsections) M
  have := counit_iso_of_unit_iso adj M
  exact isoApp_of_iso adj.counit e'.symm

private theorem adjunction_counit_derived_isIso
    (R : Type (u + 1)) [CommRing R]
    {V : Type*} [Category V] [Abelian V] [HasDerivedCategory V]
    [Abelian.HasKInjectiveResolutions V]
    (L : ModuleCat.{u + 1} R ⥤ V) (G : V ⥤ ModuleCat.{u + 1} R)
    [L.Additive] [G.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : L ⊣ G) (K : DerivedCategory V)
    (hK : ∀ i : ℤ, IsIso (adj.counit.app ((DerivedCategory.homologyFunctor V i).obj K))) :
    IsIso (adj.mapDerivedCategoryAdjunction.counit.app K) := by
  let P := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  have hP (i : ℤ) : IsIso (adj.counit.app (P.homology i)) := by
    have eH : P.homology i ≅ (DerivedCategory.homologyFunctor V i).obj K :=
      ((DerivedCategory.homologyFunctorFactors V i).app P).symm ≪≫
        (DerivedCategory.homologyFunctor V i).mapIso e
    have := hK i
    exact isoApp_of_iso adj.counit eH.symm
  have hq : QuasiIso ((adj.mapHomologicalComplex (.up ℤ)).counit.app P) := by
    constructor
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have he : HomologicalComplex.homologyMap
        ((adj.mapHomologicalComplex (.up ℤ)).counit.app P) i =
        ((P.sc i).mapHomologyIso (G ⋙ L)).hom ≫
          adj.counit.app (P.homology i) ≫ ((P.sc i).mapHomologyIso (𝟭 _)).inv :=
      ShortComplex.homologyMap_mapNatTrans (P.sc i) adj.counit
    rw [he]
    have := hP i
    infer_instance
  have hQ : IsIso (DerivedCategory.Q.map
      ((adj.mapHomologicalComplex (.up ℤ)).counit.app P)) := inferInstance
  have heq := adj.mapDerivedCategoryAdjunction_counit_app_Qh_obj
    ((HomotopyCategory.quotient V (.up ℤ)).obj P)
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient] at heq
  have hQh : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient V (.up ℤ)).map
        ((adj.mapHomologicalComplex (.up ℤ)).counit.app P))) := hQ
  have : IsIso (adj.mapDerivedCategoryAdjunction.counit.app (DerivedCategory.Q.obj P)) := by
    change IsIso (adj.mapDerivedCategoryAdjunction.counit.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient V (.up ℤ)).obj P)))
    rw [heq]
    infer_instance
  exact isoApp_of_iso adj.mapDerivedCategoryAdjunction.counit e

private theorem perfect_single_projective
    (R : Type (u + 1)) [CommRing R]
    (M : ModuleCat.{u + 1} R) [Module.Projective R M] [Module.Finite R M] :
    DerivedCategory.IsPerfectRingComplex ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let P := (HomologicalComplex.single (ModuleCat.{u + 1} R) (.up ℤ) 0).obj M
  refine ⟨P, 0, 0, inferInstance, inferInstance, ?_, ⟨Iso.refl _⟩⟩
  intro i
  by_cases hi : i = 0
  · subst i
    change Module.Projective R M ∧ Module.Finite R M
    exact ⟨inferInstance, inferInstance⟩
  · have : Subsingleton (P.X i) := ModuleCat.isZero_iff_subsingleton.mp
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)
    exact ⟨inferInstance, inferInstance⟩

private theorem perfect_single_finite_pid
    (R : Type (u + 1)) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] :
    DerivedCategory.IsPerfectRingComplex ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  let K := LinearMap.ker π
  let S : ShortComplex (ModuleCat.{u + 1} R) :=
    ShortComplex.mk (ModuleCat.ofHom K.subtype) (ModuleCat.ofHom π)
      (by ext x; exact x.property)
  have hS : S.ShortExact := by
    have : Mono S.f := (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
    have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 hπ
    exact ⟨(ShortComplex.moduleCat_exact_iff_range_eq_ker S).2 (by simp [S, K])⟩
  have hK := perfect_single_projective R (ModuleCat.of R K)
  have hF := perfect_single_projective R (ModuleCat.of R (Fin n → R))
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hK
  have := P.isStrictlyGE_shift a 1 (a - 1) (by omega)
  have := P.isStrictlyLE_shift b 1 (b - 1) (by omega)
  have hKs : DerivedCategory.IsPerfectRingComplex
      (((DerivedCategory.singleFunctor (ModuleCat.{u + 1} R) 0).obj
        (ModuleCat.of R K))⟦(1 : ℤ)⟧) :=
    ⟨P⟦(1 : ℤ)⟧, a - 1, b - 1, inferInstance, inferInstance,
      fun i ↦ hP (i + 1), ⟨(shiftFunctor _ 1).mapIso e ≪≫
        ((DerivedCategory.Q.commShiftIso 1).app P).symm⟩⟩
  exact DerivedCategory.isPerfectRingComplex_obj₂_of_distTriang
    hS.singleTriangle.rotate
    (CategoryTheory.Pretriangulated.rot_of_distTriang _ hS.singleTriangle_distinguished) hF hKs


private theorem perfect_bounded_finite_pid
    (R : Type (u + 1)) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (c : DerivedCategory (ModuleCat.{u + 1} R))
    (s : Finset ℤ)
    (hs : ∀ i : ℤ, i ∉ s → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj c))
    (hc : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj c)) :
    DerivedCategory.IsPerfectRingComplex c := by
  apply DerivedCategory.isPerfectRingComplex_of_perfect_cohomology c
  · obtain ⟨a, ha⟩ := s.finite_toSet.bddBelow
    obtain ⟨b, hb⟩ := s.finite_toSet.bddAbove
    refine ⟨a, b, fun i hi ↦ hs i ?_⟩
    intro his
    rcases hi with hi | hi
    · exact (not_le_of_gt hi) (ha his)
    · exact (not_le_of_gt hi) (hb his)
  · intro i
    have := hc i
    exact perfect_single_finite_pid R _

private theorem triangulated_single_finite_pid
    (R : Type (u + 1)) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (Q : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} R)))
    [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]
    (hR : Q ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of R R)))
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] :
    Q ((DerivedCategory.singleFunctor _ 0).obj M) := by
  classical
  let H := DerivedCategory.singleFunctor (ModuleCat.{u + 1} R) 0
  have hfree (N : ModuleCat.{u + 1} R) [Module.Free R N] [Module.Finite R N] :
      Q (H.obj N) := by
    let b := Module.Free.chooseBasis R N
    let X := fun _ : Module.Free.ChooseBasisIndex R N ↦ ModuleCat.of R R
    have hX : (Q.inverseImage H) (ModuleCat.of R (∀ j, X j)) := by
      apply (Q.inverseImage H).prop_of_isLimit_fan
        (ModuleCat.HasLimit.productLimitCone.{u + 1, u + 1, u + 1} X).isLimit
      intro j
      exact hR
    exact Q.prop_of_iso (H.mapIso b.equivFun.toModuleIso).symm hX
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  let K := LinearMap.ker π
  let S : ShortComplex (ModuleCat.{u + 1} R) :=
    ShortComplex.mk (ModuleCat.ofHom K.subtype) (ModuleCat.ofHom π)
      (by ext x; exact x.property)
  have hS : S.ShortExact := by
    have : Mono S.f := (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
    have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 hπ
    exact ⟨(ShortComplex.moduleCat_exact_iff_range_eq_ker S).2 (by simp [S, K])⟩
  have hK := hfree (ModuleCat.of R K)
  have hF := hfree (ModuleCat.of R (Fin n → R))
  exact Q.ext_of_isTriangulatedClosed₃ hS.singleTriangle hS.singleTriangle_distinguished hK hF

private def moduleQSmall (R : Type (u + 1)) [CommRing R] :=
  @DerivedCategory.Q.{u + 1} (ModuleCat.{u + 1} R) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)

private def moduleHomologySmall (R : Type (u + 1)) [CommRing R] (i : ℤ) :=
  @DerivedCategory.homologyFunctor.{u + 1} (ModuleCat.{u + 1} R) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _) i

private def moduleHomologyShrinkIso
    (R : Type (u + 1)) [CommRing R] (i : ℤ) :
    DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i ≅
      (ShrinkHoms.equivalence.{u + 1}
        (DerivedCategory (ModuleCat.{u + 1} R))).functor ⋙ moduleHomologySmall R i := by
  let Q := DerivedCategory.Q (C := ModuleCat.{u + 1} R)
  let W := HomologicalComplex.quasiIso (ModuleCat.{u + 1} R) (.up ℤ)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} R) (.up ℤ) i
  let F := (ShrinkHoms.equivalence.{u + 1}
    (DerivedCategory (ModuleCat.{u + 1} R))).functor ⋙ moduleHomologySmall R i
  letI : Localization.Lifting Q W H F :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      @DerivedCategory.homologyFunctorFactors.{u + 1} (ModuleCat.{u + 1} R) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _) i⟩
  letI : Localization.Lifting Q W H
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i) :=
    ⟨DerivedCategory.homologyFunctorFactors _ i⟩
  exact Localization.liftNatIso Q W H H _ F (Iso.refl _)

private theorem adjunction_unit_derived_isIso
    (k : Type u) [Field k] (R : CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
    (α : constantRing.{u, u} k R ⟶ B)
    (L : ModuleCat.{u + 1} R ⥤ PointDerivedHom.Modules.{u, u} k B)
    (adj : L ⊣ sections.{u, u} k B α)
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits (sections.{u, u} k B α)]
    [PreservesFiniteColimits (sections.{u, u} k B α)]
    (hsections : Function.Bijective (scalar.{u, u} k B α (op (finalObject k))))
    (c : DerivedCategory (ModuleCat.{u + 1} R))
    (hc : ∀ i : ℤ, Module.FinitePresentation R
      ((DerivedCategory.homologyFunctor.{u + 2} (ModuleCat.{u + 1} R) i).obj c)) :
    letI := adj.left_adjoint_additive
    IsIso (adj.mapDerivedCategoryAdjunction.unit.app c) := by
  let := adj.left_adjoint_additive
  let C := DerivedCategory.Q.{u + 2}.objPreimage c
  let e := DerivedCategory.Q.{u + 2}.objObjPreimageIso c
  have hC (i : ℤ) : IsIso (adj.unit.app (C.homology i)) := by
    let eH : C.homology i ≅
        (DerivedCategory.homologyFunctor.{u + 2} (ModuleCat.{u + 1} R) i).obj c :=
      ((DerivedCategory.homologyFunctorFactors _ i).app C).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso e
    have : Module.FinitePresentation R (C.homology i) :=
      Module.FinitePresentation.of_equiv eH.toLinearEquiv.symm
    exact isoApp_finitePresentation R adj.unit
      (adjunction_unit_rankOne_isIso k R B α L adj hsections) _
  have := adjunction_unit_complex_quasiIso R L (sections.{u, u} k B α) adj C hC
  have hQ : IsIso (DerivedCategory.Q.map
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app C)) := inferInstance
  have heq := adj.mapDerivedCategoryAdjunction_unit_app_fac
    ((HomotopyCategory.quotient _ (.up ℤ)).obj C)
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at heq
  have hQh : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((adj.mapHomologicalComplex (.up ℤ)).unit.app C))) := hQ
  have : IsIso (adj.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Q.obj C)) :=
    IsIso.of_isIso_fac_right heq
  exact isoApp_of_iso adj.mapDerivedCategoryAdjunction.unit e

/--
The extension-of-scalars/sections reconstruction at the algebraically closed point.
The extension functor is fixed on objects and morphisms to
`B ⊗_underline R underline(-)`. The assumed explicit abelian adjunction
records both pure-tensor formulas. Its canonical termwise derived adjunction,
not an independently chosen derived adjunction, supplies the unit and counit.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
`sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md`, second sentence
(blueprint: lem-pod-point-sections-reconstruction).

Proof (the eight steps recorded by the node). (1) On modules, use the pure
tensor formulas from `def-pur-sheaf-tensor-product` and
`def-weil-proetale-locally-constant-sheaf`; balancing and sheafification make
the formulas well-defined, and the triangle identities descend through the
exact derived factorizations of `lem-weil-pbc-exact-functor-derived-factorization`.
(2) At finite level, `lem-weil-l-adic-extension-integers-dvr` gives finite
coefficient rings. Finite presentations and
`lem-weil-proetale-constant-sheaf-stalk` prove the unit and finite torsion
constructibility for each finite module, hence for bounded finite cohomology.
(3) The finite constructible comparison nodes
`lem-weil-pbc-finite-ring-constructible-sheaf-origin`,
`lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant`, and
`prop-weil-pbc-site-comparison-finite-level` identify each target with its
constant sections, so evaluation is the finite counit.
(4) Exactness and `lem-sp-exact-functor-preserves-homology` identify the
cohomology of termwise extension and sections; the cohomology criterion
`lem-weil-pbc-unbounded-derived-iso-cohomology` upgrades the module maps to
the finite derived unit and the constructible finite counit.
(5) For integral coefficients, the DVR/PID and finite-free-resolution lemmas
`lem-weil-l-adic-extension-integers-dvr`, `lem-weil-pbc-pid-noetherian-normal`,
`lem-weil-pbc-finite-free-resolution-noetherian`, and
`lem-sc-dvr-fg-torsionfree-free`, followed by
`lem-sf-perfect-cohomology-assembly`, supply the bounded finite-projective
representative required for every bounded finitely generated complex.
(6) Apply `lem-weil-pbc-integral-stratified-perfect-characterization` on the
single point, using `lem-weil-pbc-independent-bounded-flat-kflat` and the
integral constructibility definition, to show that extension of this model is
constructible and that its unit is invertible on projective summands.
(7) For a constructible integral target, take the counit cone. Exact sections
(`lem-weil-point-proetale-sections-exact`), the comparison
`lem-pod-point-sections-derived-reduction`, finite reconstruction, and the
derived-completeness triangle force the cone to vanish, giving the counit on
`sfIntegralConstructibleCategory`.
(8) The chain-level pure-generator formulas are natural; localization and
inverses of quasi-isomorphisms preserve these equations, so both derived
units and counits are natural in their arguments.
-/
theorem pointSectionsReconstruction
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) (integral : Bool)
    (L : ModuleCat.{u + 1} (coefficientRing.{u, u} l E n integral) ⥤
      PointDerivedHom.Modules.{u, u} D.k (coefficientSheaf.{u, u} D.k l E n integral))
    (hobj : ∀ M : ModuleCat.{u + 1} (coefficientRing.{u, u} l E n integral),
      L.obj M = extensionObject.{u, u} D.k (coefficientSheaf.{u, u} D.k l E n integral)
        (coefficientMap.{u, u} D.k l E n integral) M)
    (hmap : ∀ (M N : ModuleCat.{u + 1} (coefficientRing.{u, u} l E n integral))
      (f : M ⟶ N), L.map f = eqToHom (hobj M) ≫
        extensionMorphism.{u, u} D.k (coefficientSheaf.{u, u} D.k l E n integral)
          (coefficientMap.{u, u} D.k l E n integral) f ≫ eqToHom (hobj N).symm)
    (adj : L ⊣ sections.{u, u} D.k (coefficientSheaf.{u, u} D.k l E n integral)
      (coefficientMap.{u, u} D.k l E n integral))
    (hexplicit : ExplicitAdjunction.{u, u} D.k
      (coefficientSheaf.{u, u} D.k l E n integral)
      (coefficientMap.{u, u} D.k l E n integral) L hobj adj)
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits (sections.{u, u} D.k (coefficientSheaf.{u, u} D.k l E n integral)
      (coefficientMap.{u, u} D.k l E n integral))]
    [PreservesFiniteColimits (sections.{u, u} D.k (coefficientSheaf.{u, u} D.k l E n integral)
      (coefficientMap.{u, u} D.k l E n integral))]
    (hsections : Function.Bijective (scalar.{u, u} D.k
      (coefficientSheaf.{u, u} D.k l E n integral)
      (coefficientMap.{u, u} D.k l E n integral) (op (finalObject D.k)))) :
    pointSectionsReconstructionResult D.k l E n hn integral L adj := by
  cases integral
  · let := adj.left_adjoint_additive
    constructor
    · intro c
      constructor
      · change IsIso (adj.mapDerivedCategoryAdjunction.unit.app c.obj)
        apply adjunction_unit_derived_isIso D.k
          (coefficientRing.{u, u} l E n false) _ _ L adj hsections c.obj
        intro i
        have : Finite ((moduleHomologySmall
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) i).obj c.obj) :=
          c.property.2 i
        have : Finite ((DerivedCategory.homologyFunctor.{u + 2}
            (ModuleCat.{u + 1} (ULift.{u + 1, u}
              (Padic.coefficientExtensionRing l E n))) i).obj c.obj) :=
          Finite.of_equiv ((moduleHomologySmall
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) i).obj c.obj)
            ((moduleHomologyShrinkIso
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) i).app
              c.obj).toLinearEquiv.toEquiv.symm
        have := Padic.finite_coefficientExtensionRing l E n hn
        have : Finite (coefficientRing.{u, u} l E n false) := by
          change Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
          infer_instance
        change Module.FinitePresentation
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
        simpa only [coefficientRing] using
          (Module.finitePresentation_of_finite
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
            ((DerivedCategory.homologyFunctor.{u + 2}
              (ModuleCat.{u + 1} (ULift.{u + 1, u}
                (Padic.coefficientExtensionRing l E n))) i).obj c.obj))
      · classical
        let A := Padic.coefficientExtensionRing l E n
        have : Finite A := Padic.finite_coefficientExtensionRing l E n hn
        have eH (i : ℤ) :
            (L.obj ((moduleHomologySmall (ULift.{u + 1, u} A) i).obj c.obj)) ≅
              (DerivedCategory.homologyFunctor _ i).obj (L.mapDerivedCategory.obj c.obj) :=
          L.mapIso ((moduleHomologyShrinkIso (ULift.{u + 1, u} A) i).app c.obj).symm ≪≫
            (L.mapDerivedCategoryHomologyFunctorIso i).app c.obj
        constructor
        · obtain ⟨s, hs⟩ := c.property.1
          apply s.finite_toSet.subset
          intro i hi
          by_contra his
          exact hi ((L.map_isZero (hs i his)).of_iso (eH i).symm)
        · intro i
          have : Finite ((moduleHomologySmall (ULift.{u + 1, u} A) i).obj c.obj) :=
            c.property.2 i
          have h := finiteExtension_constructible D.k A L adj
            ((moduleHomologySmall (ULift.{u + 1, u} A) i).obj c.obj)
          rw [proEtaleModuleRestriction_constructible_iff] at h ⊢
          exact ProEtale.isConstructible_of_iso
            ((proEtaleModuleRestriction (Spec (.of D.k)) A).mapIso (eH i)) h
    · intro C hC
      have := Padic.finite_coefficientExtensionRing l E n hn
      apply adjunction_counit_derived_isIso (coefficientRing.{u, u} l E n false) L _ adj C
      intro i
      let G := sections.{u, u} D.k
        (constantRing.{u, u} D.k
          (.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))) (𝟙 _)
      have : PreservesFiniteLimits G :=
        inferInstanceAs (PreservesFiniteLimits (sections.{u, u} D.k
          (coefficientSheaf.{u, u} D.k l E n false) (coefficientMap.{u, u} D.k l E n false)))
      have : PreservesFiniteColimits G :=
        inferInstanceAs (PreservesFiniteColimits (sections.{u, u} D.k
          (coefficientSheaf.{u, u} D.k l E n false) (coefficientMap.{u, u} D.k l E n false)))
      exact finite_counit_isIso D.k _ L adj hsections _ (hC.2 i)
  · let := adj.left_adjoint_additive
    let : HasDerivedCategory (PointDerivedHom.Modules.{u, u} D.k
        (coefficientSheaf.{u, u} D.k l E n true)) := HasDerivedCategory.standard _
    have hforward : ∀ c : DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))),
      (∃ s : Finset ℤ, (∀ i : ℤ, i ∉ s →
        IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionIntegers l E))) i).obj c)) ∧
        (∀ i : ℤ, Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
          ((DerivedCategory.homologyFunctor
            (ModuleCat.{u + 1} (ULift.{u + 1, u}
              (Padic.coefficientExtensionIntegers l E))) i).obj c))) →
        IsIso (adj.mapDerivedCategoryAdjunction.unit.app c) ∧
          sfIntegralConstructible l E (Spec (.of D.k)) (L.mapDerivedCategory.obj c) ∧
          ∃ (P : CochainComplex (ModuleCat.{u + 1}
              (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ℤ) (a b : ℤ),
            P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
            (∀ i : ℤ, Module.Projective
              (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) (P.X i) ∧
              Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
                (P.X i)) ∧
            Nonempty (c ≅ DerivedCategory.Q.obj P) ∧
            sfIntegralConstructible l E (Spec (.of D.k))
              (L.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) := by
      intro c hc
      obtain ⟨s, hs, hc⟩ := hc
      have hpid : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) := by
        have hdvr := (Padic.extension_integers_dvr l E
          (Padic.coefficientExtensionAbsoluteValue l E)
          (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
        exact hdvr.2.2.2.2.2.2.2.2.1
      have : IsPrincipalIdealRing (ULift.{u + 1, u}
          (Padic.coefficientExtensionIntegers l E)) :=
        IsPrincipalIdealRing.of_surjective ULift.ringEquiv.symm.toRingHom
          ULift.ringEquiv.symm.surjective
      have : IsDomain (ULift.{u + 1, u}
          (Padic.coefficientExtensionIntegers l E)) :=
        ULift.ringEquiv.toMulEquiv.isDomain
      have hperfect := perfect_bounded_finite_pid
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) c s hs hc
      constructor
      · apply adjunction_unit_derived_isIso D.k _ _ _ L adj hsections c
        intro i
        have hci := hc i
        let := hci
        change Module.FinitePresentation
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) _
        simpa only [coefficientRing] using
          (Module.finitePresentation_of_finite
            (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
            ((DerivedCategory.homologyFunctor.{u + 2}
              (ModuleCat.{u + 1} (ULift.{u + 1, u}
                (Padic.coefficientExtensionIntegers l E))) i).obj c))
      · let R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
        let Q : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} R)) :=
          (sfIntegralConstructible l E (Spec (.of D.k))).inverseImage L.mapDerivedCategory
        let hLshift : L.mapDerivedCategory.CommShift ℤ := inferInstance
        have hLtri : L.mapDerivedCategory.IsTriangulated := inferInstance
        have hQtri := sfIntegralConstructible_isTriangulated l E (Spec (.of D.k))
        have : Q.IsTriangulated := inferInstance
        have : Q.IsClosedUnderIsomorphisms := inferInstance
        have hR : Q ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of R R)) := by
          obtain ⟨eR⟩ := adjunction_rankOne_iso D.k
            (coefficientRing.{u, u} l E n true) (coefficientSheaf.{u, u} D.k l E n true)
            (coefficientMap.{u, u} D.k l E n true) L adj
          let e : L.mapDerivedCategory.obj
              ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of R R)) ≅
                integralConstantCoefficientObject l E (Spec (.of D.k)) :=
            (L.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of R R) ≪≫
            (DerivedCategory.singleFunctor _ 0).mapIso eR
          exact (sfIntegralConstructible l E (Spec (.of D.k))).prop_of_iso e.symm
            (integralConstantCoefficient_constructible l E (Spec (.of D.k)) D hl).2.1
        let Pfinite : ObjectProperty (ModuleCat.{u + 1} R) := fun M ↦ Module.Finite R M
        have : Pfinite.IsClosedUnderIsomorphisms := by
          constructor
          intro M N e hM
          let := hM
          exact Module.Finite.of_surjective e.hom.hom e.toLinearEquiv.surjective
        have hbounded : DerivedCategory.TStructure.t.bounded c := by
          obtain ⟨a, ha⟩ := s.finite_toSet.bddBelow
          obtain ⟨b, hb⟩ := s.finite_toSet.bddAbove
          refine ⟨⟨a, (DerivedCategory.isGE_iff c a).2 ?_⟩,
            ⟨b, (DerivedCategory.isLE_iff c b).2 ?_⟩⟩
          · intro i hi
            exact hs i (fun his ↦ (not_le_of_gt hi) (ha his))
          · intro i hi
            exact hs i (fun his ↦ (not_le_of_gt hi) (hb his))
        have hconstruct : Q c := DerivedCategory.prop_of_bounded Q Pfinite
          (fun M hM ↦ by
            let : Module.Finite R M := hM
            exact triangulated_single_finite_pid R Q hR M) c hbounded hc
        obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hperfect
        exact ⟨hconstruct, P, a, b, ha, hb, hP, ⟨e⟩,
          (sfIntegralConstructible l E (Spec (.of D.k))).prop_of_iso
            (L.mapDerivedCategory.mapIso e) hconstruct⟩
    constructor
    · exact hforward
    · intro C
      let G := sections.{u, u} D.k (coefficientSheaf.{u, u} D.k l E n true)
        (coefficientMap.{u, u} D.k l E n true)
      have : (pointIntegralSections l E D.k).Additive := pointIntegralSectionsAdditive _ _ _
      have : PreservesFiniteLimits (pointIntegralSections l E D.k) :=
        pointReductionIntegralLimits D l E
      have : PreservesFiniteColimits (pointIntegralSections l E D.k) :=
        pointReductionIntegralColimits D l E
      let eG := Functor.mapDerivedCategoryNatIso (integralSectionsIso D.k l E n)
      let R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
      let : HasDerivedCategory (ModuleCat.{u + 1} R) := HasDerivedCategory.standard _
      let P : CochainComplex (scalarReductionSource.{u, u} l E (Spec (.of D.k))) ℤ :=
        DerivedCategory.Q.objPreimage C.obj
      let eP := DerivedCategory.Q.objObjPreimageIso C.obj
      have hP : sfIntegralConstructible l E (Spec (.of D.k)) (DerivedCategory.Q.obj P) :=
        (sfIntegralConstructible l E (Spec (.of D.k))).prop_of_iso eP.symm C.property
      have hfg := ((point_sections_finiteness D l hl E n hn).2 P hP).1
      let PS := ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj P
      let eS : G.mapDerivedCategory.obj C.obj ≅ DerivedCategory.Q.obj PS :=
        G.mapDerivedCategory.mapIso eP.symm ≪≫ G.mapDerivedCategoryFactors.app P
      have eH (i : ℤ) :
          (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj
            (G.mapDerivedCategory.obj C.obj) ≅
          (moduleHomologySmall R i).obj ((moduleQSmall R).obj PS) :=
        (DerivedCategory.homologyFunctor _ i).mapIso eS ≪≫
          (moduleHomologyShrinkIso R i).app (DerivedCategory.Q.obj PS)
      have hc : ∃ s : Finset ℤ, (∀ i : ℤ, i ∉ s →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj
            (G.mapDerivedCategory.obj C.obj))) ∧
          (∀ i : ℤ, Module.Finite R
            ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj
              (G.mapDerivedCategory.obj C.obj))) := by
        obtain ⟨s, hs⟩ := hfg.1
        refine ⟨s, ?_, ?_⟩
        · intro i hi
          exact (hs i hi).of_iso (eH i)
        · intro i
          have : Module.Finite R
              ((moduleHomologySmall R i).obj ((moduleQSmall R).obj PS)) := hfg.2.1 i
          exact Module.Finite.of_surjective (eH i).inv.hom (eH i).toLinearEquiv.symm.surjective
      have hunit := (hforward (G.mapDerivedCategory.obj C.obj) hc).1
      have hsource := (hforward (G.mapDerivedCategory.obj C.obj) hc).2.1
      have hmap : IsIso (G.mapDerivedCategory.map
          (adj.mapDerivedCategoryAdjunction.counit.app C.obj)) :=
        IsIso.of_isIso_fac_left (adj.mapDerivedCategoryAdjunction.right_triangle_components C.obj)
      obtain ⟨Z, g, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle
        (adj.mapDerivedCategoryAdjunction.counit.app C.obj)
      let T := Pretriangulated.Triangle.mk
        (adj.mapDerivedCategoryAdjunction.counit.app C.obj) g δ
      have hZ : sfIntegralConstructible l E (Spec (.of D.k)) Z :=
        (sfIntegralConstructible l E (Spec (.of D.k))).ext_of_isTriangulatedClosed₃
          T hT hsource C.property
      have hzG : IsZero (G.mapDerivedCategory.obj Z) :=
        Pretriangulated.Triangle.isZero₃_of_isIso₁ _
          (G.mapDerivedCategory.map_distinguished T hT) hmap
      have hz : IsZero Z := integral_constructible_isZero D l hl E ⟨Z, hZ⟩
        (hzG.of_iso (eG.app Z).symm)
      exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ T hT).mp hz

end WeilConjectures
