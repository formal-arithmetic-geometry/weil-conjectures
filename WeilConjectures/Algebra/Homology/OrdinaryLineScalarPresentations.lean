/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OrdinaryLineScalarData
import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-! # Ordinary signed-line tensor and derived scalar extension

Source: Stacks Project, Tags 07A4, 0G7E and 0D6D; blueprint main-20261015,
Tate-twist local freeness, proof (3).
(blueprint: lem-pur-ordinary-line-scalar-presentations)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe t a w u v b r ua va
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
-- Prefer the native additive structures over routes through abelian instances.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
namespace SheafOfModules.OrdinaryLineScalar

variable (X : Scheme.{t}) [EssentiallySmall.{max a (t + 1)} X.ProEt]

variable {X}
  [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
    HasDerivedCategory.{w} (Modules.{t, a} X R)]
local notation "𝒬[" R "]" => (DerivedCategory.Q (C := Modules X R))
attribute [local instance] modulesCategory modulesAbelian monoidalCategory
attribute [local implicit_reducible] monoidalCategory
attribute [local irreducible] compute

set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false in
private theorem localized_unit
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    (E : A ⥤ A) [E.Additive] (o : E ≅ 𝟭 A)
    (D : DerivedCategory A ⥤ DerivedCategory A)
    (eps : DerivedCategory.Qh ⋙ D ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hd : D.IsLeftDerivedFunctor eps (HomotopyCategory.quasiIso A (.up ℤ))) :
    ∃ d : D ≅ 𝟭 (DerivedCategory A), ∀ P : CochainComplex A ℤ,
      d.hom.app ((DerivedCategory.Q (C := A)).obj P) =
        D.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
        eps.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((E.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso A).hom.app
          ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (DerivedCategory.Q (C := A)).map
          ((Functor.mapHomologicalComplexCompIso
            (Functor.isoWhiskerLeft (𝟭 _) o ≪≫ Functor.leftUnitor _) (.up ℤ) ≪≫
            Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app P) := by
  let h : E.mapHomotopyCategory (.up ℤ) ≅ (𝟭 A).mapHomotopyCategory (.up ℤ) := {
    hom := NatTrans.mapHomotopyCategory o.hom (.up ℤ)
    inv := NatTrans.mapHomotopyCategory o.inv (.up ℤ)
    hom_inv_id := by
      rw [← NatTrans.mapHomotopyCategory_comp, o.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
    inv_hom_id := by
      rw [← NatTrans.mapHomotopyCategory_comp, o.inv_hom_id,
        NatTrans.mapHomotopyCategory_id] }
  let eH := h ≪≫ Functor.mapHomotopyCategoryIdIso A (.up ℤ)
  let e : E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅ DerivedCategory.Qh :=
    Functor.isoWhiskerRight eH DerivedCategory.Qh ≪≫ Functor.leftUnitor _
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  have hi : W.IsInvertedBy (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso W e).2 (Localization.inverts _ W)
  let _ := hd
  have _ := Functor.isIso_of_isLeftDerivedFunctor_of_inverts D eps hi
  let factors := asIso eps ≪≫ e
  let d : D ≅ 𝟭 (DerivedCategory A) :=
    Localization.liftNatIso DerivedCategory.Qh W _ _ _ _
      (factors ≪≫ (Functor.rightUnitor _).symm)
  refine ⟨d, ?_⟩
  intro P
  have he (H : HomotopyCategory A (.up ℤ)) :
      d.hom.app (DerivedCategory.Qh.obj H) = eps.app H ≫
        DerivedCategory.Qh.map (eH.hom.app H) := by
    simp [d, factors, e, Localization.liftNatTrans_app, Localization.Lifting.iso]
  let v : (E.mapHomologicalComplex (.up ℤ)).obj P ⟶ P :=
    (Functor.mapHomologicalComplexCompIso
      (Functor.isoWhiskerLeft (𝟭 _) o ≪≫ Functor.leftUnitor _) (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app P
  have hv : eH.hom.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) =
      (E.mapHomotopyCategoryFactors (.up ℤ)).hom.app P ≫
        (HomotopyCategory.quotient A (.up ℤ)).map v := by
    simp only [eH, Iso.trans_hom, NatTrans.comp_app,
      Functor.mapHomotopyCategoryIdIso_hom_app, h, NatTrans.mapHomotopyCategory_app]
    change (HomotopyCategory.quotient A (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex o.hom (.up ℤ)).app P) ≫
      (HomotopyCategory.quotient A (.up ℤ)).map
        ((Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app P) =
      (𝟙 _) ≫ (HomotopyCategory.quotient A (.up ℤ)).map v
    rw [Category.id_comp, ← Functor.map_comp]
    congr 1
    ext i
    simp [v]
  have hn := d.hom.naturality ((DerivedCategory.quotientCompQhIso A).inv.app P)
  dsimp only [Functor.id_map, Functor.comp_obj] at hn
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso A).inv.app P)).1
  rw [← hn, he, hv, Functor.map_comp]
  simp only [Category.assoc]
  change _ = _ ≫ _ ≫ _ ≫ (DerivedCategory.quotientCompQhIso A).hom.app
    ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫ (DerivedCategory.Q (C := A)).map v ≫
      (DerivedCategory.quotientCompQhIso A).inv.app P
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality_assoc v]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem identity_ordinary_generic
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    [∀ R : Sheaf J CommRingCat.{r},
      HasDerivedCategory.{w} (SuccessiveDerivedQuotient.Modules R)]
    (p : ∀ {R S : Sheaf J CommRingCat.{r}}
      (α : R ⟶ S), SuccessiveDerivedQuotient.Presentation.{u, v, r, w}
        (J := J) α)
    (n : SuccessiveDerivedQuotient.Normalization.{u, v, r, w}
      (J := J) p)
    (R : Sheaf J CommRingCat.{r}) :
    ∃ o : (p (𝟙 R)).ordinary ≅ 𝟭 (SuccessiveDerivedQuotient.Modules R),
      ∀ M U s x, (o.hom.app M).val.app U
        (SuccessiveDerivedQuotient.sectionTensor (p (𝟙 R)) M U s x) = s • x := by
  let A := SuccessiveDerivedQuotient.Modules R
  let res := SuccessiveDerivedQuotient.restriction.{u, v, r}
    (J := J) (𝟙 R)
  let adj := n.ordinaryAdjunction (𝟙 R)
  let ri : res ≅ 𝟭 A :=
    NatIso.ofComponents (fun (M : A) ↦ {
      hom := { val := {
        app := fun U ↦ ModuleCat.ofHom
          (X := (res.obj M).val.obj U) (Y := M.val.obj U) {
          toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
        naturality := by intros; ext; rfl } }
      inv := { val := {
        app := fun U ↦ ModuleCat.ofHom
          (X := M.val.obj U) (Y := (res.obj M).val.obj U) {
          toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
        naturality := by intros; ext; rfl } }
      hom_inv_id := by ext; rfl
      inv_hom_id := by ext; rfl }) (by intros; ext; rfl)
  let ai := Adjunction.id.ofNatIsoRight ri.symm
  let o : (p (𝟙 R)).ordinary ≅ 𝟭 A := adj.leftAdjointUniq ai
  have ho (M : A) (U : Cᵒᵖ) (x : M.val.obj U) :
      (o.hom.app M).val.app U (SuccessiveDerivedQuotient.sectionTensor (p (𝟙 R)) M U 1 x) = x := by
    have h := Adjunction.unit_leftAdjointUniq_hom_app adj ai M
    have hx := congrArg (fun f ↦ f.val.app U x) h
    change (o.hom.app M).val.app U ((adj.unit.app M).val.app U x) = x at hx
    rw [n.ordinary_unit] at hx
    exact hx
  have hs (M : A) (U : Cᵒᵖ) (s : R.obj.obj U) (x : M.val.obj U) :
      SuccessiveDerivedQuotient.sectionTensor (p (𝟙 R)) M U s x = s •
        SuccessiveDerivedQuotient.sectionTensor (p (𝟙 R)) M U 1 x := by
    dsimp only [SuccessiveDerivedQuotient.sectionTensor]
    rw [← ((eqToHom ((p (𝟙 R)).obj_eq M).symm).val.app U).hom.map_smul]
    congr 1
    have hh := (scalarExtensionSection_smul (𝟙 R) M U s 1 x).symm
    simp only [mul_one] at hh
    exact hh
  exact ⟨o, fun M U s x ↦ by
    rw [hs, (o.hom.app M).val.app U |>.hom.map_smul, ho]⟩

set_option backward.isDefEq.respectTransparency false in
private theorem identity_unitData
    (p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
      (α : R ⟶ S), SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
        (J := Scheme.ProEt.topology X) α)
    (n : SuccessiveDerivedQuotient.Normalization.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) p)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}) :
    Nonempty (UnitData p R) := by
  obtain ⟨o, ho⟩ := identity_ordinary_generic.{w, t + 1, t, max a (t + 1)}
    (J := Scheme.ProEt.topology X) p n R
  obtain ⟨d, hd⟩ := localized_unit (p (𝟙 R)).ordinary o
    (p (𝟙 R)).derived (p (𝟙 R)).counit (p (𝟙 R)).universal
  exact ⟨{ ordinary := o
           formula := ho
           derived := d
           computed := fun P ↦ by simpa only [compute, Category.assoc] using hd P }⟩

/-- Choose the already existing universal scalar presentations with the normalized tower
and multiplication unitors. Source: Stacks 06YY and 0D6D
(blueprint: lem-pur-ordinary-line-scalar-presentations).
Proof: use successive_derived_quotient_normalization. For identity coefficients the
ordinary multiplication p tensor s maps to sp, with inverse p maps to p tensor 1.
It is a natural isomorphism and localizes to the stated unitor. The universal counit
and full faithfulness of localization give its computation equation. -/
theorem exists_presentations :
    ∃ p : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}
      (α : R ⟶ S), SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
        (J := Scheme.ProEt.topology X) α,
      Nonempty (SuccessiveDerivedQuotient.Normalization.{t + 1, t, max a (t + 1), w}
        (J := Scheme.ProEt.topology X) p) ∧
      ∀ R, Nonempty (UnitData p R) := by
  obtain ⟨p, hn⟩ := SuccessiveDerivedQuotient.successive_derived_quotient_normalization
    (J := Scheme.ProEt.topology X)
  refine ⟨p, hn, ?_⟩
  intro R
  exact identity_unitData p hn.some R


end SheafOfModules.OrdinaryLineScalar
