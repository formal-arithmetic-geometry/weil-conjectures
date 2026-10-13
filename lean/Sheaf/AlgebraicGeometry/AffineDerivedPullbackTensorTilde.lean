/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde
import Sheaf.AlgebraicGeometry.TensorPullbackTilde
import Sheaf.AlgebraicGeometry.AffineTildeTotalTensor
import Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison
import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.Algebra.Homology.KFlatResolution

/-! # Affine computations of derived pullback and tensor

Source: Stacks Project, Lemmas 36.3.8(2), 36.3.9(2), Tags 08DW and 08DX,
and Lemma 36.3.6, Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).

The affine formulas are written for every K-flat resolution `P ⟶ M`.
Thus the right sides are the concrete representatives of the module derived tensors,
with no boundedness, flatness of the ring map, or quasi-coherence hypothesis added.

## Main statements

- `derivedPullback_openRestriction_iso`: restriction of derived pullback.
- `derivedTensor_openRestriction_iso`: restriction of derived tensor, natural in both factors.
- `derivedPullback_tilde_iso`: affine pullback on any K-flat resolution.
- `derivedTensor_tilde_iso`: affine tensor on any K-flat resolution of the first factor.
- `derivedPullback_tilde_kFlat_natIso`: natural affine pullback comparison on K-flat models.
- `derivedTensor_tilde_kFlat_natIso`: natural affine tensor comparison on K-flat models.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry


attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem tensorDerivedCounit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ (_ : (Scheme.Modules.tensorPullback f).Additive)
      (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
        (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh
            (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))),
      (derivedPullback f).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) ∧
      ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
        CochainComplex.IsKFlat (R := Y.sheaf) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hL, htri, hK⟩ :=
      Classical.choose_spec (exists_derivedPullback f)
  have h : E = Scheme.Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hE (fun M N a ↦ hEmap a)
  subst E
  exact ⟨hEadd, ε, hL, hK⟩

attribute [local irreducible] derivedPullback schemeDerivedTensorMonoidal
  Functor.mapDerivedCategory

set_option maxHeartbeats 800000 in
-- The composition lift carries three independent derived counits.
private theorem derivedPullback_comp_iso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] :
    Nonempty (derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g)) := by
  classical
  obtain ⟨af, εf, hLf, hKf⟩ := tensorDerivedCounit f
  obtain ⟨ag, εg, hLg, hKg⟩ := tensorDerivedCounit g
  obtain ⟨ac, εc, hLc, hKc⟩ := tensorDerivedCounit (f ≫ g)
  have := hLf
  have := hLg
  have := hLc
  let A := SheafOfModules.{u} (moduleRings Z.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let F : B ⥤ C := Scheme.Modules.tensorPullback f
  let G : A ⥤ B := Scheme.Modules.tensorPullback g
  let H : A ⥤ C := Scheme.Modules.tensorPullback (f ≫ g)
  let qA : HomotopyCategory A (.up ℤ) ⥤ schemeDerivedCategory Z := DerivedCategory.Qh
  let qB : HomotopyCategory B (.up ℤ) ⥤ schemeDerivedCategory Y := DerivedCategory.Qh
  let qC : HomotopyCategory C (.up ℤ) ⥤ schemeDerivedCategory X := DerivedCategory.Qh
  obtain ⟨η₀⟩ := Scheme.Modules.nonempty_tensorPullbackComp f g
  let η : G ⋙ F ≅ H := η₀.symm
  let ηh := Functor.mapHomotopyCategoryCompIso η (.up ℤ)
  let β : qA ⋙ (derivedPullback g ⋙ derivedPullback f) ⟶
      H.mapHomotopyCategory (.up ℤ) ⋙ qC :=
    (Functor.associator qA (derivedPullback g) (derivedPullback f)).inv ≫
      Functor.whiskerRight εg (derivedPullback f) ≫
      (Functor.associator (G.mapHomotopyCategory (.up ℤ)) qB (derivedPullback f)).hom ≫
      Functor.whiskerLeft (G.mapHomotopyCategory (.up ℤ)) εf ≫
      (Functor.associator (G.mapHomotopyCategory (.up ℤ))
        (F.mapHomotopyCategory (.up ℤ)) qC).inv ≫ Functor.whiskerRight ηh.hom qC
  let τ := (derivedPullback (f ≫ g)).leftDerivedLift εc
    (HomotopyCategory.quasiIso A (.up ℤ)) (derivedPullback g ⋙ derivedPullback f) β
  have hflat (P : CochainComplex A ℤ) (hP : CochainComplex.IsKFlat (R := Z.sheaf) P) :
      IsIso (τ.app (qA.obj ((HomotopyCategory.quotient A (.up ℤ)).obj P))) := by
    have := hKg P hP
    have := hKc P hP
    have hGP : CochainComplex.IsKFlat (R := Y.sheaf)
        ((G.mapHomologicalComplex (.up ℤ)).obj P) := by
      have h := CochainComplex.isKFlat_pullback g.base Y.sheaf Z.sheaf ⟨g.c⟩ P hP
      convert h using 1
      rfl
    have hf := hKf ((G.mapHomologicalComplex (.up ℤ)).obj P) hGP
    have : IsIso (εf.app ((G.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient A (.up ℤ)).obj P))) := by
      rw [Functor.mapHomotopyCategory_obj]
      exact hf
    have fac := (derivedPullback (f ≫ g)).leftDerived_fac_app εc
      (HomotopyCategory.quasiIso A (.up ℤ)) (derivedPullback g ⋙ derivedPullback f) β
      ((HomotopyCategory.quotient A (.up ℤ)).obj P)
    have : IsIso (τ.app (qA.obj ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ≫
        εc.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) := by
      rw [show τ.app _ ≫ _ = _ from fac]
      dsimp [β]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (εc.app _)
  have : IsIso τ := by
    apply (NatTrans.isIso_iff_isIso_app τ).2
    intro K
    apply (NatTrans.isIso_app_iff_of_iso τ (qA.objObjPreimageIso K)).1
    obtain ⟨M, hM⟩ := HomotopyCategory.quotient_obj_surjective (qA.objPreimage K)
    rw [← hM]
    obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := Z.sheaf) M
    have hsq := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
    have := Localization.inverts qA (HomotopyCategory.quasiIso A (.up ℤ)) _ hsq
    apply (NatTrans.isIso_app_iff_of_iso τ
      (asIso (qA.map ((HomotopyCategory.quotient A (.up ℤ)).map s)))).1
    exact hflat P hP
  exact ⟨asIso τ⟩

set_option maxHeartbeats 800000 in
-- Transporting the chosen counit uses the exact restriction comparison.
private theorem derivedOpenRestriction_iso (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] :
    let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)
    Nonempty (derivedPullback U.ι ≅ R.mapDerivedCategory) := by
  classical
  obtain ⟨hEadd, ε, hL, hK⟩ := tensorDerivedCounit U.ι
  let T : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback U.ι
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
  let η : T ≅ R :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction U.ι).some.leftAdjointUniq
      (Scheme.Modules.restrictAdjunction U.ι) ≪≫ (Scheme.Modules.overFunctorEquiv U).symm
  have : PreservesFiniteLimits R := by dsimp [R]; infer_instance
  have : PreservesFiniteColimits R := by dsimp [R]; infer_instance
  have : T.Additive := hEadd
  have : R.Additive := Functor.additive_of_iso η
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso η.symm
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso η.symm
  let ηh : T.mapHomotopyCategory (.up ℤ) ≅ R.mapHomotopyCategory (.up ℤ) :=
    { hom := η.hom.mapHomotopyCategory (.up ℤ)
      inv := η.inv.mapHomotopyCategory (.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp }
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
  have : (derivedPullback U.ι).IsLeftDerivedFunctor ε W := hL
  have : R.mapDerivedCategory.IsLeftDerivedFunctor R.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ R.mapDerivedCategoryFactorsh
  exact ⟨Functor.leftDerivedNatIso (derivedPullback U.ι) R.mapDerivedCategory
    ε R.mapDerivedCategoryFactorsh.hom W
      (Functor.isoWhiskerRight ηh DerivedCategory.Qh)⟩

/-- Derived pullback commutes naturally with restriction to opens.
Source: Stacks, Tag 08DW, proof
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node steps 1 and 2): the tensor-pullback adjunction and uniqueness of left
derived functors identify derived pullback along an open inclusion with exact
restriction. The composition comparison is invertible on K-flat representatives
by lem-pc-kflat-pullback-preservation, and hence everywhere by lem-pc-kflat-resolution
and naturality. Apply it to both sides of `U.ι ≫ f = f.resLE V U hUV ≫ V.ι`,
then whisker with the two exact-restriction identifications. -/
theorem derivedPullback_openRestriction_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))] :
    Nonempty (derivedPullback f ⋙
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).mapDerivedCategory ≅
      (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
          (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv V)).mapDerivedCategory ⋙
        derivedPullback (f.resLE V U hUV)) := by
  obtain ⟨αU⟩ := derivedOpenRestriction_iso X U
  obtain ⟨αV⟩ := derivedOpenRestriction_iso Y V
  obtain ⟨cU⟩ := derivedPullback_comp_iso U.ι f
  obtain ⟨cV⟩ := derivedPullback_comp_iso (f.resLE V U hUV) V.ι
  have h : U.ι ≫ f = f.resLE V U hUV ≫ V.ι := by simp
  exact ⟨Functor.isoWhiskerLeft (derivedPullback f) αU.symm ≪≫ cU ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) h) ≪≫ cV.symm ≪≫
    Functor.isoWhiskerRight αV (derivedPullback (f.resLE V U hUV))⟩

/-- Derived tensor commutes with restriction to any open subscheme.
Source: Stacks, Tag 08DX, proof; the restriction computation of Tag 08DW
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 3): identify derived pullback along `U.ι` with exact restriction
by adjunction uniqueness and uniqueness of left derived functors. Transport the
strong monoidal structure of def-pc-derived-pullback-monoidal-model through this
natural isomorphism. The inverse of Mathlib's `Functor.curriedTensorPreIsoPost`
for that transported structure gives the comparison, natural in both arguments. -/
theorem derivedTensor_openRestriction_iso (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    : Nonempty
      (curriedTensor (schemeDerivedCategory X) ⋙
        (Functor.whiskeringRight (schemeDerivedCategory X) (schemeDerivedCategory X)
          (schemeDerivedCategory U.toScheme)).obj
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory ≅
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory ⋙
          curriedTensor (schemeDerivedCategory U.toScheme) ⋙
          (Functor.whiskeringLeft (schemeDerivedCategory X)
            (schemeDerivedCategory U.toScheme) (schemeDerivedCategory U.toScheme)).obj
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory) := by
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
  obtain ⟨α⟩ := derivedOpenRestriction_iso X U
  obtain ⟨m, hm⟩ := exists_derivedPullbackMonoidalModel U.ι
  let := m.toMonoidal
  let := Functor.Monoidal.transport α
  exact ⟨(Functor.curriedTensorPreIsoPost R.mapDerivedCategory).symm⟩


private theorem moduleKFlat_acyclic (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P)
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (hF : F.Acyclic) :
    (CochainComplex.mapBifunctor F P (curriedTensor (ModuleCat.{u} A))).Acyclic := by
  have h := (HomotopyCategory.kFlat_iff_preserves_acyclic
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)).mp
      ((HomotopyCategory.kFlat_quotient_obj_iff P).mpr hP)
  have hF' := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).mpr hF
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
    (h _ hF').2

private theorem complexDerivedCounitIso
    {C D I : Type (u + 1)} [Category.{u} C] [Category.{u} D] [Category.{u} I]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (F : I ⥤ CochainComplex C ℤ) (E : C ⥤ D) [E.Additive]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [IsIso (Functor.whiskerLeft (F ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε)] :
    Nonempty (F ⋙ DerivedCategory.Q ⋙ L ≅
      F ⋙ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  exact ⟨Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft F (DerivedCategory.quotientCompQhIso _).symm) L ≪≫
    asIso (Functor.whiskerLeft (F ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft F (E.mapHomotopyCategoryFactors (.up ℤ)))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft (F ⋙ E.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _)⟩

private theorem complexFunctorSquareIso
    {C₁ C₂ D₁ D₂ : Type (u + 1)}
    [Category.{u} C₁] [Category.{u} C₂] [Category.{u} D₁] [Category.{u} D₂]
    [Preadditive C₁] [Preadditive C₂] [Preadditive D₁] [Preadditive D₂]
    (F : C₁ ⥤ D₁) (G : D₁ ⥤ D₂) (H : C₁ ⥤ C₂) (K : C₂ ⥤ D₂)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    (θ : F ⋙ G ≅ H ⋙ K) :
    Nonempty (F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ K.mapHomologicalComplex (.up ℤ)) := by
  exact ⟨Functor.mapHomologicalComplexCompIso θ (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ K)) (.up ℤ)).symm⟩

private theorem complexDerivedSquareIso
    {C₁ C₂ D₁ D₂ I : Type (u + 1)}
    [Category.{u} C₁] [Category.{u} C₂] [Category.{u} D₁] [Category.{u} D₂]
    [Category.{u} I] [Preadditive C₁] [Preadditive C₂] [Abelian D₁] [Abelian D₂]
    [HasDerivedCategory.{w} D₁] [HasDerivedCategory.{w} D₂]
    (ι : I ⥤ CochainComplex C₁ ℤ)
    (F : C₁ ⥤ D₁) (G : D₁ ⥤ D₂) (E : C₁ ⥤ C₂) (H : C₂ ⥤ D₂)
    [F.Additive] [G.Additive] [E.Additive] [H.Additive]
    (L : DerivedCategory D₁ ⥤ DerivedCategory D₂)
    (ε : DerivedCategory.Qh ⋙ L ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [hI : IsIso (Functor.whiskerLeft
      ((ι ⋙ F.mapHomologicalComplex (.up ℤ)) ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε)]
    (θ : F ⋙ G ≅ E ⋙ H) :
    Nonempty (ι ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙ L ≅
      ι ⋙ E.mapHomologicalComplex (.up ℤ) ⋙ H.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q) := by
  obtain ⟨β⟩ := complexDerivedCounitIso (ι ⋙ F.mapHomologicalComplex (.up ℤ)) G L ε
  obtain ⟨δ⟩ := complexFunctorSquareIso F G E H θ
  exact ⟨β ≪≫ Functor.isoWhiskerLeft ι
    (Functor.isoWhiskerRight δ (DerivedCategory.Q (C := D₂)))⟩

/-- Naturality of the affine pullback comparison on K-flat module models.
Source: Stacks, Tag 08DW(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node steps 4 and 6): apply the natural termwise tilde/base-change isomorphism
(lem-weil-pbc-tilde-pullback-base-change) to K-flat complexes. Their tilde complexes
are K-flat (lem-pc-affine-tilde-kflat), so the derived-pullback counit is invertible
there (def-pc-derived-pullback). Compose the two natural comparisons. For arbitrary
M use a K-flat resolution P to M; exact tilde sends it to an isomorphism after Q
(lem-pc-affine-qcoh-derived-equivalence). Naturality on K-flat models gives compatibility
with resolution comparisons, hence the affine formula independent of that choice. -/
theorem derivedPullback_tilde_kFlat_natIso (A B : Type u) [CommRing A] [CommRing B]
    (φ : A →+* B)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))] :
    Nonempty
      (CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
        (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙
          DerivedCategory.Q ⋙ derivedPullback (Spec.map (CommRingCat.ofHom φ)) ≅
        CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} B ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))
            (tilde.functor (.of B))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q) := by
  let f := Spec.map (CommRingCat.ofHom φ)
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  let F := CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ T
  obtain ⟨hEadd, ε, hε, hflat⟩ := tensorDerivedCounit f
  let E₀ : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace) :=
    Scheme.Modules.tensorPullback f
  have : E₀.Additive := hEadd
  have hεiso (P : CochainComplex.KFlat (ModuleCat.{u} A)) :
      IsIso ((Functor.whiskerLeft
        (F ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε).app P) := by
    apply hflat
    exact isKFlat_tilde A P.obj (moduleKFlat_acyclic A P.obj P.property)
  have hεall : IsIso (Functor.whiskerLeft (F ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε) :=
    NatIso.isIso_of_isIso_app _
  obtain ⟨θ, _⟩ := Scheme.Modules.exists_tensorPullback_tilde_iso (CommRingCat.ofHom φ)
  have : (tilde.functor (.of A) : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)).Additive :=
    ⟨by intros; exact tilde.map_add _ _⟩
  have : (tilde.functor (.of B) : ModuleCat.{u} B ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)).Additive :=
    ⟨by intros; exact tilde.map_add _ _⟩
  exact complexDerivedSquareIso (hI := hεall)
    (D₁ := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
    (D₂ := SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))
    (CochainComplex.ιKFlat (ModuleCat.{u} A))
    (tilde.functor (.of A)) E₀ (ModuleCat.extendScalars φ) (tilde.functor (.of B))
    (derivedPullback f) ε θ

/-- Naturality of the affine tensor comparison in a K-flat first model and an arbitrary
second complex. Source: Stacks, Tag 08DX(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 5): tilde of the first model is K-flat
(lem-pc-affine-tilde-kflat). Apply the existing natural K-flat derived-tensor
comparison (lem-pc-kflat-derived-tensor-comparison), then the existing localized
tilde total-tensor comparison (lem-pc-affine-tilde-total-tensor), precomposed in
its first argument by the K-flat inclusion. Compose these natural isomorphisms;
all associativity identifications are functor associators. -/
theorem derivedTensor_tilde_kFlat_natIso (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))] :
    Nonempty
      (CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
        (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q ⋙
          curriedTensor (schemeDerivedCategory (Spec (.of A))) ⋙
          (Functor.whiskeringLeft (CochainComplex (ModuleCat.{u} A) ℤ)
            (schemeDerivedCategory (Spec (.of A)))
            (schemeDerivedCategory (Spec (.of A)))).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q) ≅
        CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
          (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex ⋙
          (Functor.whiskeringRight (CochainComplex (ModuleCat.{u} A) ℤ)
            (CochainComplex (ModuleCat.{u} A) ℤ)
            (schemeDerivedCategory (Spec (.of A)))).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q)) := by
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  let F := CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ T
  have hβ := kFlat_derivedTensor_comparison_natIso (Spec (.of A)) F T
    (fun P ↦ isKFlat_tilde A P.obj (moduleKFlat_acyclic A P.obj P.property))
  have hθ := affineTilde_totalTensor_natIso A
  refine Nonempty.map2 ?_ hβ hθ
  intro β θ
  let ι := CochainComplex.ιKFlat (ModuleCat.{u} A)
  exact (Functor.associator ι T _).symm ≪≫ β ≪≫
    Functor.associator ι T _ ≪≫ Functor.isoWhiskerLeft ι θ



private theorem affineTilde_Q_map_isIso (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (s : P ⟶ M) (hs : QuasiIso s) :
    IsIso (DerivedCategory.Q.map
      (((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ))).map s)) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  obtain ⟨e, ⟨α⟩, _⟩ := exists_affineQCohDerivedEquivalence A
  have : QuasiIso s := hs
  exact (NatIso.isIso_map_iff α s).mp (by
    change IsIso (((e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).map
      (DerivedCategory.Q.map s)))
    infer_instance)

/-- Affine derived pullback of termwise tilde is termwise tilde of derived base change,
computed on any K-flat resolution of the input complex.
Source: Stacks, Tag 08DW(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node steps 4 and 6): use the specified resolution P to M. Termwise tilde
preserves quasi-isomorphisms (lem-pc-affine-qcoh-derived-equivalence), and tilde P
is K-flat (lem-pc-affine-tilde-kflat). Derived pullback is therefore represented
by termwise tensor pullback of tilde P (def-pc-derived-pullback).
The natural tilde/base-change comparison in each degree
(lem-weil-pbc-tilde-pullback-base-change) identifies this with tilde of B tensor P.
This complex computes M tensor-derived B since P is K-flat. -/
theorem derivedPullback_tilde_iso (A B : Type u) [CommRing A] [CommRing B]
    (φ : A →+* B)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))]
    (M P : CochainComplex (ModuleCat.{u} A) ℤ) (s : P ⟶ M) (hs : QuasiIso s)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P) :
    Nonempty
      ((derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj
        (DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} A ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
              (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)) ≅
        DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} B ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))
              (tilde.functor (.of B))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj
                (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P))) := by
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  have : IsIso (DerivedCategory.Q.map (T.map s)) := affineTilde_Q_map_isIso A s hs
  obtain ⟨α⟩ := derivedPullback_tilde_kFlat_natIso A B φ
  exact ⟨(derivedPullback (Spec.map (CommRingCat.ofHom φ))).mapIso
    (asIso (DerivedCategory.Q.map (T.map s))).symm ≪≫ α.app ⟨P, hP⟩⟩

/-- On an affine scheme, derived tensor of termwise tilde complexes is termwise tilde
of module derived tensor, computed with any K-flat resolution of the first factor.
Source: Stacks, Tag 08DX(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node steps 5 and 6): use the specified resolution P to M. Exactness of termwise
tilde (lem-pc-affine-qcoh-derived-equivalence) and K-flatness of tilde P
(lem-pc-affine-tilde-kflat) allow the sheaf derived tensor to be computed by
Tot(tilde P tensor tilde N) (def-pc-kflat-complex, def-pc-tensor-complex-sheaves).
In each bidegree apply lem-weil-pbc-affine-tilde-tensor; its naturality respects
both differentials. Tilde preserves the direct sums used in totalization, yielding
tilde Tot(P tensor N). This computes M tensor-derived N since P is K-flat.
The sum over p+q=n can be infinite for unbounded complexes; all coproducts, not just
finite ones, are preserved by tilde, which is a left adjoint. -/
theorem derivedTensor_tilde_iso (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (M N P : CochainComplex (ModuleCat.{u} A) ℤ) (s : P ⟶ M) (hs : QuasiIso s)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P) :
    Nonempty
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ⊗
        DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} A ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
              (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj N) ≅
        DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} A ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
              (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor (ModuleCat.{u} A))))) := by
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  have : IsIso (DerivedCategory.Q.map (T.map s)) := affineTilde_Q_map_isIso A s hs
  obtain ⟨α⟩ := derivedTensor_tilde_kFlat_natIso A
  exact ⟨((curriedTensor (schemeDerivedCategory (Spec (.of A)))).flip.obj
    (DerivedCategory.Q.obj (T.obj N))).mapIso
      (asIso (DerivedCategory.Q.map (T.map s))).symm ≪≫ (α.app ⟨P, hP⟩).app N⟩


end AlgebraicGeometry
