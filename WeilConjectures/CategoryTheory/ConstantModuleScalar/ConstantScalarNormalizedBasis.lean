/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantModuleScalar.ConstantModuleScalarCenter
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import WeilConjectures.Algebra.Homology.SmoothPurity.BasedTensorEvaluation
public import WeilConjectures.AlgebraicGeometry.Picard.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeExtensionLeftExact
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Normalized finite-basis inclusions for exact constant scalar extension -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r w i
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.RingedCoefficientCounit
open scoped ChangeOfRings

namespace CategoryTheory.ConstantModuleScalar

private theorem basisLift_constant (V : Cᵒᵖ) (x : B) :
    (basisLift J A B).val.app V
      ((toSheafify J ((basisConst (C := C) A).obj (ModuleCat.of A B)).presheaf).app V x) =
        (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app V x := by
  have h := congrArg (fun g ↦
      (PresheafOfModules.toPresheaf ((Functor.const Cᵒᵖ).obj (RingCat.of A))).map g)
    ((PresheafOfModules.sheafificationHomEquiv (basisRingUnit J A)
      (P := (basisConst (C := C) A).obj (ModuleCat.of A B))
      (F := basisTarget J A B)).apply_symm_apply (basisConstToTarget J A B))
  rw [basisLift]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h V) x

private theorem basisMap_constant {M N : ModuleCat.{r} A} (g : M ⟶ N)
    (V : Cᵒᵖ) (x : M) :
    ((PresheafOfModules.sheafification (basisRingUnit J A)).map
      ((basisConst A).map g)).val.app V
        ((toSheafify J ((basisConst (C := C) A).obj M).presheaf).app V x) =
      (toSheafify J ((basisConst (C := C) A).obj N).presheaf).app V (g x) := by
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality J
      ((PresheafOfModules.toPresheaf _).map ((basisConst (C := C) A).map g))) V) x).symm

private theorem basis_coordinate_constant (n : ℕ) (b : Module.Basis (Fin n) A B)
    (V : Cᵒᵖ) (x : B) (i : Fin n) :
    ((basisSheafIso J A B n b).hom ≫ Pi.π _ i).val.app V
      ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).app V x) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app V (b.equivFun x i) := by
  rw [← basisLift_constant J A B V x]
  change ((basisLift J A B ≫ (basisSheafIso J A B n b).hom ≫ Pi.π _ i).val.app V) _ = _
  simp only [basisSheafIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
    IsIso.hom_inv_id_assoc, Pi.mapIso_hom_π, piComparison_comp_π_assoc,
    Functor.mapIso_hom, asIso_hom]
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc, limit.isoLimitCone_inv_π]
  change (basisTarget_self J A).hom.val.app V
    ((basisLift J A A).val.app V
      (((PresheafOfModules.sheafification (basisRingUnit J A)).map
        ((basisConst A).map (ModuleCat.ofHom
          ((LinearMap.proj i).comp b.equivFun.toLinearMap)))).val.app V
            ((toSheafify J ((basisConst (C := C) A).obj (ModuleCat.of A B)).presheaf).app
              V x))) = _
  have hs (R : Sheaf J RingCat.{r}) (f : R ⟶ R) (hf : f = 𝟙 R) (V : Cᵒᵖ)
      (x : ((SheafOfModules.restrictScalars f).obj (SheafOfModules.unit R)).val.obj V) :
      (show ((SheafOfModules.restrictScalars f).obj (SheafOfModules.unit R)) ≅
        SheafOfModules.unit R from by rw [hf]; exact Iso.refl _).hom.val.app V x = x := by
    subst f
    rfl
  rw [show ∀ z, (basisTarget_self J A).hom.val.app V z = z from
    fun z ↦ hs _ _ (by
      change ((constantSheaf J CommRingCat) ⋙
        sheafCompose J (forget₂ CommRingCat RingCat)).map (𝟙 A) = _
      exact Functor.map_id _ _) V z]
  rw [basisMap_constant, basisLift_constant]
  rfl

private def tensorCoords (n : ℕ) (b : Module.Basis (Fin n) A B) :
    SheafOfModules.tensorFunctor ((constantSheaf J CommRingCat).map
      (CommRingCat.ofHom (algebraMap A B))) ⋙ restriction
        ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))) ≅
      Functor.pi' (fun _ : Fin n ↦ 𝟭 (modules (constantRing J A))) ⋙ Pi.functor (Fin n) :=
  SheafOfModules.tensorCoordinateIso _ n (basisSheafIso J A B n b).symm

private theorem tensorCoords_constant (n : ℕ) (b : Module.Basis (Fin n) A B)
    (M : modules (constantRing J A)) (V : Cᵒᵖ) (s : B) (x : M.val.obj V) (c : Fin n) :
    (Pi.π (fun _ : Fin n ↦ M) c).val.app V
      (((tensorCoords J A B n b).hom.app M).val.app V
        ((toSheafify J (SheafOfModules.changeOfRingsPresheaf
          ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B)))
            M).presheaf).app V
          ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).app V s
            ⊗ₜ[(constantRing J A).obj.obj V,
              (((constantSheaf J CommRingCat).map
                (CommRingCat.ofHom (algebraMap A B))).hom.app V).hom] x))) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app V (b.equivFun s c) • x := by
  let φ := (constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))
  let e :
      (∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          ((constantSheaf J CommRingCat).obj A))) ≅
        (SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
              ((constantSheaf J CommRingCat).obj B))) :=
    (basisSheafIso J A B n b).symm
  simp only [tensorCoords, SheafOfModules.tensorCoordinateIso, NatIso.ofComponents_hom_app]
  have hh := congrArg (fun f ↦ f.app V)
    (SheafOfModules.tensorSheafCoordinates_unit φ n e M)
  let s' : ((constantSheaf J CommRingCat).obj B).obj.obj V :=
    (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app V s
  have hv := ConcreteCategory.congr_hom hh
    (s' ⊗ₜ[(constantRing J A).obj.obj V, (φ.hom.app V).hom] x)
  change (SheafOfModules.tensorSheafCoordinates φ n e M).hom.val.app V
    ((SheafOfModules.tensorUnit φ M).app V _) = _ at hv
  refine (congrArg ((Pi.π (fun _ : Fin n ↦ M) c).val.app V) hv).trans ?_
  unfold SheafOfModules.tensorCoordinates
  change (Pi.π (fun _ : Fin n ↦ M) c).val.app V
    ((SheafOfModules.tensorCoordinateApp φ n e M V).hom _) = _
  refine (SheafOfModules.tensorCoordinateApp_tmul φ n e M V s' x c).trans ?_
  exact congrArg (fun a ↦ a • x) (basis_coordinate_constant J A B n b V s c)

private theorem derived_app_Q {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (B : CommRingCat.{r}) [HasDerivedCategory.{w} (modules (constantRing J B))]
    (b : B) (K : CochainComplex (modules (constantRing J B)) ℤ) :
    (derived J B b).app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((cochain J B b).app K) :=
  CatCenter.localization_app _ _ _ _

private theorem localized_unit
    {X : Type c} {Y : Type d} [Category.{vC} X] [Category.{vD} Y]
    [Abelian X] [Abelian Y] [HasDerivedCategory.{w} X] [HasDerivedCategory.{w} Y]
    {E : X ⥤ Y} {U : Y ⥤ X} [E.Additive] [U.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E ⊣ U) (P : CochainComplex X ℤ) :
    adj.onDerivedCategory.unit.app (DerivedCategory.Q.obj P) ≫
      U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app P) ≫
      U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P) := by
  have hu : adj.onDerivedCategory.unit.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.inv.app P) := by
    simp only [Adjunction.onDerivedCategory, Adjunction.localization_unit_app]
    rfl
  change _ = DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P)
  rw [hu]
  simp only [Category.assoc]
  let e := E.mapDerivedCategoryFactors.app P
  let v := U.mapDerivedCategoryFactors.app ((E.mapHomologicalComplex (.up ℤ)).obj P)
  change DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
    v.inv ≫ U.mapDerivedCategory.map e.inv ≫ U.mapDerivedCategory.map e.hom ≫ v.hom = _
  rw [← U.mapDerivedCategory.map_comp_assoc, e.inv_hom_id]
  erw [U.mapDerivedCategory.map_id]
  rw [Category.id_comp, v.inv_hom_id]
  exact Category.comp_id _

private theorem localized_basis_iso (n : ℕ) (b : Fin n → B)
    (h : ∀ M, IsIso (biproduct.desc fun c : Fin n ↦ adj.unit.app M ≫
      U.map ((ordinary J B (b c)).app (E.obj M)))) (M : DerivedCategory
        (modules (constantRing J A))) :
    IsIso (biproduct.desc fun c : Fin n ↦ adj.onDerivedCategory.unit.app M ≫
      U.mapDerivedCategory.map ((derived J B (b c)).app (E.mapDerivedCategory.obj M))) := by
  let d := adj.onDerivedCategory
  have hC (K : CochainComplex (modules (constantRing J A)) ℤ) :
      IsIso (biproduct.desc fun c : Fin n ↦ (adj.mapHomologicalComplex (.up ℤ)).unit.app K ≫
        (U.mapHomologicalComplex (.up ℤ)).map
          ((cochain J B (b c)).app ((E.mapHomologicalComplex (.up ℤ)).obj K))) := by
    have (m : ℤ) : IsIso ((biproduct.desc fun c : Fin n ↦
        (adj.mapHomologicalComplex (.up ℤ)).unit.app K ≫
          (U.mapHomologicalComplex (.up ℤ)).map
            ((cochain J B (b c)).app ((E.mapHomologicalComplex (.up ℤ)).obj K))).f m) := by
      have he : (fun c : Fin n ↦ (HomologicalComplex.eval _ _ m).map
          ((adj.mapHomologicalComplex (.up ℤ)).unit.app K ≫
            (U.mapHomologicalComplex (.up ℤ)).map
              ((cochain J B (b c)).app ((E.mapHomologicalComplex (.up ℤ)).obj K)))) =
          fun c : Fin n ↦ adj.unit.app (K.X m) ≫
            U.map ((ordinary J B (b c)).app (E.obj (K.X m))) := by
        funext c
        rfl
      have : IsIso (biproduct.desc fun c : Fin n ↦
          (HomologicalComplex.eval _ _ m).map
            ((adj.mapHomologicalComplex (.up ℤ)).unit.app K ≫
              (U.mapHomologicalComplex (.up ℤ)).map
                ((cochain J B (b c)).app ((E.mapHomologicalComplex (.up ℤ)).obj K)))) := by
        rw [he]
        exact h (K.X m)
      exact Functor.isIso_map_biproductDesc (HomologicalComplex.eval _ _ m) _
    exact HomologicalComplex.Hom.isIso_of_components _
  have hQ (K : CochainComplex (modules (constantRing J A)) ℤ) :
      IsIso (biproduct.desc fun c : Fin n ↦ d.unit.app (DerivedCategory.Q.obj K) ≫
        U.mapDerivedCategory.map ((derived J B (b c)).app
          (E.mapDerivedCategory.obj (DerivedCategory.Q.obj K)))) := by
    have := hC K
    have := Functor.isIso_biproductDesc_map DerivedCategory.Q
      (fun c : Fin n ↦ (adj.mapHomologicalComplex (.up ℤ)).unit.app K ≫
        (U.mapHomologicalComplex (.up ℤ)).map
          ((cochain J B (b c)).app ((E.mapHomologicalComplex (.up ℤ)).obj K)))
    let z := U.mapDerivedCategory.mapIso (E.mapDerivedCategoryFactors.app K) ≪≫
      U.mapDerivedCategoryFactors.app ((E.mapHomologicalComplex (.up ℤ)).obj K)
    refine isIso_biproductDesc_of_iso _ (fun c : Fin n ↦ DerivedCategory.Q.map
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app K ≫
        (U.mapHomologicalComplex (.up ℤ)).map
          ((cochain J B (b c)).app ((E.mapHomologicalComplex (.up ℤ)).obj K))))
      (Iso.refl _) z (fun c ↦ ?_) inferInstance
    have hu : d.unit.app (DerivedCategory.Q.obj K) ≫ z.hom =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) :=
      localized_unit adj K
    have e₁ := (derived J B (b c)).naturality (E.mapDerivedCategoryFactors.hom.app K)
    dsimp only [Functor.comp_obj, Functor.id_map] at e₁
    simp only [derived, CatCenter.localization_app] at e₁
    have e₂ := U.mapDerivedCategoryFactors.hom.naturality
      ((cochain J B (b c)).app ((E.mapHomologicalComplex (.up ℤ)).obj K))
    dsimp only [Functor.comp_map] at e₂
    simp only [Functor.map_comp, Iso.refl_hom, Category.id_comp, Category.assoc]
    dsimp only [z, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    simp only [derived]
    rw [← U.mapDerivedCategory.map_comp_assoc, ← e₁, U.mapDerivedCategory.map_comp,
      Category.assoc, e₂]
    simpa only [z, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
      congrArg (fun f ↦ f ≫ DerivedCategory.Q.map
        ((U.mapHomologicalComplex (.up ℤ)).map
          ((cochain J B (b c)).app ((E.mapHomologicalComplex (.up ℤ)).obj K)))) hu
  let e := DerivedCategory.Q.objObjPreimageIso M
  refine isIso_biproductDesc_of_iso _ _ e.symm
    ((E.mapDerivedCategory ⋙ U.mapDerivedCategory).mapIso e.symm) (fun c ↦ ?_)
    (hQ (DerivedCategory.Q.objPreimage M))
  have hu := d.unit.naturality e.inv
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hu
  simp only [Functor.comp_obj, Functor.mapIso_hom, Iso.symm_hom, Functor.comp_map,
    Category.assoc]
  have hc := (derived J B (b c)).naturality (E.mapDerivedCategory.map e.inv)
  rw [← U.mapDerivedCategory.map_comp, ← hc, U.mapDerivedCategory.map_comp]
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫
    U.mapDerivedCategory.map ((derived J B (b c)).app
      (E.mapDerivedCategory.obj (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage M)))))
        hu.symm

/-- The scalar-unit inclusions are finite-biproduct inclusions with their prescribed
pure-tensor representatives on every unbounded complex.
Source: Stacks 03CY, 03CZ and 07A6; finite-coefficient transport Steps 1 and 3
(blueprint: lem-pur-constant-scalar-normalized-basis).
Proof: sheafify the basis of B over A and its dual coordinate functionals. They give
mutually inverse maps between restricted tensor extension of M and a finite power
of M. Define each inclusion as the scalar unit followed by multiplication by its
basis vector; the adjunction formula makes this precisely x maps to b_a tensor x.
The coordinate functional sends c tensor x to q_a(c)x. Tensor balancing proves
linearity, including for locally constant coefficient sections. The basis expansion
and Kronecker identities prove both finite-matrix identities before sheafification;
the universal property of sheafification preserves them. All maps are natural in M,
so they commute with differentials. Apply the exact localization to these cochain
maps and their matrix identities. The localized unit and both exact-functor
factorizations yield exactly the last equation below. Transport the matrix
identities along Q.objObjPreimageIso to arbitrary derived objects. The empty
basis gives the zero object and the same empty-sum identity. -/
theorem normalized_basis
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    [HasWeakSheafify J CommRingCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (A B : CommRingCat.{r}) [Algebra A B]
    [HasDerivedCategory.{w} (modules (constantRing J A))]
    [HasDerivedCategory.{w} (modules (constantRing J B))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w}
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))))
    [PreservesFiniteLimits D.E] [PreservesFiniteColimits D.E]
    [PreservesFiniteLimits (restriction
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))))]
    [PreservesFiniteColimits (restriction
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))))]
    (a : D.E ⊣ restriction
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))))
    (ha : ∀ (M : modules (constantRing J A)) (N : modules (constantRing J B))
      (f : SheafOfModules.changeOfRings.{v, u, r}
        ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))) M ⟶ N)
      (V : Cᵒᵖ) (x : M.val.obj V),
      (a.homEquiv M N (eqToHom (D.obj_eq M) ≫ f)).val.app V x =
        f.val.app V ((toSheafify J
          (SheafOfModules.changeOfRingsPresheaf.{v, u, r}
            ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B)))
              M).presheaf).app V
                ((1 : (constantRing J B).obj.obj V)
                  ⊗ₜ[(constantRing J A).obj.obj V,(((constantSheaf J CommRingCat).map
                    (CommRingCat.ofHom (algebraMap A B))).hom.app V).hom] x)))
    {I : Type i} [Fintype I] (b : Module.Basis I A B) :
    let U := (restriction ((constantSheaf J CommRingCat).map
      (CommRingCat.ofHom (algebraMap A B)))).mapDerivedCategory
    let S := D.E.mapDerivedCategory
    let ι := fun (M : DerivedCategory (modules (constantRing J A))) (c : I) ↦
      a.onDerivedCategory.unit.app M ≫ U.map ((derived J B (b c)).app (S.obj M))
    (∀ M, ∃ q : I → (U.obj (S.obj M) ⟶ M),
      (∀ c d : I, ι M c ≫ q d =
        @ite _ (c = d) (Classical.propDecidable _) (𝟙 M) 0) ∧
      ∑ c : I, q c ≫ ι M c = 𝟙 _) ∧
    ∀ (K : CochainComplex (modules (constantRing J A)) ℤ) (c : I),
      ∃ k : K ⟶ ((restriction ((constantSheaf J CommRingCat).map
        (CommRingCat.ofHom (algebraMap A B)))).mapHomologicalComplex (.up ℤ)).obj
          ((D.E.mapHomologicalComplex (.up ℤ)).obj K),
        (∀ (n : ℤ) (V : Cᵒᵖ) (x : (K.X n).val.obj V),
          (k.f n).val.app V x =
            (eqToHom (D.obj_eq (K.X n)).symm).val.app V
              ((toSheafify J (SheafOfModules.changeOfRingsPresheaf.{v, u, r}
                ((constantSheaf J CommRingCat).map
                  (CommRingCat.ofHom (algebraMap A B))) (K.X n)).presheaf).app V
                    ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).app V (b c)
                      ⊗ₜ[(constantRing J A).obj.obj V,
                        (((constantSheaf J CommRingCat).map
                          (CommRingCat.ofHom (algebraMap A B))).hom.app V).hom] x))) ∧
        ι (DerivedCategory.Q.obj K) c ≫
            U.map (D.E.mapDerivedCategoryFactors.hom.app K) ≫
            (restriction ((constantSheaf J CommRingCat).map
              (CommRingCat.ofHom (algebraMap A B)))).mapDerivedCategoryFactors.hom.app
                ((D.E.mapHomologicalComplex (.up ℤ)).obj K) = DerivedCategory.Q.map k := by
  classical
  dsimp only
  let U := restriction ((constantSheaf J CommRingCat).map
    (CommRingCat.ofHom (algebraMap A B)))
  let Ec := D.E.mapHomologicalComplex (.up ℤ)
  let Uc := U.mapHomologicalComplex (.up ℤ)
  have hcol (M : modules (constantRing J A)) (c : I) (V : Cᵒᵖ)
      (x : M.val.obj V) :
      ((a.unit.app M ≫ U.map ((ordinary J B (b c)).app (D.E.obj M))).val.app V) x =
        (eqToHom (D.obj_eq M).symm).val.app V
          ((SheafOfModules.tensorUnit _ M).app V
            ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).app V (b c)
              ⊗ₜ[(constantRing J A).obj.obj V,
                (((constantSheaf J CommRingCat).map
                  (CommRingCat.ofHom (algebraMap A B))).hom.app V).hom] x)) := by
    have ht := ha M (D.E.obj M)
      (eqToHom (D.obj_eq M).symm ≫
        (ordinary J B (b c)).app (D.E.obj M)) V x
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Adjunction.homEquiv_unit] at ht
    change ((a.unit.app M ≫ U.map
      ((ordinary J B (b c)).app (D.E.obj M))).val.app V) x = _
    refine ht.trans ?_
    change ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).app V (b c)) •
      ((eqToHom (D.obj_eq M).symm).val.app V
        ((SheafOfModules.tensorUnit _ M).app V ((1 : (constantRing J B).obj.obj V)
          ⊗ₜ[(constantRing J A).obj.obj V,
            (((constantSheaf J CommRingCat).map
              (CommRingCat.ofHom (algebraMap A B))).hom.app V).hom] x))) = _
    rw [← ((eqToHom (D.obj_eq M).symm).val.app V).hom.map_smul]
    apply congrArg ((eqToHom (D.obj_eq M).symm).val.app V)
    let φ := (constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))
    let s : (constantRing J B).obj.obj V :=
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app V (b c)
    let η := (SheafOfModules.tensorUnit φ M).app V
    refine (η.hom.map_smul s _).symm.trans ?_
    apply congrArg η
    exact (ModuleCat.ExtendScalars.smul_tmul (φ.hom.app V).hom
      (s : (constantRing J B).obj.obj V) 1 x).trans (by simp only [mul_one]; rfl)
  constructor
  · let : HasSheafify J CommRingCat.{r} :=
      hasSheafifyEssentiallySmallSite.{v, r, u, r + 1, r} J CommRingCat.{r}
    let e := Fintype.equivFin I
    let b' := b.reindex e
    have hord (M : modules (constantRing J A)) :
        IsIso (biproduct.desc fun c : Fin (Fintype.card I) ↦
          a.unit.app M ≫ U.map ((ordinary J B (b' c)).app (D.E.obj M))) := by
      let t := U.mapIso (eqToIso (D.obj_eq M)) ≪≫ (tensorCoords J A B _ b').app M
      have ht : (biproduct.desc fun c : Fin (Fintype.card I) ↦
          a.unit.app M ≫ U.map ((ordinary J B (b' c)).app (D.E.obj M))) ≫ t.hom =
          (biproduct.isoProduct (fun _ : Fin (Fintype.card I) ↦ M)).hom := by
        apply biproduct.hom_ext'
        intro c
        apply Pi.hom_ext
        intro d
        dsimp only [Functor.pi', Functor.id_obj]
        simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.isoProduct_hom,
          Pi.lift_π, biproduct.ι_π]
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro V
        apply ModuleCat.hom_ext
        ext x
        have hc := hcol M (e.symm c) V x
        simp only [b', Module.Basis.reindex_apply]
        change (t.hom ≫ Pi.π (fun _ : Fin (Fintype.card I) ↦ M) d).val.app V
          (((a.unit.app M ≫ U.map ((ordinary J B (b (e.symm c))).app
            (D.E.obj M))).val.app V) x) = _
        rw [hc]
        change (Pi.π (fun _ : Fin (Fintype.card I) ↦ M) d).val.app V
          (((tensorCoords J A B _ b').hom.app M).val.app V
            (((eqToHom (D.obj_eq M)).val.app V)
              (((eqToHom (D.obj_eq M).symm).val.app V) _))) = _
        have heq (z : (SheafOfModules.changeOfRings _ M).val.obj V) :
            (eqToHom (D.obj_eq M)).val.app V
              ((eqToHom (D.obj_eq M).symm).val.app V z) = z := by
          exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.val.app V)
            (eqToHom_trans (D.obj_eq M).symm (D.obj_eq M))) z
        rw [heq]
        refine (tensorCoords_constant J A B _ b' M V (b (e.symm c)) x d).trans ?_
        rw [show b (e.symm c) = b' c by simp only [b', Module.Basis.reindex_apply]]
        simp only [Module.Basis.equivFun_self]
        split_ifs with h
        · subst d
          simp
        · simp
          rfl
      have : IsIso ((biproduct.desc fun c : Fin (Fintype.card I) ↦
          a.unit.app M ≫ U.map ((ordinary J B (b' c)).app (D.E.obj M))) ≫ t.hom) := by
        rw [ht]
        infer_instance
      exact IsIso.of_isIso_comp_right _ t.hom
    intro M
    let f := biproduct.desc fun c : Fin (Fintype.card I) ↦
      a.onDerivedCategory.unit.app M ≫ U.mapDerivedCategory.map
        ((derived J B (b' c)).app (D.E.mapDerivedCategory.obj M))
    have : IsIso f := localized_basis_iso J A B D.E U a _ b' hord M
    refine ⟨fun c ↦ inv f ≫ biproduct.π _ (e c), ?_, ?_⟩
    · intro c d
      have hf : a.onDerivedCategory.unit.app M ≫ U.mapDerivedCategory.map
          ((derived J B (b c)).app (D.E.mapDerivedCategory.obj M)) =
          biproduct.ι (fun _ : Fin (Fintype.card I) ↦ M) (e c) ≫ f := by
        simp [f, b', Module.Basis.reindex_apply, e]
      rw [hf]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      by_cases h : c = d
      · subst d
        simp
      · simp [h, e.injective.ne h]
    · have hf (c : I) : a.onDerivedCategory.unit.app M ≫ U.mapDerivedCategory.map
          ((derived J B (b c)).app (D.E.mapDerivedCategory.obj M)) =
          biproduct.ι (fun _ : Fin (Fintype.card I) ↦ M) (e c) ≫ f := by
        simp [f, b', Module.Basis.reindex_apply, e]
      change (∑ c : I, (inv f ≫ biproduct.π (fun _ : Fin (Fintype.card I) ↦ M) (e c)) ≫
        (a.onDerivedCategory.unit.app M ≫ U.mapDerivedCategory.map
          ((derived J B (b c)).app (D.E.mapDerivedCategory.obj M)))) = 𝟙 _
      simp_rw [hf, Category.assoc]
      rw [← Preadditive.comp_sum]
      simp_rw [← Category.assoc]
      rw [← Preadditive.sum_comp]
      rw [e.sum_comp (fun j : Fin (Fintype.card I) ↦
        biproduct.π (fun _ : Fin (Fintype.card I) ↦ M) j ≫
          biproduct.ι (fun _ : Fin (Fintype.card I) ↦ M) j), biproduct.total]
      simp
  · intro K c
    let k : K ⟶ Uc.obj (Ec.obj K) :=
      (a.mapHomologicalComplex (.up ℤ)).unit.app K ≫
        Uc.map ((cochain J B (b c)).app (Ec.obj K))
    refine ⟨k, ?_, ?_⟩
    · intro n V x
      exact hcol (K.X n) c V x
    · have hu := localized_unit a K
      have hs := (derived J B (b c)).naturality (D.E.mapDerivedCategoryFactors.hom.app K)
      dsimp only [Functor.comp_obj, Functor.id_map] at hs
      have hn := U.mapDerivedCategoryFactors.hom.naturality
        ((cochain J B (b c)).app (Ec.obj K))
      dsimp only [Functor.comp_map] at hn
      change (a.onDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
        U.mapDerivedCategory.map ((derived J B (b c)).app
          (D.E.mapDerivedCategory.obj (DerivedCategory.Q.obj K)))) ≫
        U.mapDerivedCategory.map (D.E.mapDerivedCategoryFactors.hom.app K) ≫
        U.mapDerivedCategoryFactors.hom.app (Ec.obj K) = _
      simp only [Category.assoc]
      rw [← U.mapDerivedCategory.map_comp_assoc, ← hs, U.mapDerivedCategory.map_comp,
        Category.assoc, derived_app_Q, hn]
      have hmap := congrArg (fun f ↦ f ≫ DerivedCategory.Q.map
          ((U.mapHomologicalComplex (.up ℤ)).map
            ((cochain J B (b c)).app (Ec.obj K)))) hu
      have hm : (NatTrans.mapHomologicalComplex a.unit (.up ℤ)).app K =
          (a.mapHomologicalComplex (.up ℤ)).unit.app K := by
        ext n
        rfl
      rw [hm] at hmap
      simpa only [k, Uc, Ec, Functor.map_comp, Category.assoc] using hmap

end CategoryTheory.ConstantModuleScalar
