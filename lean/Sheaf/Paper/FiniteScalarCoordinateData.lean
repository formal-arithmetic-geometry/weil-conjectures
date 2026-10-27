module

public import Sheaf.Paper.FinitePowerComplex
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
import all Sheaf.Paper.FiniteFreeScalarExtension
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Normalized finite scalar coordinates on modules and strict towers

Source: Stacks 03CY, 03DB, 03EK, 06YY and 0940; Bhatt--Scholze, Lemma 3.4.12.
(blueprint: def-pur-finite-scalar-coordinate-data).

These are canonical coordinate constructions used in the proper biproduct formula.
They do not replace the proved finite-basis theorem on complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
namespace WeilConjectures.PurStrictScalar
open AlgebraicGeometry.ProEtale.StrictTower

namespace OrdinaryProof
open SheafOfModules
universe v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  {R S : Sheaf J CommRingCat.{u}}

attribute [local irreducible] CategoryTheory.Limits.limit
set_option backward.defeqAttrib.useBackward true

set_option hygiene false in
local notation "𝓡" T => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T
set_option hygiene false in
local notation "𝓻" φ => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ

private theorem coordinatesForFunctor (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ unit (𝓡 R)) ≅
      (restrictScalars (𝓻 a)).obj (unit (𝓡 S)))
    (E : SheafOfModules.{u} (𝓡 R) ⥤ SheafOfModules.{u} (𝓡 S))
    (h : ∀ M, E.obj M = changeOfRings.{v, u, u} a M)
    (hmap : ∀ {M N} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ changeOfRingsHom a M f ≫ eqToHom (h N).symm) :
    ∃! β : E ⋙ restrictScalars (𝓻 a) ≅ finitePowerFunctor d,
      ∀ (M : SheafOfModules.{u} (𝓡 R)) (V : Cᵒᵖ) (s : S.obj.obj V)
        (x : M.val.obj V) (j : Fin d),
        ((β.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) j).val.app V)
          ((eqToHom (h M).symm).val.app V
            ((toSheafify J (changeOfRingsPresheaf.{v, u, u} a M).presheaf).app V
              (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x))) =
          ((e.inv ≫ Pi.π (fun _ : Fin d ↦ unit (𝓡 R)) j).val.app V s) • x := by
  let U := restrictScalars (𝓻 a)
  let c (M : SheafOfModules.{u} (𝓡 R)) := U.mapIso (eqToIso (h M)) ≪≫
    scalarExtensionIso a d e M
  let β : E ⋙ U ≅ finitePowerFunctor d := NatIso.ofComponents c (by
    intro M N f
    have ht : U.map (E.map f) ≫ U.map (eqToHom (h N)) =
        U.map (eqToHom (h M)) ≫ U.map (SheafOfModules.changeOfRingsHom a M f) := by
      rw [← U.map_comp, ← U.map_comp, hmap]
      simp
    change U.map (E.map f) ≫ (U.map (eqToHom (h N)) ≫ _) =
      (U.map (eqToHom (h M)) ≫ _) ≫ Limits.Pi.map (fun _ : Fin d ↦ f)
    rw [← Category.assoc, ht, Category.assoc]
    exact (congrArg (fun f ↦ U.map (eqToHom (h M)) ≫ f)
      (scalarExtensionIso_naturality a d e f)).trans
        (Category.assoc _ _ _).symm)
  have hβ : ∀ (M : SheafOfModules.{u} (𝓡 R)) (V : Cᵒᵖ) (s : S.obj.obj V)
      (x : M.val.obj V) (j : Fin d),
      ((β.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) j).val.app V)
        (((eqToHom (h M).symm).val.app V
          ((toSheafify J (changeOfRingsPresheaf.{v, u, u} a M).presheaf).app V
            (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)))) =
      ((e.inv ≫ Pi.π (fun _ : Fin d ↦ SheafOfModules.unit
        (𝓡 R)) j).val.app V s) • x := by
    intro M V s x j
    have ht : (U.map (eqToHom (h M))).val.app V
        (((eqToHom (h M).symm).val.app V
          ((toSheafify J (changeOfRingsPresheaf.{v, u, u} a M).presheaf).app V
            (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)))) =
        (toSheafify J
          (changeOfRingsPresheaf.{v, u, u} a M).presheaf).app V
            (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x) := by
      change (eqToHom (h M)).val.app V ((eqToHom (h M).symm).val.app V _) = _
      have heq : eqToHom (h M).symm ≫ eqToHom (h M) = 𝟙 _ := by simp
      have hh := congrArg (fun f ↦ f.val.app V) heq
      have hh' : (eqToHom (h M).symm).val.app V ≫
          (eqToHom (h M)).val.app V = 𝟙 _ := hh
      exact (ModuleCat.comp_apply _ _ _).symm.trans
        (by
          rw [hh']
          rfl)
    change ((scalarExtensionIso a d e M).hom ≫
      Pi.π (fun _ : Fin d ↦ M) j).val.app V
        ((U.map (eqToHom (h M))).val.app V (((eqToHom (h M).symm).val.app V
          ((toSheafify J (changeOfRingsPresheaf.{v, u, u} a M).presheaf).app V
            (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x))))) = _
    rw [ht]
    exact scalarExtensionIso_tmul a d e M V s x j
  refine ⟨β, hβ, ?_⟩
  intro γ hγ
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply Pi.hom_ext
  intro j
  let v := U.map (eqToHom (h M).symm)
  have : IsIso v := by dsimp [v]; infer_instance
  apply (cancel_epi v).mp
  apply SheafOfModules.scalarExtension_hom_ext_of_basis a d e M M
  ext V z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul s x =>
    have hh := (hγ M V s x j).trans (hβ M V s x j).symm
    unfold SheafOfModules.tensorUnit
    exact hh


end OrdinaryProof

attribute [local irreducible] CategoryTheory.Limits.limit

private theorem scalar_hom_ext (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S)))
    (M N : pbcModules W R)
    (f g : (pbcRestrict a).obj ((pbcExtend a).obj M) ⟶ N)
    (ht : ∀ (V : W.ProEtᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V),
      f.val.app V (pbcTensorSection a M V s x) =
        g.val.app V (pbcTensorSection a M V s x)) : f = g := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} := inferInstance
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance
  let h : (pbcExtend a).obj M = SheafOfModules.changeOfRings a M :=
    (pbcExtensionExistence a).choose_spec.choose M
  let v := (pbcRestrict a).map (eqToHom h.symm)
  have : IsIso v := by dsimp [v]; infer_instance
  apply (cancel_epi v).mp
  apply SheafOfModules.scalarExtension_hom_ext_of_basis a d e M N
  ext V z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul s x =>
    have hh := ht V s x
    change f.val.app V ((eqToHom h.symm).val.app V _) =
      g.val.app V ((eqToHom h.symm).val.app V _) at hh
    unfold SheafOfModules.tensorUnit
    exact hh

/-- Finite products of strict towers, computed pointwise.
Source: finite limits of functor categories
(blueprint: def-pur-finite-scalar-coordinate-data). -/
instance scalarTower_products (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :
    HasFiniteProducts (pbcTowers W R) := inferInstance

/-- Finite products in the derived strict-tower category.
Source: finite biproducts in an abelian category
(blueprint: def-pur-finite-scalar-coordinate-data). -/
instance scalarTowerDerived_products (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :
    HasFiniteProducts (DerivedCategory (pbcTowers W R)) := inferInstance

/-- The ordinary coordinate isomorphism is uniquely fixed on all local tensors.
Source: Stacks 03CY, 03EK (blueprint: def-pur-finite-scalar-coordinate-data).
Proof: the finite-basis cochain calculation in degree zero yields the coordinate maps
and their inverses. Its formula makes them natural in every module and determines
them uniquely by the sheafified balanced tensor universal property. -/
theorem ordinaryCoordinates_existsUnique (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    ∃! β : pbcExtend a ⋙ pbcRestrict a ≅ finitePowerFunctor d,
      ∀ (M : pbcModules W R) (V : W.ProEtᵒᵖ) (s : S.obj.obj V)
        (x : M.val.obj V) (j : Fin d),
        ((β.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) j).val.app V)
            (pbcTensorSection a M V s x) =
          ((e.inv ≫ Pi.π (fun _ : Fin d ↦ SheafOfModules.unit
            ((adicLisseForget W).obj R)) j).val.app V s) • x := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} := inferInstance
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance
  exact OrdinaryProof.coordinatesForFunctor a d e (pbcExtend a)
    (pbcExtensionExistence a).choose_spec.choose
    (pbcExtensionExistence a).choose_spec.choose_spec.choose

/-- The unique ordinary finite-basis coordinates, with no independent choices.
Source: Stacks 03EK (blueprint: def-pur-finite-scalar-coordinate-data). -/
def ordinaryCoordinates (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    pbcExtend a ⋙ pbcRestrict a ≅ finitePowerFunctor d :=
  (ordinaryCoordinates_existsUnique W a d e).exists.choose

attribute [local irreducible] reductionChange reductionDerivedChange

/-- A finite free coefficient extension is exact on all module sheaves.
Source: Stacks 03CY (blueprint: def-pur-finite-scalar-coordinate-data).
Proof: the ordinary coordinate comparison identifies restricted extension with a
finite power. Restriction is exact and reflects exactness because its underlying
abelian sheaf is unchanged. Finite powers in the abelian category are exact. -/
theorem finiteScalar_exact (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    PreservesFiniteLimits (pbcExtend a) ∧ PreservesFiniteColimits (pbcExtend a) := by
  have : (pbcRestrict a).ReflectsIsomorphisms :=
    (proEtaleRingRestrictScalars_properties a).2.2
  have : PreservesFiniteLimits (finitePowerFunctor (A := pbcModules W R) d) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits (finitePowerFunctor (A := pbcModules W R) d) :=
    inferInstance
  have : PreservesFiniteLimits (pbcExtend a ⋙ pbcRestrict a) :=
    preservesFiniteLimits_of_natIso (ordinaryCoordinates W a d e).symm
  have : PreservesFiniteColimits (pbcExtend a ⋙ pbcRestrict a) :=
    preservesFiniteColimits_of_natIso (ordinaryCoordinates W a d e).symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves (pbcExtend a) (pbcRestrict a),
    preservesFiniteColimits_of_reflects_of_preserves (pbcExtend a) (pbcRestrict a)⟩

@[irreducible] private def complexPowerIso {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (d : ℕ) :
    (finitePowerFunctor (A := A) d).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ finitePowerFunctor d :=
  NatIso.ofComponents (fun P ↦ DerivedCategory.Q.mapIso (finitePowerComplexIso d P) ≪≫
    PreservesProduct.iso DerivedCategory.Q (fun _ : Fin d ↦ P)) (by
    intro P P' f
    apply Pi.hom_ext
    intro j
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
      PreservesProduct.iso_hom, piComparison_comp_π, finitePowerFunctor,
      Functor.comp_map, Pi.map_π, piComparison_comp_π_assoc]
    simp only [← Functor.map_comp]
    congr 1
    apply HomologicalComplex.Hom.ext
    funext k
    simp only [HomologicalComplex.comp_f]
    have hp := finitePowerComplexIso_projection d P j k
    have hp' := finitePowerComplexIso_projection d P' j k
    simp only [HomologicalComplex.comp_f] at hp hp'
    rw [hp', ← Category.assoc, hp]
    change Limits.Pi.map (fun _ : Fin d ↦ f.f k) ≫ Pi.π _ j = _
    exact Pi.map_π (fun _ : Fin d ↦ f.f k) j)

private theorem localizedCoordinates {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (E : A ⥤ B) (U : B ⥤ A) [E.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (F : DerivedCategory A ⥤ DerivedCategory B)
    (c : DerivedCategory.Q ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (d : ℕ) (b : E ⋙ U ≅ finitePowerFunctor d) :
    ∃! κ : F ⋙ U.mapDerivedCategory ≅ finitePowerFunctor d,
      ∀ P : CochainComplex A ℤ,
        κ.hom.app (DerivedCategory.Q.obj P) =
          U.mapDerivedCategory.map (c.hom.app P) ≫
            U.mapDerivedCategoryFactors.hom.app
              ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P) ≫
            DerivedCategory.Q.map (finitePowerComplexIso d P).hom ≫
            (PreservesProduct.iso DerivedCategory.Q (fun _ : Fin d ↦ P)).hom := by
  let Q := DerivedCategory.Q (C := A)
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let t : Q ⋙ (F ⋙ U.mapDerivedCategory) ≅ Q ⋙ finitePowerFunctor d :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight c _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ U.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (NatIso.mapHomologicalComplex b (.up ℤ)) _ ≪≫
      complexPowerIso d
  let κ := Localization.liftNatIso Q W _ _ (F ⋙ U.mapDerivedCategory)
    (finitePowerFunctor d) t
  have hk (P : CochainComplex A ℤ) : κ.hom.app (Q.obj P) = t.hom.app P := by
    simp only [κ, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
      Localization.Lifting.compLeft_iso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      Category.id_comp, Category.comp_id]
  refine ⟨κ, ?_, ?_⟩
  · intro P
    rw [hk]
    simp only [t, Iso.trans_hom, Iso.symm_hom, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.comp_app, Category.id_comp, complexPowerIso,
      NatIso.ofComponents_hom_app, Functor.mapIso_hom]
  · intro κ' hκ'
    apply Iso.ext
    apply Localization.natTrans_ext Q W
    intro P
    rw [hk]
    simpa only [t, Iso.trans_hom, Iso.symm_hom, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.comp_app, Category.id_comp, Category.comp_id, complexPowerIso,
      NatIso.ofComponents_hom_app, Functor.mapIso_hom, Category.assoc] using hκ' P

@[irreducible] private def exactScalarCochainIso {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (F : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ F ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [F.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ))] :
    DerivedCategory.Q ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  have hinv : (HomotopyCategory.quasiIso A (.up ℤ)).IsInvertedBy
      (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _ E.mapDerivedCategoryFactorsh).mp
      ((Localization.inverts DerivedCategory.Qh _).of_comp _ _ E.mapDerivedCategory)
  have := Functor.isIso_of_isLeftDerivedFunctor_of_inverts F ε hinv
  exact Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A).symm F ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.quotient A (.up ℤ)) (asIso ε) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)

/-- The derived coordinates are uniquely normalized on every cochain counit.
Source: Stacks 06YY, 03DB (blueprint: def-pur-finite-scalar-coordinate-data).
Proof: finite freeness makes ordinary extension exact. Localize the ordinary
coordinates and use the universal scalar counit to identify its derived extension.
The exact localization preserves finite products. This yields the displayed
normalization, which determines the natural transformation by universality. -/
theorem derivedCoordinates_existsUnique (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    ∃! κ : pbcDerivedExtend a ⋙ pbcDerivedRestrict a ≅ finitePowerFunctor d,
      ∀ P : CochainComplex (pbcModules W R) ℤ,
        κ.hom.app (DerivedCategory.Q.obj P) =
          (pbcDerivedRestrict a).map (pbcComplexCounit a P) ≫
            (pbcRestrict a).mapDerivedCategoryFactors.hom.app
              (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryCoordinates W a d e) (.up ℤ)).hom.app P) ≫
            DerivedCategory.Q.map (finitePowerComplexIso d P).hom ≫
            (PreservesProduct.iso DerivedCategory.Q (fun _ : Fin d ↦ P)).hom := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} := inferInstance
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance
  have := (finiteScalar_exact W a d e).1
  have := (finiteScalar_exact W a d e).2
  have := pbcDerivedExtension_universal a
  let c := exactScalarCochainIso (A := pbcModules W R) (B := pbcModules W S)
    (pbcExtend a) (pbcDerivedExtend a) (pbcExtensionCounit a)
  have hc (P : CochainComplex (pbcModules W R) ℤ) :
      c.hom.app P = pbcComplexCounit a P := by
    simp only [c, exactScalarCochainIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      asIso_hom, Category.id_comp, pbcComplexCounit]
  simpa only [hc, pbcDerivedRestrict] using
    localizedCoordinates (A := pbcModules W R) (B := pbcModules W S)
    (pbcExtend a) (pbcRestrict a)
    (pbcDerivedExtend a) c d (ordinaryCoordinates W a d e)

/-- Finite-basis derived coordinates with the specified universal counit.
Source: Stacks 06YY (blueprint: def-pur-finite-scalar-coordinate-data). -/
def derivedCoordinates (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    pbcDerivedExtend a ⋙ pbcDerivedRestrict a ≅ finitePowerFunctor d :=
  (derivedCoordinates_existsUnique W a d e).exists.choose

@[irreducible] private def towerPowerIso {A : Type*} [Category A] [HasFiniteProducts A] (d : ℕ) :
    (Functor.whiskeringRight ℕᵒᵖ A A).obj (finitePowerFunctor d) ≅
      finitePowerFunctor d :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents
    (fun n ↦ (piObjIso (fun _ : Fin d ↦ M) n).symm) (by
      intro n m f
      apply (cancel_mono (piObjIso (fun _ : Fin d ↦ M) m).hom).mp
      apply Pi.hom_ext
      intro j
      simp only [Category.assoc, Iso.symm_hom]
      change (Limits.Pi.map (fun _ : Fin d ↦ M.map f)) ≫
          (piObjIso (fun _ : Fin d ↦ M) m).inv ≫
            (piObjIso (fun _ : Fin d ↦ M) m).hom ≫ Pi.π _ j =
        (piObjIso (fun _ : Fin d ↦ M) n).inv ≫
          (∏ᶜ fun _ : Fin d ↦ M).map f ≫
            (piObjIso (fun _ : Fin d ↦ M) m).hom ≫ Pi.π _ j
      simp only [piObjIso_hom_comp_π]
      rw [piObjIso_inv_comp_π, Pi.map_π,
        (Pi.π (fun _ : Fin d ↦ M) j).naturality f,
        ← Category.assoc, piObjIso_inv_comp_π])) (by
    intro M N f
    apply NatTrans.ext
    funext n
    apply (cancel_mono (piObjIso (fun _ : Fin d ↦ N) n).hom).mp
    apply Pi.hom_ext
    intro j
    simp only [NatTrans.comp_app, NatIso.ofComponents_hom_app, Iso.symm_hom,
      Category.assoc]
    change Limits.Pi.map (fun _ : Fin d ↦ f.app n) ≫
        (piObjIso (fun _ : Fin d ↦ N) n).inv ≫
          (piObjIso (fun _ : Fin d ↦ N) n).hom ≫ Pi.π _ j =
      (piObjIso (fun _ : Fin d ↦ M) n).inv ≫
        (Limits.Pi.map (fun _ : Fin d ↦ f)).app n ≫
          (piObjIso (fun _ : Fin d ↦ N) n).hom ≫ Pi.π _ j
    simp only [piObjIso_hom_comp_π]
    rw [piObjIso_inv_comp_π, Pi.map_π]
    have h := congrArg (fun g ↦ g.app n) (Pi.map_π (fun _ : Fin d ↦ f) j)
    simp only [NatTrans.comp_app] at h
    rw [h, piObjIso_inv_comp_π_assoc])

@[irreducible] private def towerCoordinateIso {A B : Type*} [Category A] [Category B]
    [HasFiniteProducts A] {E : A ⥤ B} {U : B ⥤ A} (d : ℕ)
    (b : E ⋙ U ≅ finitePowerFunctor d) :
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj E ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj U ≅ finitePowerFunctor d :=
  (NatIso.ofComponents (fun M ↦
    (NatIso.ofComponents (fun n ↦ b.app (M.obj n)) (by
      intro n m f
      exact b.hom.naturality (M.map f)) :
        (M ⋙ E) ⋙ U ≅ M ⋙ finitePowerFunctor d)) (by
    intro M N f
    apply NatTrans.ext
    funext n
    exact b.hom.naturality (f.app n)) :
      (Functor.whiskeringRight ℕᵒᵖ A B).obj E ⋙
        (Functor.whiskeringRight ℕᵒᵖ B A).obj U ≅
          (Functor.whiskeringRight ℕᵒᵖ A A).obj (finitePowerFunctor d)) ≪≫ towerPowerIso d

private theorem towerCoordinateIso_projection {A B : Type*} [Category A] [Category B]
    [HasFiniteProducts A] {E : A ⥤ B} {U : B ⥤ A} (d : ℕ)
    (b : E ⋙ U ≅ finitePowerFunctor d) (M : ℕᵒᵖ ⥤ A) (n : ℕᵒᵖ) (j : Fin d) :
    (((towerCoordinateIso d b).hom.app M) ≫ Pi.π (fun _ : Fin d ↦ M) j).app n =
      b.hom.app (M.obj n) ≫ Pi.π (fun _ : Fin d ↦ M.obj n) j := by
  unfold towerCoordinateIso towerPowerIso
  change (b.hom.app (M.obj n) ≫ (piObjIso (fun _ : Fin d ↦ M) n).inv) ≫
    (Pi.π (fun _ : Fin d ↦ M) j).app n = _
  rw [Category.assoc, piObjIso_inv_comp_π]

/-- Ordinary finite-basis coordinates on entire strict diagrams are uniquely fixed
by the same tensor formula at every index.
Source: Stacks 03EK, 0940 (blueprint: def-pur-finite-scalar-coordinate-data).
Proof: apply the ordinary coordinate comparison at every index. Its naturality
makes it commute with all transitions, and finite products of diagrams are
pointwise. The displayed formula determines each sheaf map, hence the diagram map. -/
theorem ordinaryTowerCoordinates_existsUnique (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    ∃! β : (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a) ⋙
          (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a) ≅ finitePowerFunctor d,
      ∀ (M : pbcTowers W R) (n : ℕ) (V : W.ProEtᵒᵖ) (s : S.obj.obj V)
        (x : (M.obj (op n)).val.obj V) (j : Fin d),
        (((β.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) j).app (op n)).val.app V)
            (pbcTensorSection a (M.obj (op n)) V s x) =
          ((e.inv ≫ Pi.π (fun _ : Fin d ↦ SheafOfModules.unit
            ((adicLisseForget W).obj R)) j).val.app V s) • x := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} := inferInstance
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance
  let β := towerCoordinateIso d (ordinaryCoordinates W a d e)
  have hb := (ordinaryCoordinates_existsUnique W a d e).exists.choose_spec
  have hβ : ∀ (M : pbcTowers W R) (n : ℕ) (V : W.ProEtᵒᵖ) (s : S.obj.obj V)
      (x : (M.obj (op n)).val.obj V) (j : Fin d),
      (((β.hom.app M ≫ Pi.π (fun _ : Fin d ↦ M) j).app (op n)).val.app V)
        (pbcTensorSection a (M.obj (op n)) V s x) =
      ((e.inv ≫ Pi.π (fun _ : Fin d ↦ SheafOfModules.unit
        ((adicLisseForget W).obj R)) j).val.app V s) • x := by
    intro M n V s x j
    rw [towerCoordinateIso_projection]
    exact hb (M.obj (op n)) V s x j
  refine ⟨β, hβ, ?_⟩
  intro γ hγ
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  apply (cancel_mono (piObjIso (fun _ : Fin d ↦ M) n).hom).mp
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, piObjIso_hom_comp_π]
  apply scalar_hom_ext W a d e (M.obj n) (M.obj n)
  intro V s x
  exact (hγ M (unop n) V s x j).trans (hβ M (unop n) V s x j).symm

/-- The uniquely normalized ordinary coordinates of strict diagrams.
Source: Stacks 03EK, 0940 (blueprint: def-pur-finite-scalar-coordinate-data). -/
def ordinaryTowerCoordinates (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a) ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a) ≅ finitePowerFunctor d :=
  (ordinaryTowerCoordinates_existsUnique W a d e).exists.choose

/-- Finite limits of strict coefficient restriction are computed pointwise.
Source: Stacks 03DA, 0940 (blueprint: def-pur-finite-scalar-coordinate-data). -/
instance scalarTowerRestriction_limits (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- Finite colimits of strict coefficient restriction are computed pointwise.
Source: Stacks 03DA, 0940 (blueprint: def-pur-finite-scalar-coordinate-data). -/
instance scalarTowerRestriction_colimits (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)) := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} := inferInstance
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance
  exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- Scalar extension on diagrams is additive, pointwise.
Source: additivity of scalar tensor (blueprint: def-pur-finite-scalar-coordinate-data). -/
instance scalarTowerExtension_additive (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)).Additive := inferInstance

/-- Scalar restriction on diagrams is additive, pointwise.
Source: additivity of scalar restriction
(blueprint: def-pur-finite-scalar-coordinate-data). -/
instance scalarTowerRestriction_additive (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)).Additive := inferInstance

/-- Exactness of finite-free extension on strict towers.
Source: finite limits and colimits in functor categories are pointwise
(blueprint: def-pur-finite-scalar-coordinate-data). -/
theorem scalarTowerExtension_exact (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)) ∧
      PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)) := by
  have := (finiteScalar_exact W a d e).1
  have := (finiteScalar_exact W a d e).2
  exact ⟨⟨fun _ _ _ ↦ inferInstance⟩, ⟨fun _ _ _ ↦ inferInstance⟩⟩

/-- Exact localization of ordinary finite-free tensor on strict diagrams. The
basis is used only to supply exactness, whose proof is propositionally irrelevant.
Source: Stacks 03CY, 0940 (blueprint: def-pur-finite-scalar-coordinate-data). -/
def finiteScalarTower (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    DerivedCategory (pbcTowers W R) ⥤ DerivedCategory (pbcTowers W S) :=
  have := (scalarTowerExtension_exact W a d e).1
  have := (scalarTowerExtension_exact W a d e).2
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)).mapDerivedCategory

/-- The canonical exact-localization factor on every whole-diagram cochain.
Source: Stacks 06YY, 0940 (blueprint: def-pur-finite-scalar-coordinate-data). -/
def finiteScalarTowerCounit (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S)))
    (P : CochainComplex (pbcTowers W R) ℤ) :
    (finiteScalarTower W a d e).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)).mapHomologicalComplex
          (.up ℤ)).obj P) :=
  have := (scalarTowerExtension_exact W a d e).1
  have := (scalarTowerExtension_exact W a d e).2
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)).mapDerivedCategoryFactors.hom.app P

-- Keep the exact-localization construction folded while elaborating its normalization type.
attribute [local irreducible] finiteScalarTower finiteScalarTowerCounit
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The whole-cochain normalization predicate, named to share its expression.
Source: Stacks 03DB and 0940 (blueprint: def-pur-finite-scalar-coordinate-data). -/
def derivedTowerCoordinateNormalization (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S)))
    (κ : finiteScalarTower W a d e ⋙
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)).mapDerivedCategory ≅
          finitePowerFunctor d) : Prop :=
    ∀ P : CochainComplex (pbcTowers W R) ℤ,
      κ.hom.app (DerivedCategory.Q.obj P) =
        (((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)).mapDerivedCategory).map
            (finiteScalarTowerCounit W a d e P) ≫
          ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            (pbcRestrict a)).mapDerivedCategoryFactors.hom.app
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)).mapHomologicalComplex
              (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (ordinaryTowerCoordinates W a d e) (.up ℤ)).hom.app P) ≫
          DerivedCategory.Q.map (finitePowerComplexIso d P).hom ≫
          (PreservesProduct.iso DerivedCategory.Q (fun _ : Fin d ↦ P)).hom

/-- Derived strict-tower coordinates are fixed before finite evaluation, on every
whole cochain factor of exact tensor and exact restriction.
Source: Stacks 03DB, 0940 (blueprint: def-pur-finite-scalar-coordinate-data).
Proof: localize the ordinary natural coordinate comparison of entire diagrams.
Compose its exact-localization factors with the finite-power complex isomorphism
and the finite-product comparison of Q. Localization's universal property gives
uniqueness of the displayed whole-diagram natural transformation. -/
theorem derivedTowerCoordinates_existsUnique (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    ∃! κ : finiteScalarTower W a d e ⋙
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)).mapDerivedCategory ≅
          finitePowerFunctor d,
      ∀ P : CochainComplex (pbcTowers W R) ℤ,
        κ.hom.app (DerivedCategory.Q.obj P) =
          (((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)).mapDerivedCategory).map
              (finiteScalarTowerCounit W a d e P) ≫
            ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
              (pbcRestrict a)).mapDerivedCategoryFactors.hom.app
              ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)).mapHomologicalComplex
                (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
              (ordinaryTowerCoordinates W a d e) (.up ℤ)).hom.app P) ≫
            DerivedCategory.Q.map (finitePowerComplexIso d P).hom ≫
            (PreservesProduct.iso DerivedCategory.Q (fun _ : Fin d ↦ P)).hom := by
  unfold finiteScalarTower finiteScalarTowerCounit
  let E : pbcTowers W R ⥤ pbcTowers W S :=
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcExtend a)
  let U : pbcTowers W S ⥤ pbcTowers W R :=
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)
  have : PreservesFiniteLimits E := (scalarTowerExtension_exact W a d e).1
  have : PreservesFiniteColimits E := (scalarTowerExtension_exact W a d e).2
  exact localizedCoordinates (A := pbcTowers W R) (B := pbcTowers W S)
    E U E.mapDerivedCategory E.mapDerivedCategoryFactors d
    (ordinaryTowerCoordinates W a d e)

/-- Uniqueness with the named cochain-normalization predicate.
Source: Stacks 03DB and 0940 (blueprint: def-pur-finite-scalar-coordinate-data). -/
theorem derivedTowerCoordinates_normalized (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    ∃! κ : finiteScalarTower W a d e ⋙
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)).mapDerivedCategory ≅
          finitePowerFunctor d,
      derivedTowerCoordinateNormalization W a d e κ := by
  exact derivedTowerCoordinates_existsUnique W a d e

/-- The unique whole-derived-tower basis coordinates.
Source: Stacks 03DB, 0940 (blueprint: def-pur-finite-scalar-coordinate-data). -/
def derivedTowerCoordinates (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj R)) ≅
      (pbcRestrict a).obj (SheafOfModules.unit ((adicLisseForget W).obj S))) :
    finiteScalarTower W a d e ⋙
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcRestrict a)).mapDerivedCategory ≅
        finitePowerFunctor d :=
  (derivedTowerCoordinates_normalized W a d e).choose

end WeilConjectures.PurStrictScalar
