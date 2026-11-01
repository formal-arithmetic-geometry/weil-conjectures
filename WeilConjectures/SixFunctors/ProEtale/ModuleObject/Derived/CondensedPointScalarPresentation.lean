/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarLimits
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison

/-! # Ordinary scalar presentation of the point copower functor -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct IntermediateField

universe v
namespace CategoryTheory
variable (R : Type v) [Ring R] (M : Mod Ab.{v} (AddCommGrpCat.of R))

private noncomputable def internalToModule : Mod Ab.{v} (AddCommGrpCat.of R) ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R M.X
  map {M N} f := ModuleCat.ofHom
    { toFun := f.hom
      map_add' := map_add f.hom.hom
      map_smul' := fun a m ↦ by
        have h := congrArg (fun g ↦ g.hom (a ⊗ₜ[ℤ] m))
          (IsModHom.smul_hom (A := AddCommGrpCat.of R) (f := f.hom))
        change f.hom.hom ((γ[AddCommGrpCat.of R,M.X]).hom (a ⊗ₜ[ℤ] m)) =
          (γ[AddCommGrpCat.of R,N.X]).hom (a ⊗ₜ[ℤ] f.hom.hom m)
        change f.hom.hom ((γ[AddCommGrpCat.of R,M.X]).hom (a ⊗ₜ[ℤ] m)) =
          (γ[AddCommGrpCat.of R,N.X]).hom (a ⊗ₜ[ℤ] f.hom.hom m) at h
        exact h }
  map_id M := rfl
  map_comp f g := rfl

private noncomputable def ordinaryAct (N : ModuleCat.{v} R) :
    AddCommGrpCat.of R ⊗ AddCommGrpCat.of N ⟶ AddCommGrpCat.of N :=
  AddCommGrpCat.ofHom (TensorProduct.lift (LinearMap.mk₂ ℤ (fun (a : R) (m : N) ↦ a • m)
    (fun a b m ↦ add_smul a b m)
    (fun c a m ↦ smul_assoc c a m)
    (fun a m n ↦ smul_add a m n)
    (fun c a m ↦ smul_comm a c m))).toAddMonoidHom

private noncomputable def moduleToInternalObj (N : ModuleCat.{v} R) :
    Mod Ab.{v} (AddCommGrpCat.of R) := by
  letI : ModObj (AddCommGrpCat.of R) (AddCommGrpCat.of N) :=
    ModObj.mk' (AddCommGrpCat.of R) (ordinaryAct R N)
      (AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun n m ↦ by
        change (n.down : R) • m = n.down • m
        exact Int.cast_smul_eq_zsmul R n.down m))
      (AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext_threefold fun a b m ↦ by
        exact mul_smul a b m))
  exact ⟨AddCommGrpCat.of N⟩

private noncomputable def moduleToInternalHom {M N : Mod Ab.{v} (AddCommGrpCat.of R)}
    (f : (internalToModule R).obj M ⟶ (internalToModule R).obj N) : M ⟶ N :=
  Mod.homMk (AddCommGrpCat.ofHom f.hom.toAddMonoidHom)
    (AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun a m ↦ by
      exact f.hom.map_smul a m))

private instance : (internalToModule R).Full := (internalToModuleFullyFaithful R).full
private instance : (internalToModule R).Faithful := (internalToModuleFullyFaithful R).faithful

private noncomputable def realizationIso (N : ModuleCat.{v} R) :
    (internalToModule R).obj (moduleToInternalObj R N) ≅ N :=
  ModuleCat.isoMk (Iso.refl _) (fun _ ↦ rfl)

private instance : (internalToModule R).EssSurj where
  mem_essImage N := ⟨moduleToInternalObj R N, ⟨realizationIso R N⟩⟩

private instance : (internalToModule R).IsEquivalence where


end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]

private def sectionsIsoOfAdjunction
    (L : ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)) ⥤ PointMod ℓ k)
    (R : PointMod ℓ k ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)))
    [L.Additive] [R.Additive] (adj : L ⊣ R)
    (e : L.obj (ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl ℓ))) ≅ 𝟙_ (PointMod ℓ k))
    (he : ∀ a : ULift.{u + 1} (PadicAlgCl ℓ),
      L.map (ModuleCat.ofHom (LinearMap.mulRight _ a)) ≫ e.hom =
        e.hom ≫ (pointScalarsOp ℓ k a).unop) : pointSections ℓ k ≅ R := by
  let f (M : PointMod ℓ k) : (pointSections ℓ k).obj M ≃+ R.obj M :=
    ((AddEquiv.ofBijective
      ({ toFun := fun m ↦ e.hom ≫ m
         map_zero' := by simp
         map_add' := by
           intro m n
           change e.hom ≫ (m + n) = e.hom ≫ m + e.hom ≫ n
           exact Preadditive.comp_add _ _ _ e.hom m n } :
        (pointSections ℓ k).obj M →+
          (L.obj (ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl ℓ))) ⟶ M))
      ⟨fun m n h ↦ (cancel_epi e.hom).mp h,
        fun m ↦ ⟨e.inv ≫ m, by simp⟩⟩).trans
      (adj.homAddEquiv _ _)).trans
      (ModuleCat.homAddEquiv.trans
        (LinearMap.ringLmapEquivSelf (ULift.{u + 1} (PadicAlgCl ℓ)) ℤ
          (R.obj M)).toAddEquiv)
  let l (M : PointMod ℓ k) : (pointSections ℓ k).obj M ≃ₗ[
      ULift.{u + 1} (PadicAlgCl ℓ)] R.obj M :=
    { f M with
      map_smul' := by
        intro a m
        change (adj.homEquiv _ M (e.hom ≫ ((pointScalarsOp ℓ k a).unop ≫ m))) 1 =
          a • (adj.homEquiv _ M (e.hom ≫ m)) 1
        rw [← Category.assoc, ← he, Category.assoc,
          adj.homEquiv_naturality_left]
        change (adj.homEquiv _ M (e.hom ≫ m)) (1 * a) = _
        rw [_root_.one_mul]
        simpa only [smul_eq_mul, _root_.mul_one] using
          (adj.homEquiv _ M (e.hom ≫ m)).hom.map_smul a 1 }
  exact NatIso.ofComponents (fun M ↦ (l M).toModuleIso) (by
    intro M N g
    ext m
    change (adj.homEquiv _ N (e.hom ≫ (m ≫ g))) 1 =
      (R.map g) ((adj.homEquiv _ M (e.hom ≫ m)) 1)
    rw [← Category.assoc, adj.homEquiv_naturality_right]
    rfl)

private def scalarCoordinateEquivalence :
    Mod Ab.{u + 1} (scalarRingObj (Profinite.padicAlgClRingObj ℓ)) ≌
      ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)) := by
  let K := ULift.{u + 1} (PadicAlgCl ℓ)
  let φ := scalarQbarHom.{u} ℓ
  haveI : (Mod.comap φ).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  exact (Mod.comap φ ⋙ internalToModule K).asEquivalence

private def scalarCoordinateRegularIso :
    (scalarCoordinateEquivalence ℓ).functor.obj
      (Mod.regular (scalarRingObj (Profinite.padicAlgClRingObj ℓ))) ≅
      ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl ℓ)) := by
  let K := ULift.{u + 1} (PadicAlgCl ℓ)
  let φ := scalarQbarHom.{u} ℓ
  let r : (Mod.comap φ).obj
      (Mod.regular (scalarRingObj (Profinite.padicAlgClRingObj ℓ))) ≅
        Mod.regular (AddCommGrpCat.of K) :=
    (Mod.comapCongr (by simp : inv (inv φ) = φ)).symm.app _ ≪≫
      Mod.regularIsoOfIsIso (inv φ)
  exact (internalToModule K).mapIso r ≪≫ (internalRegularCoordinates K).toModuleIso

section RegularScalar
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end RegularScalar

private def scalarEntry (a : ULift.{u + 1} (PadicAlgCl ℓ)) :
    𝟙_ Ab.{u + 1} ⟶ scalarRingObj (Profinite.padicAlgClRingObj ℓ) :=
  (AddCommGrpCat.uliftZMultiplesAddEquiv _).symm ((scalarQbarConstants ℓ) a)

private theorem scalarCoordinateRegular_action (a : ULift.{u + 1} (PadicAlgCl ℓ)) :
    (scalarCoordinateEquivalence ℓ).functor.map
        (Mod.regularLift (Mod.regular (scalarRingObj (Profinite.padicAlgClRingObj ℓ)))
          (scalarEntry ℓ a)) ≫ (scalarCoordinateRegularIso ℓ).hom =
      (scalarCoordinateRegularIso ℓ).hom ≫
        ModuleCat.ofHom (LinearMap.mulRight _ a) := by
  let φinv : scalarRingObj (Profinite.padicAlgClRingObj.{u} ℓ) ⟶
      AddCommGrpCat.of (ULift.{u + 1} (PadicAlgCl ℓ)) :=
    (scalarQbarConstants.{u} ℓ).symm.toAddEquiv.toAddCommGrpIso.hom
  have hi : inv (scalarQbarHom.{u} ℓ) = φinv :=
    IsIso.inv_eq_of_hom_inv_id (by
      ext x
      exact congrArg ULift.down ((scalarQbarConstants.{u} ℓ).symm_apply_apply x))
  have hm := congrArg (fun m ↦ @MonObj.mul Ab.{u + 1} _ _
    (scalarRingObj (Profinite.padicAlgClRingObj.{u} ℓ)) m) (scalarQbar_monObj.{u} ℓ)
  ext x
  let y : ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ
    (Profinite.of PUnit.{u + 1})) := x
  change ((inv (scalarQbarHom.{u} ℓ)).hom
    ((μ[scalarRingObj (Profinite.padicAlgClRingObj.{u} ℓ)]).hom
      (x ⊗ₜ[ℤ] (scalarEntry ℓ a).hom (ULift.up 1)))).down =
    ((inv (scalarQbarHom.{u} ℓ)).hom x).down * a.down
  have ha : (scalarEntry ℓ a).hom (ULift.up 1) = (scalarQbarConstants.{u} ℓ) a := by
    change (1 : ℤ) • (scalarQbarConstants.{u} ℓ) a = _
    simp
  rw [hi, hm, ha]
  erw [AddCommGrpCat.ringMonObj_mul_tmul]
  change ((scalarQbarConstants.{u} ℓ).symm
    (y * (scalarQbarConstants.{u} ℓ) a)).down =
    ((scalarQbarConstants.{u} ℓ).symm y * a).down
  simp


private def encodedRegularIso :
    (scalarCoordinateEquivalence ℓ).inverse.obj
      (ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl ℓ))) ≅
      Mod.regular (scalarRingObj (Profinite.padicAlgClRingObj ℓ)) :=
  (scalarCoordinateEquivalence ℓ).inverse.mapIso (scalarCoordinateRegularIso ℓ).symm ≪≫
    (scalarCoordinateEquivalence ℓ).unitIso.symm.app _

private theorem encodedRegular_action (a : ULift.{u + 1} (PadicAlgCl ℓ)) :
    (scalarCoordinateEquivalence ℓ).inverse.map
        (ModuleCat.ofHom (LinearMap.mulRight _ a)) ≫ (encodedRegularIso ℓ).hom =
      (encodedRegularIso ℓ).hom ≫
        Mod.regularLift (Mod.regular (scalarRingObj (Profinite.padicAlgClRingObj ℓ)))
          (scalarEntry ℓ a) := by
  let Q := scalarCoordinateEquivalence ℓ
  let r := scalarCoordinateRegularIso ℓ
  let f := Mod.regularLift (Mod.regular (scalarRingObj (Profinite.padicAlgClRingObj ℓ)))
    (scalarEntry ℓ a)
  let g := ModuleCat.ofHom (LinearMap.mulRight (ULift.{u + 1} (PadicAlgCl ℓ)) a)
  have h₀ : Q.functor.map f ≫ r.hom = r.hom ≫ g :=
    scalarCoordinateRegular_action ℓ a
  have h : g ≫ r.inv = r.inv ≫ Q.functor.map f := by
    apply (cancel_epi r.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← h₀, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  change Q.inverse.map g ≫ (Q.inverse.map r.inv ≫ Q.unitIso.inv.app _) =
    (Q.inverse.map r.inv ≫ Q.unitIso.inv.app _) ≫ f
  rw [← Category.assoc, ← Q.inverse.map_comp, h, Q.inverse.map_comp, Category.assoc]
  exact congrArg (fun q ↦ Q.inverse.map r.inv ≫ q) (Q.unitIso.inv.naturality f)

private def pointScalarSection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (a : 𝟙_ Ab.{u + 1} ⟶ scalarSections.obj Λ) :
    𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ :=
  Functor.LaxMonoidal.ε (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map a ≫
    (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).counit.app Λ

private theorem pointScalarSection_constant (a : ULift.{u + 1} (PadicAlgCl ℓ)) :
    pointScalarSection (Profinite.padicAlgClRingObj ℓ) (scalarEntry ℓ a) =
      (Profinite.PadicAlgCl.constRingHom ℓ a.down).hom := by
  let F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  let b := (Profinite.PadicAlgCl.constRingHom ℓ a.down).hom
  have ha : Functor.LaxMonoidal.ε scalarSections ≫ scalarSections.map b =
      scalarEntry ℓ a := by
    rw [scalarSections_monoidal_eq]
    apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
    rw [show (AddCommGrpCat.uliftZMultiplesAddEquiv _)
      (scalarEntry ℓ a) = (scalarQbarConstants.{u} ℓ) a from
        (AddCommGrpCat.uliftZMultiplesAddEquiv _).apply_symm_apply _]
    change (((Functor.LaxMonoidal.ε
        (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
      (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map b).app
        (Opposite.op (Profinite.of PUnit.{u + 1}))).hom (ULift.up 1)) = _
    have h := Sheaf.ε_comp_ringHomΓSheafCompose_hom
      (coherentTopology Profinite.{u}) (Profinite.padicAlgClCondensedRing ℓ)
      (Profinite.PadicAlgCl.constSectionRingHom ℓ) (fun _ _ ↦ rfl) a.down
    have hp := congrArg (fun f ↦ f.app
      (Opposite.op (Profinite.of PUnit.{u + 1})) (ULift.up 1)) h
    change (((Functor.LaxMonoidal.ε
        (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
      (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map b).app
        (Opposite.op (Profinite.of PUnit.{u + 1}))).hom (ULift.up 1)) =
          1 * (scalarQbarConstants.{u} ℓ) a at hp
    simpa only [_root_.one_mul] using hp
  have ha' : adj.homEquiv _ Λ (Functor.OplaxMonoidal.η F ≫ b) =
      scalarEntry ℓ a := by
    rw [adj.homEquiv_naturality_right]
    exact ha
  have hb := (adj.homEquiv _ Λ).symm_apply_apply (Functor.OplaxMonoidal.η F ≫ b)
  rw [ha', adj.homEquiv_counit] at hb
  change Functor.LaxMonoidal.ε F ≫ _ = b
  rw [hb, ← Category.assoc, Functor.Monoidal.ε_η, Category.id_comp]

omit [IsAlgClosed k] in
private theorem scalarSection_constant (a : ULift.{u + 1} (PadicAlgCl ℓ)) :
    Mod.regularLift (Mod.regular
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point k).left))
      (scalarSection (Profinite.padicAlgClRingObj ℓ) (point k).left (scalarEntry ℓ a)) =
      (pointScalarsOp ℓ k a).unop := by
  have h : scalarSection (Profinite.padicAlgClRingObj ℓ) (point k).left (scalarEntry ℓ a) =
      Functor.LaxMonoidal.ε (upperStarFromPoint (point k).left) ≫
        (upperStarFromPoint (point k).left).map
          (pointScalarSection (Profinite.padicAlgClRingObj ℓ) (scalarEntry ℓ a)) := by
    simp only [scalarSection, scalarCoefficientHom, pointScalarSection, Functor.map_comp]
    rfl
  rw [h, pointScalarSection_constant]
  rfl

/-- The copower scalar extension has the finite-constant scalar presentation.
Source: blueprint local boundary duality, Step 5, explicit scalar extension.
Proof: identify the scalar ring at the one-point profinite set with the ordinary
algebraic closure, by evaluation of constant functions. Its internal modules are
ordinary modules. The finite-constant extension is left adjoint to internal
sections. On the regular module it has value the coefficient module, and on its
scalar endomorphisms it acts by the prescribed constant sections. Adjunction
therefore identifies its right adjoint with the published point sections functor,
linearly and naturally. Uniqueness of left adjoints gives the asserted natural
isomorphism with the copower construction, for arbitrary ordinary modules.
(blueprint: lem-a1-condensed-point-scalar-presentation) -/
theorem condensed_point_scalar_presentation :
    CondensedBoundaryScalarExtensionPresentation ℓ k := by
  classical
  let Q := scalarCoordinateEquivalence ℓ
  let C := Q.symm
  let F := finiteConstantScalarExtension (Profinite.padicAlgClRingObj ℓ) (point k).left
  let H := C.functor ⋙ F
  let R := pointInternalScalarSections (Profinite.padicAlgClRingObj ℓ) k ⋙ Q.functor
  obtain ⟨adjF⟩ := finiteConstantPointAdjunction (Profinite.padicAlgClRingObj ℓ) k
  let adj : H ⊣ R := C.toAdjunction.comp adjF
  have : H.IsLeftAdjoint := adj.isLeftAdjoint
  have : R.IsRightAdjoint := adj.isRightAdjoint
  have : H.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint H
  have : R.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isRightAdjoint R
  have : PreservesColimits H := adj.leftAdjoint_preservesColimits
  have : PreservesLimits R := adj.rightAdjoint_preservesLimits
  have : PreservesBinaryBiproducts H :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts H
  have : PreservesBinaryBiproducts R :=
    preservesBinaryBiproducts_of_preservesBinaryProducts R
  have : H.Additive := Functor.additive_of_preservesBinaryBiproducts H
  have : R.Additive := Functor.additive_of_preservesBinaryBiproducts R
  let e : H.obj (ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl ℓ))) ≅
      𝟙_ (PointMod ℓ k) :=
    F.mapIso (encodedRegularIso ℓ) ≪≫
      scalarRegularIso (Profinite.padicAlgClRingObj ℓ) (point k).left
  have he (a : ULift.{u + 1} (PadicAlgCl ℓ)) :
      H.map (ModuleCat.ofHom (LinearMap.mulRight _ a)) ≫ e.hom =
        e.hom ≫ (pointScalarsOp ℓ k a).unop := by
    have henc : C.functor.map (ModuleCat.ofHom (LinearMap.mulRight _ a)) ≫
        (encodedRegularIso ℓ).hom = (encodedRegularIso ℓ).hom ≫
          Mod.regularLift (Mod.regular (scalarRingObj (Profinite.padicAlgClRingObj ℓ)))
            (scalarEntry ℓ a) := encodedRegular_action ℓ a
    dsimp only [H, Functor.comp_map, e, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← F.map_comp, henc,
      F.map_comp, Category.assoc, scalarRegular_entry, scalarSection_constant]
    exact (Category.assoc _ _ _).symm
  let eR := sectionsIsoOfAdjunction ℓ k H R adj e he
  exact ⟨C, ⟨(condensedPointScalarAdjunction ℓ k).leftAdjointUniq
    (adj.ofNatIsoRight eR.symm)⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
