/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.RelativeCurvePunctual
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeNormalizedRealEnvelope
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Linear
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # Constant twists and native higher compact support

Source: latest blueprint, lem-wf-constant-twist-cohomology.
(blueprint: lem-zl-native-higher-shriek-constant-twist)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.RelativeCurve
open NativeCondensedModule CategoryTheory.Endofunctor

private instance pointColimits (X : Scheme.{u}) :
    PreservesColimits (upperStarFromPoint X) :=
  (pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).leftAdjoint_preservesColimits

private instance pointAdditive (X : Scheme.{u}) : (upperStarFromPoint X).Additive := by
  have : PreservesBinaryBiproducts (upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

private def coefficientScalars (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    PadicAlgCl l →+* MonObj.Γ (padicAlgClRingObj X l) :=
  (MonObj.Γ.mapFunctor (upperStarFromPoint X)).comp
    (Profinite.PadicAlgCl.constRingHom l)

@[instance_reducible] private def linearModules (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Linear (PadicAlgCl l) (Modules l X) :=
  Mod.linearOfRingHom (coefficientScalars l X)

attribute [local instance] linearModules

private theorem linearLowerStar (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).Linear (PadicAlgCl l) := by
  apply Mod.linear_mapMod_comp_comap
    (ProEtale.lowerStar Ab.{u + 1} f) (condensedPushforwardHom _ f)
    (coefficientScalars l X) (coefficientScalars l Y)
  intro a
  simp only [coefficientScalars, RingHom.comp_apply, MonObj.Γ.mapFunctor_hom,
    condensedPushforwardHom, Adjunction.unitAlgHom, Category.assoc]
  exact Adjunction.ε_comp_map_comp_unit_app_comp_map
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f)
    (upperStarFromPoint Y) (upperStarFromPoint X) (upperStarFromPointComp f).hom
    ((Profinite.PadicAlgCl.constRingHom l a).hom)

attribute [local instance] linearLowerStar

private theorem linearUpperStar (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).Linear (PadicAlgCl l) :=
  (CondensedRing.upperStarLowerStarAdjunction _ f).left_adjoint_linear

attribute [local instance] linearUpperStar

private theorem linearOpenShriek (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] :
    (CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj l) j).Linear
      (PadicAlgCl l) :=
  (CondensedRing.openImmersionLowerShriekUpperStarAdjunction _ j).left_adjoint_linear

attribute [local instance] linearOpenShriek

private instance complexHomologyLinear
    {C : Type*} [Category* C] [Abelian C]
    (R : Type*) [Ring R] [Linear R C] (i : ℤ) :
    (HomologicalComplex.homologyFunctor C (.up ℤ) i).Linear R := by
  have : (HomologicalComplex.shortComplexFunctor C (.up ℤ) i).Linear R := by
    constructor
    intro K L f r
    ext <;> rfl
  constructor
  intro K L f r
  change ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor C (.up ℤ) i).map (r • f)) = _
  rw [Functor.map_smul, ShortComplex.homologyMap_smul]
  rfl

private instance derivedHomologyLinear
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (R : Type*) [Ring R] [Linear R C] (i : ℤ) :
    (DerivedCategory.homologyFunctor C i).Linear R := by
  let : Localization.Lifting (DerivedCategory.Q (C := C))
      (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.homologyFunctor C (.up ℤ) i)
      (DerivedCategory.homologyFunctor C i) :=
    ⟨DerivedCategory.homologyFunctorFactors C i⟩
  exact (Localization.functor_linear_iff (DerivedCategory.Q (C := C))
    (HomologicalComplex.quasiIso C (.up ℤ)) R
    (HomologicalComplex.homologyFunctor C (.up ℤ) i)
    (DerivedCategory.homologyFunctor C i)).mp inferInstance

private def scalarIso {C : Type*} [Category* C] [Preadditive C]
    {R : Type*} [CommRing R] [Linear R C] (b : Rˣ) (M : C) : M ≅ M where
  hom := (b : R) • 𝟙 M
  inv := ((b⁻¹ : Rˣ) : R) • 𝟙 M
  hom_inv_id := by simp [Linear.comp_smul, smul_smul]
  inv_hom_id := by simp [Linear.comp_smul, smul_smul]

private theorem constantScalar_eq (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (b : (PadicAlgCl l)ˣ) :
    (CondensedRing.ConstantWeil.scalar l X b).hom =
      (b : PadicAlgCl l) • 𝟙 (𝟙_ (Modules l X)) := by
  unfold CondensedRing.ConstantWeil.scalar CondensedRing.ConstantWeil.coefficientScalar
  rw [Mod.linearOfRingHom_smul_id (coefficientScalars l X)]
  apply Mod.hom_ext
  change (((upperStarFromPoint X).mapMod (Profinite.padicAlgClRingObj l)).map
    (Mod.regularEndRingHom (Profinite.PadicAlgCl.constRingHom l b))).hom = _
  rw [Functor.mapMod_map_regularEndRingHom]
  exact Mod.rightUnitor_inv_whiskerLeft_mul_eq
    (S := padicAlgClRingObj X l) (coefficientScalars l X b).hom

private theorem left_scalar_eq_right {C : Type*} [Category* C]
    [MonoidalCategory C] [BraidedCategory C] (M : C) (t : End (𝟙_ C)) :
    (λ_ M).inv ≫ t ▷ M ≫ (λ_ M).hom =
      (ρ_ M).inv ≫ M ◁ t ≫ (ρ_ M).hom := by
  rw [← braiding_rightUnitor M,
    BraidedCategory.braiding_naturality_left_assoc,
    braiding_tensorUnit_left]
  simp

private theorem unit_twist_equivariance {C : Type*} [Category* C]
    [MonoidalCategory C] [BraidedCategory C] (P : C ⥤ C) [P.Monoidal]
    (M : C) (φ : P.obj M ≅ M) (t : End (𝟙_ C)) :
    P.map (ρ_ M).hom ≫ φ.hom ≫
        ((λ_ M).inv ≫ t ▷ M ≫ (λ_ M).hom) =
      (Functor.Monoidal.μIso P M (𝟙_ C)).inv ≫
        (φ.hom ⊗ₘ ((Functor.Monoidal.εIso P).inv ≫ t)) ≫ (ρ_ M).hom := by
  rw [left_scalar_eq_right, ← Functor.OplaxMonoidal.right_unitality_hom P M]
  simp only [tensorHom_def', whiskerLeft_comp, Category.assoc]
  rw [rightUnitor_inv_naturality_assoc, Iso.hom_inv_id_assoc,
    ← whisker_exchange_assoc φ.hom t]
  rfl

private def rescale {C : Type*} [Category* C] [Preadditive C]
    {R : Type*} [CommRing R] [Linear R C] {P : C ⥤ C}
    (M : IsoAlgebra P) (b : Rˣ) : IsoAlgebra P :=
  IsoAlgebra.mk M.carrier (M.str ≪≫ scalarIso b M.carrier)

private theorem rescale_str {C : Type*} [Category* C] [Preadditive C]
    {R : Type*} [CommRing R] [Linear R C] {P : C ⥤ C}
    (M : IsoAlgebra P) (b : Rˣ) :
    (rescale M b).obj.str = (b : R) • M.obj.str := by
  change M.str.hom ≫ ((b : R) • 𝟙 _) = _
  simp only [Linear.comp_smul, Category.comp_id]
  rfl

private def map_rescale_iso
    {C E : Type*} [Category* C] [Preadditive C] [Category* E] [Preadditive E]
    {R : Type*} [CommRing R] [Linear R C] [Linear R E]
    {P : C ⥤ C} {Q : E ⥤ E} {L : C ⥤ E} [L.Linear R]
    (e : L ⋙ Q ≅ P ⋙ L) (M : IsoAlgebra P) (b : Rˣ) :
    (IsoAlgebra.mapOfNatIso e).obj (rescale M b) ≅
      rescale ((IsoAlgebra.mapOfNatIso e).obj M) b := by
  apply IsoAlgebra.isoMk
    (K := (IsoAlgebra.mapOfNatIso e).obj (rescale M b))
    (K' := rescale ((IsoAlgebra.mapOfNatIso e).obj M) b) (Iso.refl _)
  change Q.map (𝟙 (L.obj M.carrier)) ≫
      (rescale ((IsoAlgebra.mapOfNatIso e).obj M) b).obj.str =
    ((IsoAlgebra.mapOfNatIso e).obj (rescale M b)).obj.str ≫ 𝟙 _
  rw [Q.map_id]
  simp only [Category.id_comp, Category.comp_id,
    IsoAlgebra.mapOfNatIso_obj_obj_str, rescale_str, Functor.map_smul,
    Linear.comp_smul]
  rfl

private theorem normalizedTwist_rescale
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (M : NativeL2.WeilModule D l X₀) (b : (PadicAlgCl l)ˣ) :
    Nonempty (NativeEnvelope.normalizedTwist D l X₀ hl M b ≅ rescale M b) := by
  let X := (D.geometricFiber X₀).left
  let t := (coefficientScalars l X b).hom
  have ht : (scalarIso b M.carrier).hom =
      (λ_ M.carrier).inv ≫
        (CondensedRing.ConstantWeil.scalar l X b).hom ▷ M.carrier ≫
          (λ_ M.carrier).hom := by
    rw [left_scalar_eq_right, constantScalar_eq]
    change (b : PadicAlgCl l) • 𝟙 M.carrier = _
    rw [Mod.linearOfRingHom_smul_id (coefficientScalars l X),
      Mod.linearOfRingHom_smul_id (coefficientScalars l X)]
    rw [← Mod.smulNatTrans_app_tensor]
    have h := (Mod.smulNatTrans t).naturality (ρ_ M.carrier).hom
    simp only [Functor.id_map] at h
    rw [← h, Iso.inv_hom_id_assoc]
  refine ⟨IsoAlgebra.isoMk (ρ_ M.carrier) ?_⟩
  change (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (D.geometricFrobenius X₀).hom).map (ρ_ M.carrier).hom ≫
      (M.str ≪≫ scalarIso b M.carrier).hom = _
  rw [Iso.trans_hom, ht]
  exact unit_twist_equivariance _ M.carrier M.str
    (CondensedRing.ConstantWeil.scalar l X b).hom

private def rescale_iso
    {C : Type*} [Category* C] [Preadditive C]
    {R : Type*} [CommRing R] [Linear R C] {P : C ⥤ C}
    {M N : IsoAlgebra P} (e : M ≅ N) (b : Rˣ) :
    rescale M b ≅ rescale N b := by
  apply IsoAlgebra.isoMk (K := rescale M b) (K' := rescale N b)
    ((IsoAlgebra.forget P).mapIso e)
  change P.map e.hom.hom.f ≫ (rescale N b).obj.str =
    (rescale M b).obj.str ≫ e.hom.hom.f
  rw [rescale_str, rescale_str, Linear.comp_smul, Linear.smul_comp]
  exact congrArg (fun f ↦ (b : R) • f) e.hom.hom.h

private def rescale_inverse_iso
    {C : Type*} [Category* C] [Preadditive C]
    {R : Type*} [CommRing R] [Linear R C] {P : C ⥤ C}
    (M : IsoAlgebra P) (b : Rˣ) : rescale (rescale M b) b⁻¹ ≅ M := by
  apply IsoAlgebra.isoMk (K := rescale (rescale M b) b⁻¹) (K' := M) (Iso.refl _)
  change P.map (𝟙 M.carrier) ≫ M.obj.str =
    (rescale (rescale M b) b⁻¹).obj.str ≫ 𝟙 M.carrier
  rw [P.map_id]
  simp only [Category.id_comp, rescale_str,
    smul_smul, Units.inv_mul, one_smul]
  exact (Category.comp_id _).symm

private theorem transport_three_rescale
    {C₀ C₁ C₂ C₃ : Type*}
    [Category* C₀] [Preadditive C₀] [Category* C₁] [Preadditive C₁]
    [Category* C₂] [Preadditive C₂] [Category* C₃] [Preadditive C₃]
    {R : Type*} [CommRing R]
    [Linear R C₀] [Linear R C₁] [Linear R C₂] [Linear R C₃]
    {P₀ : C₀ ⥤ C₀} {P₁ : C₁ ⥤ C₁} {P₂ : C₂ ⥤ C₂} {P₃ : C₃ ⥤ C₃}
    {L₁ : C₀ ⥤ C₁} {L₂ : C₁ ⥤ C₂} {L₃ : C₂ ⥤ C₃}
    [L₁.Linear R] [L₂.Linear R] [L₃.Linear R]
    (e₁ : L₁ ⋙ P₁ ≅ P₀ ⋙ L₁) (e₂ : L₂ ⋙ P₂ ≅ P₁ ⋙ L₂)
    (e₃ : L₃ ⋙ P₃ ≅ P₂ ⋙ L₃)
    (M M' : IsoAlgebra P₀) (N : IsoAlgebra P₃) (b : Rˣ)
    (eU : M' ≅ rescale M b)
    (eY : N ≅ rescale ((IsoAlgebra.mapOfNatIso e₃).obj
      ((IsoAlgebra.mapOfNatIso e₂).obj ((IsoAlgebra.mapOfNatIso e₁).obj M))) b) :
    Nonempty ((IsoAlgebra.mapOfNatIso e₃).obj ((IsoAlgebra.mapOfNatIso e₂).obj
      ((IsoAlgebra.mapOfNatIso e₁).obj M')) ≅ N) := by
  let S := IsoAlgebra.mapOfNatIso e₁
  let T := IsoAlgebra.mapOfNatIso e₂
  let H := IsoAlgebra.mapOfNatIso e₃
  exact ⟨H.mapIso (T.mapIso (S.mapIso eU ≪≫ map_rescale_iso e₁ M b) ≪≫
    map_rescale_iso e₂ (S.obj M) b) ≪≫ map_rescale_iso e₃ (T.obj (S.obj M)) b ≪≫
    eY.symm⟩

/-- A constant Weil twist followed by its inverse returns the given native Weil module.
Source: latest blueprint, invertibility of the constant line B_b.
(blueprint: lem-zl-native-higher-shriek-constant-twist)

Proof: the tensor unitor identifies each twist with scalar multiplication of the
Weil structure. The two scalar factors are inverse units, so their composite is one.
-/
theorem nonempty_normalizedTwist_inverse_iso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (M : NativeL2.WeilModule D l X₀) (b : (PadicAlgCl l)ˣ) :
    Nonempty (NativeEnvelope.normalizedTwist D l X₀ hl
      (NativeEnvelope.normalizedTwist D l X₀ hl M b) b⁻¹ ≅ M) := by
  obtain ⟨e₁⟩ := normalizedTwist_rescale D l hl X₀ M b
  obtain ⟨e₂⟩ := normalizedTwist_rescale D l hl X₀
    (NativeEnvelope.normalizedTwist D l X₀ hl M b) b⁻¹
  exact ⟨e₂ ≪≫ rescale_iso e₁ b⁻¹ ≪≫ rescale_inverse_iso M b⟩

set_option maxHeartbeats 2000000 in
-- Elaborating the three concrete derived transports expands their canonical comparison maps.
/-- Higher compact support commutes with the actual constant Weil line, for each chosen
compactification and each cohomological degree.
Source: latest blueprint, lem-wf-constant-twist-cohomology.
(blueprint: lem-zl-native-higher-shriek-constant-twist)

Proof: identify tensoring with the constant line with scalar multiplication of the
Weil structure by b using the tensor unitor. The ordinary compactification composite
is linear over the coefficient field: open extension and proper direct image are
linear adjoints, and their exact and right derived functors are linear. Each of the
three canonical transports defining higherShriek therefore carries b times the
structure map to b times the transported structure map. Compose these identity-carrier
comparisons and the tensor unitors at the two ends. No choice of fibre basis enters.
-/
theorem nonempty_higherShriek_normalizedTwist_iso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {U₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (h₀ : U₀ ⟶ Y₀) (c₀ : Compactification h₀.left)
    (M : NativeL2.WeilModule D l U₀) (b : (PadicAlgCl l)ˣ) (i : ℕ) :
    Nonempty (higherShriek D l h₀ c₀
        (NativeEnvelope.normalizedTwist D l U₀ hl M b) i ≅
      NativeEnvelope.normalizedTwist D l Y₀ hl (higherShriek D l h₀ c₀ M i) b) := by
  let Λ := Profinite.padicAlgClRingObj.{u} l
  let S := IsoAlgebra.mapOfNatIso
    ((CondensedRing.upperStar Λ (D.geometricFrobenius U₀).hom).mapDerivedCategorySingleFunctor 0)
  let R := IsoAlgebra.mapOfNatIso (exchange D l h₀ c₀)
  let H := IsoAlgebra.mapOfNatIso
    ((CondensedRing.upperStar Λ
      (D.geometricFrobenius Y₀).hom).mapDerivedCategoryHomologyFunctorIso (i : ℤ))
  have : (CondensedRing.rightDerivedLowerShriekOfCompactification Λ
      (geometricCompactification D h₀ c₀)).Linear (PadicAlgCl l) := by
    change ((CondensedRing.openImmersionLowerShriek Λ
      (geometricCompactification D h₀ c₀).i).mapDerivedCategory ⋙
      (CondensedRing.lowerStar Λ
        (geometricCompactification D h₀ c₀).g).rightDerivedFunctor).Linear (PadicAlgCl l)
    infer_instance
  obtain ⟨eU⟩ := normalizedTwist_rescale D l hl U₀ M b
  obtain ⟨eY⟩ := normalizedTwist_rescale D l hl Y₀ (higherShriek D l h₀ c₀ M i) b
  unfold higherShriek at eY ⊢
  exact transport_three_rescale _ _ _ M _ _ b eU eY

end WeilConjectures.RelativeCurve
