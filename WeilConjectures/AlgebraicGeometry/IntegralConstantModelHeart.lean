/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import Mathlib.CategoryTheory.Abelian.Subcategory
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleModuleObjectsEssentiallySmall
import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# The integral constant-model constructible category and its heart

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-integral-heart/
sk-lem-int-integral-heart-triangulated.md, assertions 1--2
(blueprint: det-lem-int-integral-heart-triangulated).

Coefficients are pulled-back condensed continuous functions into the valuation ring,
and the derived category is the ordinary unbounded category of internal modules.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The condensed valuation ring for an arbitrary finite extension, using its canonical
spectral norm. A finite extension of the small field of p-adic numbers is small by
`Module.Finite.small`. Its `Shrink` is used only to fit the existing continuous-function
API; `Shrink.algEquiv` identifies it with the given extension. Thus no coefficient
embedding or equality of universes is assumed. Source: blueprint integral-heart setting
and def-weil-l-adic-coefficient-extension
(blueprint: det-lem-int-integral-heart-triangulated). -/
noncomputable abbrev integralHeartCoefficientRingObj
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI : Small.{0} E := Module.Finite.small (Padic ℓ) E
  letI : FiniteDimensional (Padic ℓ) (Shrink.{0} E) :=
    (Shrink.algEquiv (Padic ℓ) E).symm.toLinearEquiv.finiteDimensional
  letI := spectralNorm.normedField (Padic ℓ) (Shrink.{0} E)
  Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers ℓ (Shrink.{0} E))

private theorem smallIntegralCoefficientIso (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [NormedField L] [NormedAlgebra ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L] :
    Nonempty (Mon.mk (integralCondensedRing ℓ (ULift.{u} L)) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers ℓ L))) := by
  let F := ULift.{u} L
  let : NormedField F :=
    { (inferInstance : Field F), (inferInstance : NormedCommRing F) with
      dist_eq x y := dist_eq_norm_neg_add x.down y.down
      norm_mul x y := norm_mul x.down y.down }
  let : NormedAlgebra ℚ_[ℓ] F := ⟨fun a x ↦ by
    change ‖a • x.down‖ ≤ ‖a‖ * ‖x.down‖
    exact norm_smul_le a x.down⟩
  let : FiniteDimensional ℚ_[ℓ] F :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := L)).symm.finiteDimensional
  let A := latticeCoefficientIntegers ℓ F
  let e : WithAbs (Padic.coefficientExtensionAbsoluteValue ℓ F) ≃+* L :=
    (WithAbs.equiv _).trans ULift.ringEquiv
  have he (x : WithAbs (Padic.coefficientExtensionAbsoluteValue ℓ F)) : ‖e x‖ = ‖x‖ := by
    change ‖(WithAbs.equiv _ x).down‖ = spectralNorm ℚ_[ℓ] F (WithAbs.equiv _ x)
    exact NormedAlgebra.norm_eq_spectralNorm ℚ_[ℓ] (L := F) (WithAbs.equiv _ x)
  have hmem (x : WithAbs (Padic.coefficientExtensionAbsoluteValue ℓ F)) :
      x ∈ A ↔ e x ∈ Padic.coefficientExtensionIntegers ℓ L := by
    have hm := (Padic.extension_integers_dvr ℓ F
      (Padic.coefficientExtensionAbsoluteValue ℓ F)
      (spectralNorm_extends (K := ℚ_[ℓ]) (L := F))).choose_spec.choose_spec.1
    change WithAbs.equiv _ x ∈ Padic.coefficientExtensionIntegers ℓ F ↔ _
    change ∀ y : F, y ∈ Padic.coefficientExtensionIntegers ℓ F ↔
      Padic.coefficientExtensionAbsoluteValue ℓ F y ≤ 1 at hm
    have hmL := (Padic.extension_integers_dvr ℓ L
      (Padic.coefficientExtensionAbsoluteValue ℓ L)
      (spectralNorm_extends (K := ℚ_[ℓ]) (L := L))).choose_spec.choose_spec.1
    change ∀ y : L, y ∈ Padic.coefficientExtensionIntegers ℓ L ↔
      Padic.coefficientExtensionAbsoluteValue ℓ L y ≤ 1 at hmL
    rw [hm, hmL]
    change ‖x‖ ≤ 1 ↔ spectralNorm ℚ_[ℓ] L (e x) ≤ 1
    rw [← NormedAlgebra.norm_eq_spectralNorm ℚ_[ℓ], he]
  let ei : A ≃+* Padic.coefficientExtensionIntegers ℓ L :=
    { toFun := fun x ↦ ⟨e x, (hmem x).mp x.property⟩
      invFun := fun x ↦ ⟨e.symm x,
        (hmem _).mpr (by simpa only [e.apply_symm_apply] using x.property)⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x y)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x y) }
  have hei : Isometry ei := by
    apply AddMonoidHomClass.isometry_of_norm ei
    intro x
    exact he x
  have heis : Isometry ei.symm := by
    intro x y
    simpa only [ei.apply_symm_apply] using (hei (ei.symm x) (ei.symm y)).symm
  let eR : Profinite.continuousMapRingSheafOfUniverse.{u,u} A ≅
      Profinite.continuousMapRingSheaf.{u} (Padic.coefficientExtensionIntegers ℓ L) :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.toRingHom.compLeftContinuous S.unop hei.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.symm.toRingHom.compLeftContinuous S.unop
              heis.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.apply_symm_apply _ }
  let eAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eAb.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom eAb.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  refine ⟨{ hom := Mon.ofHom eAb.hom
            inv := Mon.ofHom eAb.inv
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · apply Mon.Hom.ext
    exact eAb.hom_inv_id
  · apply Mon.Hom.ext
    exact eAb.inv_hom_id

private theorem smallIntegralSerre (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type) [NormedField F] [NormedAlgebra ℚ_[ℓ] F]
    [FiniteDimensional ℚ_[ℓ] F] (X : Scheme.{u}) [IsNoetherian X] :
    let Q : ObjectProperty _ := IsConstructibleModuleObject
      (condensedRingObj
        (Profinite.continuousMapRingObj (Padic.coefficientExtensionIntegers ℓ F)) X)
    Q.IsClosedUnderKernels ∧ Q.IsClosedUnderCokernels ∧ Q.IsClosedUnderExtensions := by
  have hs := CondensedRing.integralConstructible_serre ℓ F X
  dsimp [CondensedRing.integralCoeff] at hs
  have transport (B C : Subring F) (h : B = C) :
      let QB : ObjectProperty _ := IsConstructibleModuleObject
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)
      let QC : ObjectProperty _ := IsConstructibleModuleObject
        (condensedRingObj (Profinite.continuousMapRingObj.{u} C) X)
      QB.IsClosedUnderKernels ∧ QB.IsClosedUnderCokernels ∧ QB.IsClosedUnderExtensions →
      QC.IsClosedUnderKernels ∧ QC.IsClosedUnderCokernels ∧ QC.IsClosedUnderExtensions := by
    subst C
    exact id
  exact transport _ _ (CondensedRing.continuousIntegers_eq ℓ F) hs

private theorem comparisonThroughIso
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [NormedField F]
    [NormedAlgebra ℚ_[ℓ] F] [FiniteDimensional ℚ_[ℓ] F]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (φ : integralCondensedRing ℓ (ULift.{u} F) ⟶ Λ) [IsMonHom φ] [IsIso φ]
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsConstantModelConstructible Λ X M ↔
      IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  let ψ := coefficientMap φ X
  have hp := integralLfpConstantModelComparison ℓ (ULift.{u} F) X
    ((Mod.comap ψ).obj M)
  refine (constantModel_comap_iff φ X M).symm.trans (hp.symm.trans ?_)
  constructor
  · intro h
    exact _root_.constructible_of_iso
      (((Mod.comapComp (inv ψ) ψ).symm ≪≫ Mod.comapCongr (by simp) ≪≫
        Mod.comapId _).app M) (_root_.constructible_comap (inv ψ) h)
  · exact _root_.constructible_comap ψ

private theorem serreHeart
    (A : Type*) [Category.{u + 1} A] [Abelian A] [HasDerivedCategory.{u + 1} A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    [ObjectProperty.EssentiallySmall.{u + 1} P] :
    let T := DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P
    T.IsClosedUnderIsomorphisms ∧ T.IsTriangulated ∧
    (∀ K, T K → DerivedCategory.TStructure.t.bounded K ∧ ∀ n : ℤ,
      T ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      T ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
    (P.ι ⋙ DerivedCategory.singleFunctor A 0).Full ∧
    (P.ι ⋙ DerivedCategory.singleFunctor A 0).Faithful ∧
    (∀ K, (P.ι ⋙ DerivedCategory.singleFunctor A 0).essImage K ↔
      T K ∧ DerivedCategory.TStructure.t.le 0 K ∧ DerivedCategory.TStructure.t.ge 0 K) ∧
    Nonempty (Abelian P.FullSubcategory) ∧ P.IsClosedUnderKernels ∧
    P.IsClosedUnderCokernels ∧ P.IsClosedUnderExtensions ∧
    EssentiallySmall.{u + 1} P.FullSubcategory := by
  let T := DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P
  have : T.IsClosedUnderIsomorphisms := by dsimp [T]; infer_instance
  have : T.IsTriangulated := by dsimp [T]; infer_instance
  have hf : (P.ι ⋙ DerivedCategory.singleFunctor A 0).Full := inferInstance
  have hfaith : (P.ι ⋙ DerivedCategory.singleFunctor A 0).Faithful := inferInstance
  refine ⟨inferInstance, inferInstance, ?_, hf, hfaith, ?_,
    ?_, inferInstance, inferInstance, inferInstance, ?_⟩
  · intro K hK
    refine ⟨hK.1, fun n ↦ ?_⟩
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.1
    exact ⟨⟨⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩,
      DerivedCategory.homologyProperty_truncLE hK.2 n⟩,
      ⟨⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩,
      DerivedCategory.homologyProperty_truncGE hK.2 n⟩⟩
  · have hs (M : A) : T ((DerivedCategory.singleFunctor A 0).obj M) ↔ P M := by
      constructor
      · intro h
        exact P.prop_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app M)
          (h.2 0)
      · intro h
        refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
        by_cases hn : n = 0
        · subst n
          exact P.prop_of_iso
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app M).symm h
        · rcases lt_or_gt_of_ne hn with hn | hn
          · exact P.prop_of_isZero (DerivedCategory.isZero_of_isGE _ 0 n hn)
          · exact P.prop_of_isZero (DerivedCategory.isZero_of_isLE _ 0 n hn)
    intro K
    constructor
    · rintro ⟨M, ⟨eM⟩⟩
      change (DerivedCategory.singleFunctor A 0).obj M.obj ≅ K at eM
      refine ⟨T.prop_of_iso eM ((hs M.obj).mpr M.property), ?_, ?_⟩
      · have : ((DerivedCategory.singleFunctor A 0).obj M.obj).IsLE 0 := inferInstance
        have : K.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso eM 0
        exact DerivedCategory.TStructure.t.le_of_isLE K 0
      · have : ((DerivedCategory.singleFunctor A 0).obj M.obj).IsGE 0 := inferInstance
        have : K.IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso eM 0
        exact DerivedCategory.TStructure.t.ge_of_isGE K 0
    · rintro ⟨hK, hle, hge⟩
      have : K.IsLE 0 := ⟨hle⟩
      have : K.IsGE 0 := ⟨hge⟩
      obtain ⟨M, ⟨eM⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
      exact ⟨⟨M, (hs M).mp (T.prop_of_iso eM hK)⟩, ⟨eM.symm⟩⟩
  · have : P.IsClosedUnderBinaryProducts := by
      constructor
      rintro M ⟨b⟩
      refine P.prop_of_iso ?_ (P.prop_biprod
        (b.prop_diag_obj ⟨.left⟩) (b.prop_diag_obj ⟨.right⟩))
      exact biprod.isoProd _ _ ≪≫ HasLimit.isoOfNatIso (diagramIsoPair b.diag).symm ≪≫
        (limit.isLimit _).conePointUniqueUpToIso b.isLimit
    have : P.IsClosedUnderFiniteProducts := .mk'
    exact ⟨inferInstance⟩
  · infer_instance

private theorem smallFieldHeart
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [NormedField F]
    [NormedAlgebra ℚ_[ℓ] F] [FiniteDimensional ℚ_[ℓ] F]
    (X : Scheme.{u}) [IsNoetherian X] :
    let Λ := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers ℓ F)
    let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
    let P : ObjectProperty A := IsConstantModelConstructible Λ X
    let T := constantModelBoundedConstructible Λ X
    T.IsClosedUnderIsomorphisms ∧ T.IsTriangulated ∧
    (∀ K, T K → DerivedCategory.TStructure.t.bounded K ∧ ∀ n : ℤ,
      T ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      T ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
    (P.ι ⋙ DerivedCategory.singleFunctor A 0).Full ∧
    (P.ι ⋙ DerivedCategory.singleFunctor A 0).Faithful ∧
    (∀ K, (P.ι ⋙ DerivedCategory.singleFunctor A 0).essImage K ↔
      T K ∧ DerivedCategory.TStructure.t.le 0 K ∧ DerivedCategory.TStructure.t.ge 0 K) ∧
    Nonempty (Abelian P.FullSubcategory) ∧ P.IsClosedUnderKernels ∧
    P.IsClosedUnderCokernels ∧ P.IsClosedUnderExtensions ∧
    EssentiallySmall.{u + 1} P.FullSubcategory := by
  let Λ := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers ℓ F)
  let R := condensedRingObj Λ X
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R
  let P : ObjectProperty A := IsConstantModelConstructible Λ X
  let Q : ObjectProperty A := IsConstructibleModuleObject R
  obtain ⟨e⟩ := smallIntegralCoefficientIso.{u} ℓ F
  let φ := e.hom.hom
  have : IsMonHom φ := inferInstanceAs (IsMonHom e.hom.hom)
  have : IsIso φ := inferInstanceAs (IsIso e.hom.hom)
  have cmp (M : A) : P M ↔ Q M := comparisonThroughIso ℓ F Λ φ X M
  have hPQ : P = Q := funext fun M ↦ propext (cmp M)
  have hserre : Q.IsClosedUnderKernels ∧ Q.IsClosedUnderCokernels ∧
      Q.IsClosedUnderExtensions := by
    exact smallIntegralSerre ℓ F X
  have : P.IsClosedUnderKernels := hPQ.symm ▸ hserre.1
  have : P.IsClosedUnderCokernels := hPQ.symm ▸ hserre.2.1
  have : P.IsClosedUnderExtensions := hPQ.symm ▸ hserre.2.2
  -- Use transport on module objects directly, without bounded six-functor imports.
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦
    (cmp _).mpr (_root_.constructible_of_iso e ((cmp _).mp h))⟩
  have : P.ContainsZero := ⟨⟨0, isZero_zero _,
    (cmp _).mpr (isConstructibleModuleObject_of_isZero R (isZero_zero _))⟩⟩
  have hsmall := constructibleModuleObjects_essentiallySmall X R
  have : ObjectProperty.EssentiallySmall.{u + 1} P := hPQ.symm ▸ hsmall
  exact serreHeart A P

private theorem canonicalFieldHeart
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F]
    [Algebra ℚ_[ℓ] F] [FiniteDimensional ℚ_[ℓ] F]
    (X : Scheme.{u}) [IsNoetherian X] :
    letI := spectralNorm.normedField (Padic ℓ) F
    let Λ := Profinite.continuousMapRingObj.{u} (Padic.coefficientExtensionIntegers ℓ F)
    let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
    let P : ObjectProperty A := IsConstantModelConstructible Λ X
    let T := constantModelBoundedConstructible Λ X
    T.IsClosedUnderIsomorphisms ∧ T.IsTriangulated ∧
    (∀ K, T K → DerivedCategory.TStructure.t.bounded K ∧ ∀ n : ℤ,
      T ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      T ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
    (P.ι ⋙ DerivedCategory.singleFunctor A 0).Full ∧
    (P.ι ⋙ DerivedCategory.singleFunctor A 0).Faithful ∧
    (∀ K, (P.ι ⋙ DerivedCategory.singleFunctor A 0).essImage K ↔
      T K ∧ DerivedCategory.TStructure.t.le 0 K ∧ DerivedCategory.TStructure.t.ge 0 K) ∧
    Nonempty (Abelian P.FullSubcategory) ∧ P.IsClosedUnderKernels ∧
    P.IsClosedUnderCokernels ∧ P.IsClosedUnderExtensions ∧
    EssentiallySmall.{u + 1} P.FullSubcategory := by
  let : NormedField F := spectralNorm.normedField (Padic ℓ) F
  let : NormedAlgebra (Padic ℓ) F := spectralNorm.normedAlgebra (Padic ℓ) F
  exact smallFieldHeart ℓ F X

end AlgebraicGeometry.ProEtale
