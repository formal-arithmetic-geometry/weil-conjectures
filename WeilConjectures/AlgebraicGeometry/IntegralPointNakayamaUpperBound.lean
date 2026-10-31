/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import WeilConjectures.CategoryTheory.DerivedNakayamaUpperBound
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.WeilObject.Sheaf.Stalk
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ConstructibleNakayama
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # Integral Nakayama at a geometric point

Source: current blueprint, sk-lem-finite.proof.md, integral Complement, residue reduction
and Nakayama (blueprint: lem-sf-integral-point-nakayama-upper-bound).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

private def constantSections (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (S : Profinite.{u}ᵒᵖ) :
    A →+* (Profinite.continuousCoefficientRingSheaf A).obj.obj S where
  toFun a := ULift.up (ContinuousMap.const _ a)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private def constantGlobal (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : A →+* MonObj.Γ (Profinite.continuousCoefficientRingObj A) :=
  Sheaf.ringHomΓSheafCompose (coherentTopology Profinite.{u})
    (Profinite.continuousCoefficientRingSheaf A) (constantSections A) fun _ _ ↦ rfl

private theorem constantGlobal_bijective (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : Function.Bijective (constantGlobal A) := by
  constructor
  · intro a b hab
    have h := congrArg (fun x : MonObj.Γ (Profinite.continuousCoefficientRingObj A) ↦
      Functor.LaxMonoidal.ε (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
        (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map x.hom) hab
    change _ ≫ (sheafToPresheaf _ _).map
        (Sheaf.ringHomΓSheafCompose _ _ (constantSections A) (fun _ _ ↦ rfl) a).hom =
      _ ≫ (sheafToPresheaf _ _).map
        (Sheaf.ringHomΓSheafCompose _ _ (constantSections A) (fun _ _ ↦ rfl) b).hom at h
    rw [Sheaf.ε_comp_ringHomΓSheafCompose_hom,
      Sheaf.ε_comp_ringHomΓSheafCompose_hom] at h
    have hv := congrArg (fun t ↦
      (t.app (op (Profinite.of PUnit.{u + 1})) (ULift.up 1)).down PUnit.unit) h
    dsimp [Functor.ringHomΓCompForget₂, constantSections, AddMonoidHom.mulRight,
      AddEquiv.ulift, Equiv.ulift] at hv
    simp only [Int.cast_one] at hv
    change (1 : A) * a = (1 : A) * b at hv
    simpa only [one_mul] using hv
  · intro x
    let adj := sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}
    let x' := adj.homEquiv _ _
      (inv (Functor.LaxMonoidal.ε
        (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) ≫ x.hom)
    let b := x'.app (op (Profinite.of PUnit.{u + 1})) (ULift.up 1)
    refine ⟨b.down PUnit.unit, ?_⟩
    have hx : x' = (Functor.ringHomΓCompForget₂
        (Profinite.continuousCoefficientRingSheaf A).obj
        (constantSections A) (fun _ _ ↦ rfl) (b.down PUnit.unit)).hom := by
      ext S n
      obtain ⟨m⟩ := n
      have key : x'.app S (ULift.up 1) =
          (Profinite.continuousCoefficientRingObj A).obj.map
            (Profinite.isTerminalPUnit.from S.unop).op b :=
        NatTrans.naturality_apply x' (Profinite.isTerminalPUnit.from S.unop).op (ULift.up 1)
      have hm : (ULift.up m : ULift.{u + 1} ℤ) = m • ULift.up 1 := by
        ext
        simp
      refine (congrArg (x'.app S) hm).trans ?_
      rw [map_zsmul, key]
      exact (zsmul_eq_mul
        (α := (Profinite.continuousCoefficientRingPresheaf A).obj S) _ m).trans rfl
    ext1
    rw [constantGlobal, Sheaf.ringHomΓSheafCompose, RingHom.comp_apply,
      RingHom.comp_apply, MonObj.Γ.map_hom, MonObj.Γ.mapFunctor_hom, ← hx, Category.assoc,
      Sheaf.sheafifyRingPresheafIso, asIso_hom, ← Adjunction.homEquiv_counit,
      Equiv.symm_apply_apply, IsIso.hom_inv_id_assoc]

private def constantGlobalEquiv (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : A ≃+* MonObj.Γ (Profinite.continuousCoefficientRingObj A) :=
  RingEquiv.ofBijective (constantGlobal A) (constantGlobal_bijective A)

private def globalValueEquiv (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    MonObj.Γ (Profinite.continuousCoefficientRingObj A) ≃+* A :=
  (constantGlobalEquiv A).symm

private def coefficientPostcomposeSheaf {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) :
    Profinite.continuousCoefficientRingSheaf A ⟶
      Profinite.continuousCoefficientRingSheaf B :=
  ⟨{ app := fun _ ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((f.compLeftContinuous _ hf).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

private def coefficientPostcompose {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) :
    Profinite.continuousCoefficientRingObj A ⟶ Profinite.continuousCoefficientRingObj B :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (coefficientPostcomposeSheaf f hf)

private instance continuousMap_isMonHom {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) : IsMonHom (coefficientPostcompose f hf) :=
  Sheaf.isMonHom_sheafCompose_map _ (coefficientPostcomposeSheaf f hf)

private theorem globalValue_natural {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f)
    (x : MonObj.Γ (Profinite.continuousCoefficientRingObj A)) :
    globalValueEquiv B
      (MonObj.Γ.map (coefficientPostcompose f hf) x) =
        f (globalValueEquiv A x) := by
  apply (constantGlobalEquiv B).injective
  change (constantGlobalEquiv B) ((constantGlobalEquiv B).symm _) = _
  rw [RingEquiv.apply_symm_apply]
  have h := Sheaf.Γ_map_ringHomΓSheafCompose (coherentTopology Profinite.{u})
    (coefficientPostcomposeSheaf f hf) (constantSections A) (fun _ _ ↦ rfl)
    (constantSections B) (fun _ _ ↦ rfl)
    (r := globalValueEquiv A x) (r' := f (globalValueEquiv A x)) (fun _ ↦ rfl)
  change MonObj.Γ.map (coefficientPostcompose f hf)
      ((constantGlobalEquiv A) ((constantGlobalEquiv A).symm x)) = _ at h
  simpa [constantGlobalEquiv, constantGlobal] using h

private def functionValueEquiv (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : C(PUnit.{1}, A) ≃+* A where
  toFun f := f PUnit.unit
  invFun a := ContinuousMap.const _ a
  left_inv f := ContinuousMap.ext fun _x ↦ congrArg f (Subsingleton.elim _ _)
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private theorem finitePresentation_nakayama
    (A B : Type u) [CommRing A] [Field B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [DiscreteTopology B] (f : A →+* B) (hf : Continuous f)
    (hsurj : Function.Surjective f) (hunit : ∀ a, IsUnit (f a) → IsUnit a)
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (Profinite.continuousCoefficientRingObj A))
    (hM : Mod.IsFinitelyPresented _ M)
    (hz : IsZero ((Mod.extendScalars
      (coefficientPostcompose f hf)).obj M)) : IsZero M := by
  let a := coefficientPostcompose f hf
  let rA := (globalValueEquiv A).symm.toRingHom.comp (functionValueEquiv A).toRingHom
  let rB := (globalValueEquiv B).symm.toRingHom.comp (functionValueEquiv B).toRingHom
  have hrA : Function.Bijective rA :=
    (globalValueEquiv A).symm.bijective.comp (functionValueEquiv A).bijective
  have hrB : Function.Bijective rB :=
    (globalValueEquiv B).symm.bijective.comp (functionValueEquiv B).bijective
  refine Mod.isZero_of_isFinitelyPresented_of_isZero_extendScalars_of_continuousMap
    a f hf hsurj hunit (fun d hd ↦ ?_)
    (Mod.regularEndRingHom.comp rA) (Mod.regularEndRingHom_bijective.comp hrA)
    (Mod.regularEndRingHom.comp rB) (Mod.regularEndRingHom_bijective.comp hrB).1
    (fun g ↦ ?_) M hM hz
  · exact ((hd PUnit.unit).map (functionValueEquiv A).symm.toRingHom)
  · have hnat : MonObj.Γ.map a (rA g) =
        rB ((⟨f, hf⟩ : C(A, B)).comp g) := by
      apply (globalValueEquiv B).injective
      rw [globalValue_natural]
      simp only [rA, rB, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
      rfl
    simpa only [RingHom.comp_apply, hnat] using
      Mod.extendScalarsObjRegularIso_inv_comp_map a (rA g)

private theorem point_global_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k)))) :
    IsConstantModelConstructible Λ (Spec (.of k)) M ↔
      ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
        Mod.IsFinitelyPresented Λ P ∧
          Nonempty (((upperStarFromPoint (Spec (.of k))).mapMod Λ).obj P ≅ M) := by
  classical
  have hqc : CompactSpace (Spec (.of k)) ∧ QuasiSeparatedSpace (Spec (.of k)) :=
    ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hqc]
  constructor
  · rintro ⟨S, hS⟩
    obtain ⟨z⟩ : Nonempty (Spec (.of k)) := inferInstance
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp
      (S.iUnion_stratum_eq_univ ▸ Set.mem_univ z)
    rw [← S.range_immersion a] at ha
    obtain ⟨y, hy⟩ := Scheme.exists_comp_eq_of_mem_range_of_isField
      (S.immersion a) (Field.toIsField k) (𝟙 _) z ha
    obtain ⟨𝒰, h𝒰⟩ := hS a
    obtain ⟨i, g, hg⟩ := 𝒰.exists_comp_eq_of_isSepClosed_of_proetale y
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    let G := CondensedRing.upperStar Λ g
    let N := (CondensedRing.upperStar Λ (𝒰.f i)).obj
      ((CondensedRing.upperStar Λ (S.immersion a)).obj M)
    let e : G.obj N ≅ M :=
      G.mapIso ((CondensedRing.upperStarComp Λ (𝒰.f i) (S.immersion a)).app M).symm ≪≫
        ((CondensedRing.upperStarComp Λ g (𝒰.f i ≫ S.immersion a)).app M).symm ≪≫
        eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M)
          (by rw [reassoc_of% hg, hy])) ≪≫ (CondensedRing.upperStarId Λ _).app M
    exact ⟨P, hP, ⟨((CondensedRing.upperStarFromPointModComp Λ g).app P).symm ≪≫
      G.mapIso eP.symm ≪≫ e⟩⟩
  · rintro ⟨P, hP, ⟨eP⟩⟩
    refine ⟨Scheme.Stratification.trivial _, fun a ↦ ?_⟩
    refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
    refine ⟨P, hP, ⟨?_⟩⟩
    exact (CondensedRing.upperStarId Λ _).app _ ≪≫
      (CondensedRing.upperStarId Λ _).app _ ≪≫ eP.symm

private theorem geometricPoint_nakayama
    (A B : Type u) [CommRing A] [Field B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [DiscreteTopology B] (f : A →+* B) (hf : Continuous f)
    (hsurj : Function.Surjective f) (hunit : ∀ a, IsUnit (f a) → IsUnit a)
    (k : Type u) [Field k] [IsAlgClosed k]
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) (Spec (.of k))))
    (hM : IsConstantModelConstructible (Profinite.continuousCoefficientRingObj A)
      (Spec (.of k)) M)
    (hz : IsZero ((Mod.extendScalars (coefficientMap
      (coefficientPostcompose f hf) (Spec (.of k)))).obj M)) :
    IsZero M := by
  let a := coefficientPostcompose f hf
  let H := (upperStarFromPoint (Spec (.of k))).mapMod
    (Profinite.continuousCoefficientRingObj A)
  obtain ⟨P, hP, ⟨eP⟩⟩ :=
    (point_global_model _ k M).mp hM
  have hz' : IsZero ((Mod.extendScalars (coefficientMap a (Spec (.of k)))).obj
      (H.obj P)) := hz.of_iso ((Mod.extendScalars _).mapIso eP)
  let adj := Mod.extendRestrictAdjunction a
  let adj' := Mod.extendRestrictAdjunction (coefficientMap a (Spec (.of k)))
  let c := (upperStarFromPoint (Spec (.of k))).mapModComapIso a
  let g := H.map (adj.unit.app P) ≫ c.hom.app ((Mod.extendScalars a).obj P)
  have hg : g = 0 := by
    have hzero : (adj'.homEquiv _ _).symm g = 0 := hz'.eq_of_src _ _
    rw [← (adj'.homEquiv _ _).apply_symm_apply g, hzero,
      Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  have hunitP : adj.unit.app P = 0 := by
    apply H.map_injective
    rw [H.map_zero]
    exact (cancel_mono (c.hom.app ((Mod.extendScalars a).obj P))).mp
      (hg.trans (zero_comp).symm)
  have hzP : IsZero ((Mod.extendScalars a).obj P) := by
    rw [IsZero.iff_id_eq_zero, ← adj.left_triangle_components P, hunitP,
      Functor.map_zero, zero_comp]
  exact (H.map_isZero (finitePresentation_nakayama A B f hf hsurj hunit P hP hzP)).of_iso
    eP.symm

/-- At a geometric point, the first uniformizer reduction reflects upper cohomological
bounds on bounded constructible integral complexes.

Source: blueprint sk-lem-finite.proof.md, integral Complement, top-cohomology Nakayama.

Proof: a constructible sheaf on an algebraically closed point is the pullback of a finite
presentation on the condensed point. Maps between finite free modules there are scalar
matrices. Reduction is the residue-field map of a local ring, so matrix Nakayama shows
that zero ordinary reduction forces the sheaf to vanish. Apply upper-bound derived
Nakayama: in any highest degree above b the ordinary reduction of the cohomology sheaf
vanishes by orthogonality, and descending induction lowers the upper bound to b.
(blueprint: lem-sf-integral-point-nakayama-upper-bound)
-/
theorem integral_point_isLE_of_residue_isLE
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] [IsAlgClosed k]
    (K : DerivedCategory (AdicCompletion.Modules l E (Spec (.of k))))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E)
      (Spec (.of k)) K) (b : ℤ)
    [((AdicCompletion.derivedReduction l E (Spec (.of k)) 0).obj K).IsLE b] :
    K.IsLE b := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionIntegers l E
  let B := Padic.coefficientExtensionRing l E 1
  have h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  let : IsLocalRing A := h.2.2.2.1
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : (Padic.coefficientExtensionIdeal l E 1).IsMaximal := by
    change (Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1).IsMaximal
    rw [pow_one, hgen]
    exact h.2.2.2.2.1
  let : Field B := @Ideal.Quotient.field _ _ _ hm
  let : DiscreteTopology B := DerivedNakayama.quotientDiscrete l E 1
  let f := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)
  have hf : Continuous f := continuous_quot_mk
  have hlocal : IsLocalHom f := IsLocalHom.of_surjective f Ideal.Quotient.mk_surjective
  exact Mod.isLE_of_leftDerivedFunctor_extendScalars_isLE
    (AdicCompletion.quotient l E (Spec (.of k)) 0)
    (IsConstantModelConstructible (DerivedNakayama.integerRing l E) (Spec (.of k)))
    (fun M hM hz ↦ geometricPoint_nakayama A B f hf Ideal.Quotient.mk_surjective
      (fun x hx ↦ IsLocalHom.map_nonunit (f := f) x hx) k M hM hz) K hK.1.2 hK.2 b

end AlgebraicGeometry.ProEtale.CondensedRing
