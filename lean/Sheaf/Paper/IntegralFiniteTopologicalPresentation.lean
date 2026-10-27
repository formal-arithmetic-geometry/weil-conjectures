/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.Paper.IntegralFiniteScalarModelDefinitions
public import Sheaf.NumberTheory.Padics.FiniteIntegralCondensedResolution
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Arithmetic and condensed finite free resolution data -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

private def sectionsLinear
    {A T U : Type u} [CommRing A] [CommRing T] [CommRing U]
    [TopologicalSpace A] [TopologicalSpace T] [TopologicalSpace U]
    [IsTopologicalRing A] [IsTopologicalRing T] [IsTopologicalRing U]
    [Algebra A T] [Algebra A U] [ContinuousSMul A T] [ContinuousSMul A U]
    (f : T →L[A] U) (S : Profinite.{u}) :
    C(S, T) →ₗ[C(S, A)] C(S, U) where
  toFun a := (⟨fun x ↦ f x, f.continuous⟩ : C(T, U)).comp a
  map_add' a b := by ext s; exact map_add f _ _
  map_smul' a b := by ext s; exact f.map_smul (a s) (b s)

private noncomputable def sectionsMap
    {A T U : Type u} [CommRing A] [CommRing T] [CommRing U]
    [TopologicalSpace A] [TopologicalSpace T] [TopologicalSpace U]
    [IsTopologicalRing A] [IsTopologicalRing T] [IsTopologicalRing U]
    [Algebra A T] [Algebra A U] [ContinuousSMul A T] [ContinuousSMul A U]
    (f : T →L[A] U) :
    Profinite.continuousSectionsModule A T ⟶ Profinite.continuousSectionsModule A U := by
  letI : MonObj (Profinite.continuousCoefficientRingObj T).obj :=
    (Profinite.continuousCoefficientRingSheaf T).obj.monObjCompForget₂
  letI : MonObj (Profinite.continuousCoefficientRingObj U).obj :=
    (Profinite.continuousCoefficientRingSheaf U).obj.monObjCompForget₂
  let k : Profinite.continuousCoefficientRingObj T ⟶ Profinite.continuousCoefficientRingObj U :=
    ⟨{ app S := AddCommGrpCat.ofHom
         { toFun a := ULift.up ((sectionsLinear f S.unop) a.down)
           map_zero' := congrArg ULift.up (map_zero (sectionsLinear f S.unop))
           map_add' a b := congrArg ULift.up (map_add (sectionsLinear f S.unop) _ _) }
       naturality _ _ _ := by
         ext a
         apply ULift.ext
         ext s
         rfl }⟩
  refine Mod.homMk k ?_
  let aT : Profinite.continuousCoefficientRingObj A ⟶ Profinite.continuousCoefficientRingObj T :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMapOfUniverse.{u, u} (algebraMap A T)
        (continuous_algebraMap A T) :
        Profinite.continuousCoefficientRingSheaf A ⟶ Profinite.continuousCoefficientRingSheaf T)
  let aU : Profinite.continuousCoefficientRingObj A ⟶ Profinite.continuousCoefficientRingObj U :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMapOfUniverse.{u, u} (algebraMap A U)
        (continuous_algebraMap A U) :
        Profinite.continuousCoefficientRingSheaf A ⟶ Profinite.continuousCoefficientRingSheaf U)
  change (MonoidalCategory.whiskerRight aT _ ≫ MonObj.mul) ≫ k =
    MonoidalCategory.whiskerLeft _ k ≫
      (MonoidalCategory.whiskerRight aU _ ≫ MonObj.mul)
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc,
    ← Functor.LaxMonoidal.μ_natural_right_assoc,
    ← Functor.LaxMonoidal.μ_natural_left_assoc]
  have hT := Sheaf.μ_comp_map_mul (Profinite.continuousCoefficientRingObj T)
  have hU := Sheaf.μ_comp_map_mul (Profinite.continuousCoefficientRingObj U)
  simp only [reassoc_of% hT, hU]
  ext S : 2
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  intro a b
  change (k.hom.app S)
      ((MonObj.mul : MonoidalCategory.tensorObj (Profinite.continuousCoefficientRingObj T).obj
        (Profinite.continuousCoefficientRingObj T).obj ⟶ _).app S
          ((aT.hom.app S) a ⊗ₜ[ℤ] b)) =
    (MonObj.mul : MonoidalCategory.tensorObj (Profinite.continuousCoefficientRingObj U).obj
      (Profinite.continuousCoefficientRingObj U).obj ⟶ _).app S
        ((aU.hom.app S) a ⊗ₜ[ℤ] (k.hom.app S) b)
  apply ULift.ext
  ext s
  change f (algebraMap A T (a.down s) * b.down s) =
    algebraMap A U (a.down s) * f (b.down s)
  simpa only [Algebra.smul_def] using f.map_smul (a.down s) (b.down s)

private theorem continuousFiniteFreeSections (O : Type u) [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (r : ℕ) :
    letI : HasFiniteBiproducts (PointModules (condensed O)) := .of_hasFiniteProducts
    Nonempty (Profinite.continuousSectionsModule O (Fin r → O) ≅
      biproduct (fun _i : Fin r ↦ Mod.regular (Profinite.continuousCoefficientRingObj O))) := by
  classical
  let R := Profinite.continuousCoefficientRingObj O
  have hρ : (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
          (algebraMap O O) (continuous_algebraMap O O)) = 𝟙 R := by
    ext S f
    rfl
  let eR : Profinite.continuousSectionsModule O O ≅ Mod.regular R :=
    Mod.isoMk (Iso.refl R) (by
      change (_ ≫ _) ≫ 𝟙 R = _
      rw [hρ]
      change (MonoidalCategory.whiskerRight (𝟙 R) R) ≫ MonObj.mul =
        (MonoidalCategory.whiskerLeft R (𝟙 R)) ≫ MonObj.mul
      simp only [MonoidalCategory.id_whiskerRight,
        MonoidalCategory.whiskerLeft_id, Category.id_comp])
  let π : (i : Fin r) →
      Profinite.continuousSectionsModule O (Fin r → O) ⟶ Mod.regular R :=
    fun i ↦ sectionsMap (ContinuousLinearMap.proj i) ≫ eR.hom
  let ι : (i : Fin r) →
      Mod.regular R ⟶ Profinite.continuousSectionsModule O (Fin r → O) :=
    fun i ↦ eR.inv ≫ sectionsMap
    (ContinuousLinearMap.single O (fun _ : Fin r ↦ O) i)
  let B : Bicone (fun _i : Fin r ↦ Mod.regular R) :=
    { pt := Profinite.continuousSectionsModule O (Fin r → O)
      π := π
      ι := ι
      ι_π := by
        intro i j
        apply Mod.hom_ext
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro s
        change (Pi.single i (f.down s) : Fin r → O) j = _
        split_ifs with h
        · subst j; simp
        · simp [h] }
  refine ⟨biproduct.uniqueUpToIso _ (isBilimitOfTotal B ?_)⟩
  apply Mod.hom_ext
  ext S f
  apply ULift.ext
  apply ContinuousMap.ext
  intro s
  let ev : (B.pt ⟶ B.pt) →+ (Fin r → O) :=
    { toFun g := ((g.hom.hom.app S) f).down s
      map_zero' := rfl
      map_add' _ _ := rfl }
  change ev (∑ i : Fin r, B.π i ≫ B.ι i) = f.down s
  rw [map_sum]
  change (∑ i : Fin r, (Pi.single i (f.down s i) : Fin r → O)) = f.down s
  exact Finset.univ_sum_single _

/-- The arithmetic and condensed short exact data of the perfect model, before any
passage to derived categories.
Source: scalar-six direct-image proof, integral-to-finite bullet
(blueprint: lem-sfb-integral-finite-scalar-arithmetic). -/
def PerfectModelArithmetic (O A : Type u) [CommRing O] [CommRing A]
    [TopologicalSpace O] [TopologicalSpace A] [IsTopologicalRing O] [IsTopologicalRing A]
    (a : O →+* A) (ha : Continuous a) : Prop :=
  letI := a.toAlgebra
  letI := continuousSMul_of_algebraMap O A ha
  letI : HasFiniteBiproducts (PointModules (condensed O)) := .of_hasFiniteProducts
  ∃ (r : ℕ) (q : (Fin r → O) →L[O] A) (φ : (Fin r → O) →L[O] (Fin r → O)),
    Function.Surjective q ∧ Function.Injective φ ∧ Function.Exact φ q ∧
    (∃ M : Matrix (Fin r) (Fin r) O, ∀ x : Fin r → O, φ x = M.mulVec x) ∧
    Nonempty (Profinite.continuousSectionsModule O (Fin r → O) ≅
      biproduct (fun _i : Fin r ↦ Mod.regular (Profinite.continuousCoefficientRingObj O))) ∧
    (Subsingleton A → r = 0) ∧
    ∃ (F : Profinite.continuousSectionsModule O (Fin r → O) ⟶
          Profinite.continuousSectionsModule O (Fin r → O))
       (G : Profinite.continuousSectionsModule O (Fin r → O) ⟶
          Profinite.continuousSectionsModule O A)
       (h : F ≫ G = 0)
       (t : (ShortComplex.mk F G h).X₃ ≅
          (Mod.comap (condensedMap a ha).hom.hom).obj
            (Mod.regular (Profinite.continuousCoefficientRingObj A))),
      (∀ (S : Profinite.{u}) (v : ULift.{u + 1} C(S, Fin r → O)) (s : S),
        ((F.hom.hom.app (op S)) v).down s = φ (v.down s)) ∧
      (∀ (S : Profinite.{u}) (v : ULift.{u + 1} C(S, Fin r → O)) (s : S),
        ((G.hom.hom.app (op S)) v).down s = q (v.down s)) ∧
      t.hom.hom = 𝟙 (Profinite.continuousCoefficientRingObj A) ∧
      (ShortComplex.mk F G h).ShortExact

/-- The arithmetic and sectionwise data of the integral finite perfect model.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-direct-image.proof.md, integral-to-finite bullet
(blueprint: lem-sfb-integral-finite-scalar-arithmetic).

Proof: use the proved finite integral condensed resolution for nonzero A. For zero A,
take rank zero, zero continuous maps, and the unique homeomorphism onto the zero kernel.
Coordinate projections and inclusions identify the continuous-section free module with
the finite biproduct of the regular module, also in rank zero. The continuous-sections
short-exact theorem gives the specified arrows and exactness. The quotient module is
definitionally the restricted regular A-module, so its identification has identity
underlying map. These are precisely the asserted arithmetic data. -/
theorem perfectModelArithmetic_of_finite_integral
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (a : Padic.coefficientExtensionIntegers ell E →+* A)
    (ha : @Continuous _ _ (Padic.coefficientExtensionIntegersTopology ell E) inferInstance a)
    (_hpow : ∃ n : ℕ, (ell : A) ^ n = 0) :
    @PerfectModelArithmetic (Padic.coefficientExtensionIntegers ell E) A
      inferInstance inferInstance (Padic.coefficientExtensionIntegersTopology ell E) inferInstance
      (by
        let := spectralNorm.normedField (Padic ell) E
        exact inferInstanceAs (IsTopologicalRing (Padic.coefficientExtensionIntegers ell E)))
      inferInstance a ha := by
  classical
  let := Padic.coefficientExtensionIntegersTopology ell E
  let O := Padic.coefficientExtensionIntegers ell E
  let : IsTopologicalRing O := Padic.finiteIntegralIntegersTopologicalRing ell E
  let := a.toAlgebra
  let := continuousSMul_of_algebraMap O A ha
  let : HasFiniteBiproducts (PointModules (condensed O)) := .of_hasFiniteProducts
  have hpres : ∃ (r : ℕ) (q : (Fin r → O) →L[O] A)
      (φ : (Fin r → O) →L[O] (Fin r → O)),
      Function.Surjective q ∧ Function.Injective φ ∧ Function.Exact φ q ∧
      (∃ M : Matrix (Fin r) (Fin r) O, ∀ x, φ x = M.mulVec x) ∧
      (Subsingleton A → r = 0) ∧
      ∃ e : (Fin r → O) ≃ₜ LinearMap.ker q.toLinearMap,
        ∀ x, (e x).val = φ x := by
    by_cases hA : Subsingleton A
    · let := hA
      let q : (Fin 0 → O) →L[O] A := 0
      let φ : (Fin 0 → O) →L[O] (Fin 0 → O) := 0
      refine ⟨0, q, φ, ?_, ?_, ?_, ?_, fun _ ↦ rfl, ?_⟩
      · intro y
        exact ⟨0, Subsingleton.elim _ _⟩
      · exact fun _ _ _ ↦ Subsingleton.elim _ _
      · intro y
        exact ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
      · exact ⟨0, fun _ ↦ Subsingleton.elim _ _⟩
      · let e : (Fin 0 → O) ≃ₗ[O] LinearMap.ker q.toLinearMap :=
          LinearEquiv.ofSubsingleton _ _
        exact ⟨{ e.toEquiv with
          continuous_toFun :=
            (show Continuous (fun _ : (Fin 0 → O) ↦ (0 : LinearMap.ker q.toLinearMap))
              from continuous_const).congr (fun _ ↦ Subsingleton.elim _ _)
          continuous_invFun :=
            (show Continuous (fun _ : LinearMap.ker q.toLinearMap ↦ (0 : Fin 0 → O))
              from continuous_const).congr (fun _ ↦ Subsingleton.elim _ _) },
          fun _ ↦ Subsingleton.elim _ _⟩
    · obtain ⟨r, q, φ, hq, hφ, hex, hmatrix, hker, _hsections, _hfree, _hcond⟩ :=
        Padic.finite_integral_condensed_resolution ell E A a ha
      exact ⟨r, q, φ, hq, hφ, hex, hmatrix, fun h ↦ (hA h).elim, hker⟩
  obtain ⟨r, q, φ, hq, hφ, hex, hmatrix, hzero, hker⟩ := hpres
  have hrange : LinearMap.range φ.toLinearMap = LinearMap.ker q.toLinearMap :=
    (LinearMap.exact_iff.mp hex).symm
  obtain ⟨F, G, h, hF, hG, hS⟩ :=
    (Profinite.continuousSections_finiteDiscrete_shortExact O (Fin r → O) (Fin r → O) A
      φ q hφ hq hrange hker).2
  obtain ⟨e⟩ := continuousFiniteFreeSections O r
  let t : (ShortComplex.mk F G h).X₃ ≅
      (Mod.comap (condensedMap a ha).hom.hom).obj
        (Mod.regular (Profinite.continuousCoefficientRingObj A)) := Iso.refl _
  exact ⟨r, q, φ, hq, hφ, hex, hmatrix, ⟨e⟩, hzero, F, G, h, t, hF, hG, rfl, hS⟩

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
