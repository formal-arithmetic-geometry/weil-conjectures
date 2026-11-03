/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentReduction.CoherentMappingSystems
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! # Native and continuous spectral integral coefficient presentations

Source: Bhatt--Scholze, Definition 6.5.1 and Section 6.8.
(blueprint: lem-sfb-coherent-integral-native-presentation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CoherentReduction
attribute [local instance] proEtSmall sequenceSmall

private theorem nativeSpectralNorm
    (ell : ℕ) [Fact ell.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ell)] [Algebra ℚ_[ell] E]
    [IsScalarTower ℚ_[ell] E (PadicAlgCl ell)] [FiniteDimensional ℚ_[ell] E]
    (x : ULift.{u + 1} E) :
    Padic.coefficientExtensionAbsoluteValue ell (ULift.{u + 1} E) x =
      ‖algebraMap E (PadicAlgCl ell) x.down‖ := by
  let f : ULift.{u + 1} E →+* PadicAlgCl ell :=
    (algebraMap E (PadicAlgCl ell)).comp ULift.ringEquiv.toRingHom
  let a : AbsoluteValue (ULift.{u + 1} E) ℝ :=
    { toFun := fun x ↦ ‖f x‖
      map_mul' := fun x y ↦ by rw [map_mul, norm_mul]
      nonneg' := fun x ↦ norm_nonneg _
      eq_zero' := fun x ↦ by simp only [norm_eq_zero, map_eq_zero_iff f f.injective]
      add_le' := fun x y ↦ by rw [map_add]; exact norm_add_le _ _ }
  have ha : ∀ y : ℚ_[ell], a (algebraMap ℚ_[ell] (ULift.{u + 1} E) y) = ‖y‖ := by
    intro y
    change ‖algebraMap E (PadicAlgCl ell) (algebraMap ℚ_[ell] E y)‖ = ‖y‖
    rw [← IsScalarTower.algebraMap_apply ℚ_[ell] E (PadicAlgCl ell)]
    exact PadicAlgCl.norm_extends ell y
  exact (spectralNorm_unique_field_norm_ext ha x).symm

private def nativeIntegerEquiv
    (ell : ℕ) [Fact ell.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ell)] [Algebra ℚ_[ell] E]
    [IsScalarTower ℚ_[ell] E (PadicAlgCl ell)] [FiniteDimensional ℚ_[ell] E] :
    Padic.coefficientExtensionIntegers ell (ULift.{u + 1} E) ≃+* PadicAlgCl.integers ell E := by
  have hm (x : ULift.{u + 1} E) :
      x ∈ Padic.coefficientExtensionIntegers ell (ULift.{u + 1} E) ↔
        x.down ∈ PadicAlgCl.integers ell E := by
    have h := (Padic.extension_integers_dvr ell (ULift.{u + 1} E)
      (Padic.coefficientExtensionAbsoluteValue ell (ULift.{u + 1} E))
      (spectralNorm_extends (K := ℚ_[ell]) (L := ULift.{u + 1} E))
      ).choose_spec.choose_spec.1 x
    rw [nativeSpectralNorm] at h
    exact h.trans (by
      rw [PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe]
      rfl)
  exact
    { toFun := fun x ↦ ⟨x.val.down, (hm x.val).mp x.property⟩
      invFun := fun x ↦ ⟨ULift.up x.val, (hm _).mpr x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }

private theorem continuousPresheaf_isSheaf
    (T : Type (u + 1)) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] :
    Presheaf.IsSheaf (coherentTopology Profinite.{u}) (continuousPresheaf T) := by
  apply Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp
    (continuousPresheaf T) (forget CommRingCat.{u + 1})
  change Presheaf.IsSheaf (coherentTopology Profinite.{u})
    (ContinuousMap.yonedaPresheaf Profinite.toTopCat.{u} T)
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
  refine ⟨inferInstance, ?_⟩
  apply +allowSynthFailures equalizerCondition_yonedaPresheaf Profinite.toTopCat.{u} T
  intro Z B π hπ
  exact .of_surjective_continuous (((Profinite.effectiveEpi_tfae π).out 0 2).mp hπ)
    π.hom.hom.continuous

private def nativePointIso
    (ell : ℕ) [Fact ell.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ell)] [Algebra ℚ_[ell] E]
    [IsScalarTower ℚ_[ell] E (PadicAlgCl ell)] [FiniteDimensional ℚ_[ell] E] :
    Mon.mk (abelianPoint (Padic.coefficientExtensionIntegers ell (ULift.{u + 1} E))) ≅
      Mon.mk (Profinite.padicIntegersRingObj.{u} ell E) := by
  letI src := PadicAlgCl.normedFieldOfAlgebra ell E
  letI tgt := spectralNorm.normedField ℚ_[ell] (ULift.{u + 1} E)
  letI : TopologicalSpace (ULift.{u + 1} E) :=
    tgt.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let e := nativeIntegerEquiv.{u} ell E
  let sm : MetricSpace (Padic.coefficientExtensionIntegers ell (ULift.{u + 1} E)) :=
    @Subtype.metricSpace (ULift.{u + 1} E) _ tgt.toMetricSpace
  let tm : MetricSpace (PadicAlgCl.integers ell E) :=
    @Subtype.metricSpace E _ src.toMetricSpace
  letI : PseudoEMetricSpace
      (Padic.coefficientExtensionIntegers ell (ULift.{u + 1} E)) :=
    sm.toPseudoMetricSpace.toPseudoEMetricSpace
  letI : PseudoEMetricSpace (PadicAlgCl.integers ell E) :=
    tm.toPseudoMetricSpace.toPseudoEMetricSpace
  have hi : @Isometry _ _ sm.toPseudoMetricSpace.toPseudoEMetricSpace
      tm.toPseudoMetricSpace.toPseudoEMetricSpace e := by
    apply @Isometry.of_dist_eq _ _ sm.toPseudoMetricSpace tm.toPseudoMetricSpace
    intro x y
    change dist (algebraMap E (PadicAlgCl ell) x.val.down)
      (algebraMap E (PadicAlgCl ell) y.val.down) =
      spectralNorm ℚ_[ell] (ULift.{u + 1} E) (x.val - y.val)
    rw [dist_eq_norm, ← map_sub]
    exact (nativeSpectralNorm ell E (x.val - y.val)).symm
  have hii := hi.right_inv e.apply_symm_apply
  let P : Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} :=
    ⟨continuousPresheaf (Padic.coefficientExtensionIntegers ell (ULift.{u + 1} E)),
      continuousPresheaf_isSheaf _⟩
  let α := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (sheafificationIso P).symm
  let forward (S : Profinite.{u}ᵒᵖ) :
      C(S.unop, Padic.coefficientExtensionIntegers ell (ULift.{u + 1} E)) →+*
        ULift.{u + 1} C(S.unop, PadicAlgCl.integers ell E) :=
    ULift.ringEquiv.symm.toRingHom.comp
      (e.toRingHom.compLeftContinuous S.unop hi.continuous)
  let backward (S : Profinite.{u}ᵒᵖ) :
      ULift.{u + 1} C(S.unop, PadicAlgCl.integers ell E) →+*
        C(S.unop, Padic.coefficientExtensionIntegers ell (ULift.{u + 1} E)) :=
    (e.symm.toRingHom.compLeftContinuous S.unop hii.continuous).comp
      ULift.ringEquiv.toRingHom
  let β : (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj P ≅
      Profinite.padicIntegersCondensedRing.{u} ell E :=
    { hom := ⟨{ app := fun S ↦ RingCat.ofHom (forward S)
                naturality := by intros; ext x; rfl }⟩
      inv := ⟨{ app := fun S ↦ RingCat.ofHom (backward S)
                naturality := by intros; ext x; rfl }⟩
      hom_inv_id := by
        ext S f
        rfl
      inv_hom_id := by
        ext S f
        apply ULift.ext
        ext x
        rfl }
  let γ := α ≪≫ β
  let δ := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso γ
  have : IsMonHom δ.hom := Sheaf.isMonHom_sheafCompose_map _ γ.hom
  have : IsMonHom δ.inv := Sheaf.isMonHom_sheafCompose_map _ γ.inv
  exact
    { hom := Mon.ofHom δ.hom
      inv := Mon.ofHom δ.inv
      hom_inv_id := Mon.Hom.ext δ.hom_inv_id
      inv_hom_id := Mon.Hom.ext δ.inv_hom_id }

private theorem boundedConstructible_comap_iff {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)) :
    boundedConstructible S ((Mod.comap φ).mapDerivedCategory.obj K) ↔
      boundedConstructible R K := by
  let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) φ
  constructor
  · intro h
    refine ⟨G.bounded_of_bounded_mapDerivedCategory_obj h.1, fun q ↦ ?_⟩
    have hm := constructible_of_iso ((G.mapDerivedCategoryHomologyFunctorIso q).app K).symm
      (h.2 q)
    exact constructible_of_iso
      (((Mod.comapComp (inv φ) φ).symm ≪≫ Mod.comapCongr (IsIso.inv_hom_id φ) ≪≫
        Mod.comapId R).app ((DerivedCategory.homologyFunctor _ q).obj K))
      (constructible_comap (inv φ) hm)
  · intro h
    refine ⟨G.bounded_mapDerivedCategory_obj h.1, fun q ↦ ?_⟩
    exact constructible_of_iso ((G.mapDerivedCategoryHomologyFunctorIso q).app K)
      (constructible_comap φ (h.2 q))

private def coefficientBcEquivalence {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : S ⟶ R) [IsMonHom φ] [IsIso φ] :
    BoundedConstructible R ≌ BoundedConstructible S := by
  let e := Mod.comapEquivalenceOfIsIso φ
  let : e.functor.Additive := inferInstanceAs (Mod.comap φ).Additive
  exact e.mapDerivedCategory.congrFullSubcategory (by
    ext K
    exact boundedConstructible_comap_iff φ K)

/-- The native embedded integral coefficient ring and the continuous spectral
coefficient ring present the same bounded constructible categories and direct images.

Source: Bhatt--Scholze, Definition 6.5.1; coefficient presentation sub-step of
lem-sfb-dc-proper-pushforward-left-adjoint-oe-general-field.
(blueprint: lem-sfb-coherent-integral-native-presentation)

Proof: uniqueness of the extension of the ell-adic absolute value to the finite
extension identifies the spectral valuation on E with the valuation induced by
the embedding E into PadicAlgCl ell. Transporting along ULift identifies their
rings of integers as topological rings. Continuous postcomposition gives an
isomorphism of their condensed coefficient sheaves, including multiplication;
sheafification of the continuous presentation gives the same sheaf. Pullback
from the point transports it to each scheme. Restriction along this ring
isomorphism is an exact equivalence of module-object categories, preserving
and reflecting locally finitely presented modules on each stratum. Its derived
equivalence preserves bounded cohomology and constructibility, so restricts to
the displayed equivalences. At the abelian level the pushforward comparison
is sectionwise identity after coefficient restriction. Deriving it gives the
specified natural isomorphism for the actual ambient pushforward. No exceptional
adjoint, purity or biduality enters this comparison.
-/
theorem coherent_integral_native_presentation
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ell)] [Algebra ℚ_[ell] E]
    [IsScalarTower ℚ_[ell] E (PadicAlgCl ell)] [FiniteDimensional ℚ_[ell] E]
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : Z ⟶ Y) :
    ∃ (eZ : BoundedConstructible (condensedRingObj
          (Profinite.padicIntegersRingObj ell E) Z.left) ≌ Bc ell (ULift.{u + 1} E) Z.left)
      (eY : BoundedConstructible (condensedRingObj
          (Profinite.padicIntegersRingObj ell E) Y.left) ≌ Bc ell (ULift.{u + 1} E) Y.left),
      Nonempty (CondensedRing.PadicIntegersRingObj.boundedConstructibleLowerStar ell E p ⋙
          eY.functor ⋙ (boundedConstructible
            (internalRing Y.left (Padic.coefficientExtensionIntegers ell (ULift.{u + 1} E)))).ι ≅
        eZ.functor ⋙ (boundedConstructible
            (internalRing Z.left (Padic.coefficientExtensionIntegers ell (ULift.{u + 1} E)))).ι ⋙
          integralPush ell (ULift.{u + 1} E) p.left) := by
  let γ := nativePointIso.{u} ell E
  let φ := γ.hom.hom
  have : IsMonHom φ := inferInstanceAs (IsMonHom γ.hom.hom)
  have : IsIso φ := inferInstanceAs (IsIso ((Mon.forget _).map γ.hom))
  let eZ := coefficientBcEquivalence (AlgebraicGeometry.ProEtale.coefficientMap φ Z.left)
  let eY := coefficientBcEquivalence (AlgebraicGeometry.ProEtale.coefficientMap φ Y.left)
  have hflat (X : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (AlgebraicGeometry.ProEtale.coefficientMap φ X)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv
      (AlgebraicGeometry.ProEtale.coefficientMap φ X)).symm
  let := hflat
  refine ⟨eZ, eY, ⟨?_⟩⟩
  exact Functor.isoWhiskerLeft
    (boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ell E) Z.left)).ι
    (CondensedRing.derivedComapLowerStarIso φ p.left)

end AlgebraicGeometry.ProEtale.CoherentReduction
