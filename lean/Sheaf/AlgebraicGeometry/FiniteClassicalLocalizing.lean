/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.SixFunctors.IntegralModelsGenerators
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import Sheaf.Paper.InternalModuleAbEquivalence
import Sheaf.Paper.FiniteDiscreteConstructibleEncoding
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import all Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Sheaf.Paper.ProEtaleConstantModulePullbackEncoding
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.ClassicalModuleWeakSerre
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses

/-! # Classical cohomology is localizing and stable under inverse image

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.proof.md, Transfer
(blueprint: lem-sfb-finite-classical-localizing).

The first clauses use intrinsic modules over the ordinary constant ring sheaf.
The final clause uses the recorded internal-module presentation of `Dctf`.
For finite discrete coefficients the canonical ring identifications
`finiteDiscreteCondensedRing_constant` and `finiteDiscreteSchemeRing_constant`
identify this presentation with the same ordinary constant-coefficient category.
The final clause uses the existing canonical `integralModelIntrinsicRealization`
on each cohomology sheaf, making the coefficient identification explicit.
No completed derived category occurs. Finite rings are represented in `Type 0`,
without restricting their isomorphism classes; the ordinary ring is lifted to `Type u`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

private theorem trunc_coproducts
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C] {I : Type*}
    [HasColimitsOfShape (Discrete I) C] [HasExactColimitsOfShape (Discrete I) C]
    (a : ℤ) :
    PreservesColimitsOfShape (Discrete I) ((DerivedCategory.TStructure.t (C := C)).truncLE a) ∧
    PreservesColimitsOfShape (Discrete I) ((DerivedCategory.TStructure.t (C := C)).truncGE a) := by
  let t := DerivedCategory.TStructure.t (C := C)
  have conservative : JointlyReflectIsomorphisms (DerivedCategory.homologyFunctor C) :=
    ⟨fun f ↦ (DerivedCategory.isIso_iff (C := C) f).mpr (fun q ↦ inferInstance)⟩
  have le (q : ℤ) : PreservesColimitsOfShape (Discrete I)
      (t.truncLE a ⋙ DerivedCategory.homologyFunctor C q) := by
    by_cases hq : q ≤ a
    · let α := Functor.whiskerRight (t.truncLEι a) (DerivedCategory.homologyFunctor C q)
      have hi (K : DerivedCategory C) : IsIso (α.app K) := by
        exact DerivedCategory.isIso_homologyFunctor_map_truncLTι_app K (a + 1) q (by omega)
      have : IsIso α := NatIso.isIso_of_isIso_app α
      exact preservesColimitsOfShape_of_natIso (asIso α).symm
    · constructor
      intro F
      constructor
      intro c hc
      exact ⟨IsColimit.ofIsZero _
        (Functor.isZero _ (fun j ↦ DerivedCategory.isZero_of_isLE _ a q (by omega)))
        (DerivedCategory.isZero_of_isLE _ a q (by omega))⟩
  have ge (q : ℤ) : PreservesColimitsOfShape (Discrete I)
      (t.truncGE a ⋙ DerivedCategory.homologyFunctor C q) := by
    by_cases hq : a ≤ q
    · let α := Functor.whiskerRight (t.truncGEπ a) (DerivedCategory.homologyFunctor C q)
      have hi (K : DerivedCategory C) : IsIso (α.app K) :=
        DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K a q hq
      have : IsIso α := NatIso.isIso_of_isIso_app α
      exact preservesColimitsOfShape_of_natIso (asIso α)
    · constructor
      intro F
      constructor
      intro c hc
      exact ⟨IsColimit.ofIsZero _
        (Functor.isZero _ (fun j ↦ DerivedCategory.isZero_of_isGE _ a q (by omega)))
        (DerivedCategory.isZero_of_isGE _ a q (by omega))⟩
  constructor
  · constructor
    intro F
    constructor
    intro c hc
    exact ⟨conservative.jointlyReflectsColimit
      (fun q ↦ isColimitOfPreserves
        (t.truncLE a ⋙ DerivedCategory.homologyFunctor C q) hc)⟩
  · constructor
    intro F
    constructor
    intro c hc
    exact ⟨conservative.jointlyReflectsColimit
      (fun q ↦ isColimitOfPreserves
        (t.truncGE a ⋙ DerivedCategory.homologyFunctor C q) hc)⟩

private theorem classical_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}}
    {F G : SheafOfModules.{u + 1} R} (e : F ≅ G)
    (h : IsClassicalModuleSheaf F) : IsClassicalModuleSheaf G := by
  exact (isClassical_iso_iff
    ((SheafOfModules.toSheaf R ⋙
      sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})).mapIso e)).mp h

private theorem classical_encoding (X : Scheme.{u}) (B : Type u) [CommRing B]
    (F : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X B)) :
    IsClassicalModuleSheaf F ↔
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).essImage
        ((Scheme.proEtaleModuleEncoding X B).functor.obj F) := by
  obtain ⟨_, _, _, _, _, h⟩ := proEtaleClassicalSheavesModules X (ULift.{u + 1} B)
  apply Iff.trans ?_ (h ((Scheme.proEtaleModuleEncoding X B).functor.obj F))
  apply isClassical_iso_iff
  exact ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))

private theorem classical_coproduct (X : Scheme.{u}) (B : Type u) [CommRing B]
    {I : Type (u + 1)}
    (F : Discrete I ⥤ Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X B))
    (hF : ∀ i, IsClassicalModuleSheaf (F.obj i)) (c : Cocone F) (hc : IsColimit c) :
    IsClassicalModuleSheaf c.pt := by
  let E := Scheme.proEtaleModuleEncoding X B
  let L := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X
  apply (classical_encoding X B c.pt).mpr
  exact L.essImage.prop_of_isColimit (isColimitOfPreserves E.functor hc)
    (fun i ↦ (classical_encoding X B (F.obj i)).mp (hF i))

private theorem constant_model_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsFiniteConstantStratified Λ X M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  let α := condensedPullbackHom Λ (S.immersion a)
  apply localFinitePresentation_of_comap (inv α)
  have h := HasFiniteConstantLocalModel.isLocallyFinitelyPresented Λ _ (hS a)
  let e := (Mod.extendScalarsIsoComapInv α).app
    (((upperStar Ab.{u + 1} (S.immersion a)).mapMod (condensedRingObj Λ X)).obj M)
  exact localFinitePresentation_of_iso e h

private theorem fixed_scalars_exact (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    PreservesFiniteLimits (WeilConjectures.SixFunctors.integralModelFixedScalars X A) ∧
    PreservesColimitsOfSize.{u + 1, u + 1}
      (WeilConjectures.SixFunctors.integralModelFixedScalars X A) := by
  let F := WeilConjectures.SixFunctors.integralModelFixedScalars X A
  let U := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ULift.{u} A))) Ab.{u + 1})
  let e : F ⋙ U ≅ SheafOfModules.toSheaf (continuousMapRingSheaf X A) :=
    NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _
      (NatIso.ofComponents (fun _ ↦ Iso.refl _)))
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (SheafOfModules.toSheaf.{u + 1} (continuousMapRingSheaf X A)) :=
    ⟨fun {J} _ ↦ inferInstance⟩
  have : PreservesFiniteLimits U := by
    have : PreservesFiniteLimits (U ⋙ sheafToPresheaf _ _) :=
      inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ULift.{u} A))) Ab.{u + 1})))
    exact preservesFiniteLimits_of_reflects_of_preserves U (sheafToPresheaf _ _)
  have : PreservesColimitsOfSize.{u + 1, u + 1} U := by
    let V := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ULift.{u} A))) Ab.{u + 1}
    have : V.IsLeftAdjoint := by
      have := (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1}
        (Int.castRingHom (ULift.{u + 1} (ULift.{u} A)))).isLeftAdjoint
      exact inferInstanceAs (ModuleCat.restrictScalars.{u + 1}
        (Int.castRingHom (ULift.{u + 1} (ULift.{u} A))) ⋙
          forget₂ (ModuleCat.{u + 1} ℤ) Ab.{u + 1}).IsLeftAdjoint
    let adj := Adjunction.ofIsLeftAdjoint V
    have : PreservesLimitsOfSize.{u, u + 1} V.rightAdjoint := adj.rightAdjoint_preservesLimits
    have : (Scheme.ProEt.topology X).HasSheafCompose V.rightAdjoint :=
      hasSheafCompose_of_preservesLimitsOfSize _
    exact (sheafComposeAdjunction (Scheme.ProEt.topology X) adj).leftAdjoint_preservesColimits
  have : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1} (ULift.{u} A)))) :=
    ⟨fun J _ ↦ inferInstance⟩
  have : U.ReflectsIsomorphisms := inferInstance
  have : ReflectsFiniteLimits U := reflectsFiniteLimits_of_reflectsIsomorphisms U
  have : ReflectsColimitsOfSize.{u + 1, u + 1} U :=
    reflectsColimits_of_reflectsIsomorphisms
  have : PreservesFiniteLimits (F ⋙ U) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesColimitsOfSize.{u + 1, u + 1} (F ⋙ U) :=
    preservesColimits_of_natIso e.symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F U,
    preservesColimits_of_reflects_of_preserves F U⟩

private noncomputable def realization_underlying (X : Scheme.{u}) (A : Type)
    [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)) :
    (SheafOfModules.toSheaf.{u + 1} _).obj
      ((WeilConjectures.SixFunctors.integralModelIntrinsicRealization X A).obj M) ≅ M.X := by
  let F := ((CondensedRing.continuousRingModuleEquivalence X A).functor ⋙
    WeilConjectures.SixFunctors.integralModelFixedScalars X A).obj M
  let P := (finiteCoefficientModulePresheaf X.ProEt
    (ULift.{u + 1} (ULift.{u} A))).obj F.obj
  let a := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (finiteCoefficientIntrinsicScalarMap X (ULift.{u} A))).unit.app P
  have : IsIso a := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    change IsIso (toSheafify (Scheme.ProEt.topology X) P.presheaf)
    exact isIso_toSheafify (Scheme.ProEt.topology X)
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ULift.{u} A))) Ab.{u + 1})).obj F).property
  let i : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ULift.{u} A))) Ab.{u + 1})).obj F ≅
      (SheafOfModules.toSheaf.{u + 1} _).obj
        ((WeilConjectures.SixFunctors.integralModelIntrinsicRealization X A).obj M) :=
    (fullyFaithfulSheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).preimageIso
      ((PresheafOfModules.toPresheaf _).mapIso (asIso a))
  refine i.symm ≪≫ ?_
  exact ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))

private theorem generator_classical (T : Scheme.{u}) (A : Type)
    [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) T))
    (hm : IsFiniteConstantStratified (Profinite.continuousMapRingObj A) T M) :
    IsClassicalModuleSheaf
      ((WeilConjectures.SixFunctors.integralModelIntrinsicRealization T A).obj M) := by
  classical
  have hc := constant_model_constructible
    (Profinite.continuousMapRingObj A) T M hm
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} A
  let := heR
  obtain ⟨G, hG, hg⟩ := CategoryTheory.internalModuleAb_equivalence (ULift.{u + 1} A)
  let := hG
  let H := CondensedRing.finiteDiscreteCoefficientEquivalence A eR G hg T
  let V := sheafCompose (Scheme.ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1})
  have hcH := CondensedRing.finiteDiscreteCoefficient_constructible A eR G hg T M hc
  obtain ⟨N, hN, ⟨i⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
    (ULift.{u + 1} A) hcH
  obtain ⟨_, _, _, _, _, hclass⟩ := proEtaleClassicalSheavesModules T (ULift.{u + 1} A)
  have hh : IsClassical ((sheafCompose (Scheme.ProEt.topology T)
      (forget (ModuleCat.{u + 1} (ULift.{u + 1} A)))).obj (H.inverse.obj M)) :=
    (hclass (H.inverse.obj M)).mpr ⟨N, ⟨i⟩⟩
  let j : V.obj (H.inverse.obj M) ≅ M.X :=
    ((CondensedRing.finiteDiscreteCoefficientEquivalenceForgetIso A eR G hg T).app
      (H.inverse.obj M)).symm ≪≫ (Mod.forget _).mapIso (H.counitIso.app M)
  apply (isClassical_iso_iff
    ((sheafCompose (Scheme.ProEt.topology T) (forget Ab.{u + 1})).mapIso
      (realization_underlying T A M))).mpr
  exact (isClassical_iso_iff
    ((sheafCompose (Scheme.ProEt.topology T) (forget Ab.{u + 1})).mapIso j)).mp hh

/-- The full replete subcategory with classical cohomology is triangulated, closed under
small ambient coproducts and canonical truncations, and stable under every scheme inverse
image. Cohomology and both truncations preserve ambient coproducts; inverse image commutes
with truncation, with its canonical inclusion and projection. On qcqs schemes the localizing
closure of the recorded bounded constructible finite-Tor category has classical cohomology.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.proof.md, Transfer
(blueprint: lem-sfb-finite-classical-localizing).

Proof plan, following the six steps of the node:
1. Classical module sheaves contain zero and are closed under kernels, cokernels and
   extensions (det-pe-classical-derived-weak-serre). Apply
   lem-sbc-cohomology-in-weak-serre-subcategory to obtain triangulated closure.
   The good truncation formulas (def-kun-truncations) retain cohomology or replace it by zero.
2. Classical sheaves are exactly the essential image of comparison inverse image
   (det-pe-classical-sheaves-modules). Its adjunction
   (def-weil-pbc-site-comparison-morphism) identifies the inverse image of an etale sum
   with the ambient sum, including the empty sum; module sums exist by
   lem-weil-pbc-module-sheaves-colimits-forgetful.
3. The module category is Grothendieck (lem-weil-pbc-ring-sheaves-grothendieck).
   Sums are filtered colimits of finite sums, hence exact. Termwise sums compute ambient
   derived sums (lem-kun-grothendieck-derived-coproducts). Exactness commutes with kernels,
   images and cokernels, hence with cohomology and the good truncations. Step 2 gives closure.
4. Constant-coefficient inverse image is exact (def-weil-pbc-proetale-operations).
   Its cohomology is the inverse image of cohomology. The unrestricted inverse-image square
   of sk-thm-pe-direct-image-comparison preserves classical sheaves. Exactness also preserves
   good truncations and their canonical maps. No qcqs assumption is imposed on the map.
5. The finite-discrete ring identifications
   (lem-weil-pbc-finite-discrete-condensed-ring-constant and
   lem-weil-pbc-finite-discrete-scheme-ring-constant) identify internal and ordinary constant
   modules, preserving cohomology and sums. A finite ring is Noetherian. On qcqs schemes the
   heart clause of sk-thm-pe-constructible-comparison makes every constructible cohomology
   sheaf classical. Thus Dctf lies in the classical class; its Tor bound is not needed here.
6. By steps 1 and 3 this class is one of the full replete triangulated, coproduct-closed
   classes intersected in sk-def-localizing-closure. Step 5 therefore gives the inclusion.
   The zero ring, empty scheme, empty coproduct and unbounded complexes are included. -/
theorem finite_classical_localizing (ell : ℕ) [Fact ell.Prime]
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalRing A] (_hA : ∃ n : ℕ, 1 ≤ n ∧ (ell ^ n : A) = 0)
    (T : Scheme.{u}) :
    HasCoproducts.{u + 1} (Scheme.proEtaleDerivedCategory T (ULift.{u, 0} A)) ∧
    IsLocalizingSubcategoryOfSize.{u + 1}
      (fun K : Scheme.proEtaleDerivedCategory T (ULift.{u, 0} A) ↦
        IsClassicalModuleComplex K) ∧
    (∀ (K : Scheme.proEtaleDerivedCategory T (ULift.{u, 0} A)),
      IsClassicalModuleComplex K → ∀ a : ℤ,
        IsClassicalModuleComplex ((DerivedCategory.TStructure.t.truncLE a).obj K) ∧
        IsClassicalModuleComplex ((DerivedCategory.TStructure.t.truncGE a).obj K)) ∧
    (∀ (I : Type (u + 1))
      (K : I → Scheme.proEtaleDerivedCategory T (ULift.{u, 0} A)),
      (∀ i : I, IsClassicalModuleComplex (K i)) →
      ∀ (c : Cofan K), IsColimit c → ∀ q : ℤ,
        Nonempty (IsColimit ((DerivedCategory.homologyFunctor
          (Scheme.proEtaleRingModules T
            (Scheme.proEtaleConstantRing T (ULift.{u, 0} A))) q).mapCocone c)) ∧
        Nonempty (IsColimit ((DerivedCategory.TStructure.t.truncLE q).mapCocone c)) ∧
        Nonempty (IsColimit ((DerivedCategory.TStructure.t.truncGE q).mapCocone c))) ∧
    (∀ (W : Scheme.{u}) (r : W ⟶ T),
      (∀ K : Scheme.proEtaleDerivedCategory T (ULift.{u, 0} A),
        IsClassicalModuleComplex K →
          IsClassicalModuleComplex
            ((Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r).obj K)) ∧
      ∀ a : ℤ,
        ∃ eLE : DerivedCategory.TStructure.t.truncLE a ⋙
            Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r ≅
          Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r ⋙
            DerivedCategory.TStructure.t.truncLE a,
        ∃ eGE : DerivedCategory.TStructure.t.truncGE a ⋙
            Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r ≅
          Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r ⋙
            DerivedCategory.TStructure.t.truncGE a,
        eLE.hom ≫ Functor.whiskerLeft
            (Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r)
            (DerivedCategory.TStructure.t.truncLEι a) =
          Functor.whiskerRight (DerivedCategory.TStructure.t.truncLEι a)
            (Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r) ∧
        Functor.whiskerRight (DerivedCategory.TStructure.t.truncGEπ a)
            (Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r) ≫ eGE.hom =
          Functor.whiskerLeft
            (Scheme.proEtaleConstantRingDerivedPullback (ULift.{u, 0} A) r)
            (DerivedCategory.TStructure.t.truncGEπ a)) ∧
    (∀ [CompactSpace T] [QuasiSeparatedSpace T]
      (K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj A) T))),
      localizingClosureOfSize.{u + 1}
        (constantModelBoundedConstructible (Profinite.continuousMapRingObj A) T ⊓
          fun L ↦ DerivedCategory.finiteTorAmplitude _ L) K →
      ∀ q : ℤ, IsClassicalModuleSheaf
        ((WeilConjectures.SixFunctors.integralModelIntrinsicRealization T A).obj
          ((DerivedCategory.homologyFunctor _ q).obj K))) := by
  classical
  let B : Type u := ULift.{u, 0} A
  let C := Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B)
  let P : ObjectProperty C := fun F ↦ IsClassicalModuleSheaf F
  have hP : P = IsClassicalModule (X := T) B := by
    funext F
    exact propext (isClassicalModule_iff B F).symm
  obtain ⟨hzero, hk, hck, hext⟩ := classicalModule_weakSerre T B
  have : P.ContainsZero := by
    constructor
    refine ⟨(0 : C), isZero_zero C, ?_⟩
    exact (isClassicalModule_iff B (0 : C)).mp hzero
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ classical_iso e h⟩
  have : P.IsClosedUnderKernels := hP.symm ▸ hk
  have : P.IsClosedUnderCokernels := hP.symm ▸ hck
  have : P.IsClosedUnderExtensions := hP.symm ▸ hext
  have htri := (cohomology_in_weak_serre_subcategory P).1
  have hcop : HasCoproducts.{u + 1} (DerivedCategory C) := inferInstance
  have htrunc (K : DerivedCategory C) (hK : IsClassicalModuleComplex K) (a : ℤ) :
      IsClassicalModuleComplex ((DerivedCategory.TStructure.t.truncLE a).obj K) ∧
      IsClassicalModuleComplex ((DerivedCategory.TStructure.t.truncGE a).obj K) :=
    ⟨DerivedCategory.homologyProperty_truncLE (P := P) hK a,
      DerivedCategory.homologyProperty_truncGE (P := P) hK a⟩
  have : IsGrothendieckAbelian.{u + 1} C :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0} _ _
  have : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  have : AB4OfSize.{u + 1} C := AB4.of_AB5 C
  have hlocal : IsLocalizingSubcategoryOfSize.{u + 1}
      (fun K : DerivedCategory C ↦ IsClassicalModuleComplex K) := by
    refine ⟨htri, inferInstanceAs
      (DerivedCategory.homologyProperty P).IsClosedUnderIsomorphisms, ?_⟩
    intro I F hF hclass
    let := hF
    change IsClassicalModuleComplex (colimit F)
    intro q
    let G := DerivedCategory.homologyFunctor C q
    have hc (i : Discrete I) : IsClassicalModuleSheaf (G.obj (F.obj i)) := hclass i.as q
    have hsum : IsClassicalModuleSheaf (G.obj (colimit F)) :=
      classical_coproduct T B (F ⋙ G) hc
        (G.mapCocone (colimit.cocone F)) (isColimitOfPreserves G (colimit.isColimit F))
    exact @hsum
  refine ⟨hcop, hlocal, htrunc, ?_, ?_, ?_⟩
  · intro I K hK c hc q
    have hτ := trunc_coproducts (C := C) (I := I) q
    let := hτ.1
    let := hτ.2
    exact ⟨⟨isColimitOfPreserves _ hc⟩, ⟨isColimitOfPreserves _ hc⟩,
      ⟨isColimitOfPreserves _ hc⟩⟩
  · intro W r
    constructor
    · intro K hK q
      let F := Scheme.proEtaleConstantRingPullback B r
      apply classical_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app K)
      let M := (DerivedCategory.homologyFunctor C q).obj K
      apply (classical_encoding W B (F.obj M)).mpr
      obtain ⟨G, ⟨e⟩⟩ := (classical_encoding T B M).mp (hK q)
      obtain ⟨i⟩ := Scheme.proEtaleModuleRestriction_pullback_of_isIso r B M
      refine ⟨(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) r).obj G, ⟨?_⟩⟩
      exact ((comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) r).app G).symm ≪≫
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) r).mapIso e ≪≫ i.symm
    · intro a
      let F := Scheme.proEtaleConstantRingPullback B r
      refine ⟨F.mapDerivedCategoryTruncLEIso a, F.mapDerivedCategoryTruncGEIso a, ?_, ?_⟩
      · ext K
        have hbound : DerivedCategory.TStructure.t.IsLE
            (F.mapDerivedCategory.obj ((DerivedCategory.TStructure.t.truncLE a).obj K)) a :=
          F.isLE_mapDerivedCategory_obj _ a
        simpa only [Functor.mapDerivedCategoryTruncLEIso, NatIso.ofComponents_hom_app,
          asIso_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
          Functor.comp_obj, Functor.id_obj, F, B,
          Scheme.proEtaleConstantRingDerivedPullback] using
            (DerivedCategory.TStructure.t.liftTruncLE_ι
              (F.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncLEι a).app K)) a)
      · ext K
        have hbound : DerivedCategory.TStructure.t.IsGE
            (F.mapDerivedCategory.obj ((DerivedCategory.TStructure.t.truncGE a).obj K)) a :=
          F.isGE_mapDerivedCategory_obj _ a
        apply (cancel_mono ((F.mapDerivedCategoryTruncGEIso a).inv.app K)).mp
        simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
        rw [Category.assoc, Iso.hom_inv_id_app]
        simpa only [Functor.mapDerivedCategoryTruncGEIso, Iso.symm_inv,
          NatIso.ofComponents_hom_app, asIso_hom, Category.comp_id, Functor.comp_obj,
          Functor.whiskerLeft_app, Functor.id_obj, F, B,
          Scheme.proEtaleConstantRingDerivedPullback] using
            (DerivedCategory.TStructure.t.π_descTruncGE
              (F.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncGEπ a).app K)) a).symm
  · intro hcompact hqs K hK
    let D := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) T)
    let R₀ := continuousMapRingSheaf T A
    have : IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1} R₀) :=
      SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0} _ _
    have : IsGrothendieckAbelian.{u + 1} D :=
      IsGrothendieckAbelian.of_equivalence
        (CondensedRing.continuousRingModuleEquivalence T A).symm
    have : Abelian.HasKInjectiveResolutions D := inferInstance
    have : HasColimitsOfSize.{u + 1, u + 1} D := inferInstance
    let R := WeilConjectures.SixFunctors.integralModelIntrinsicRealization T A
    have : PreservesFiniteLimits R := by
      have := (fixed_scalars_exact T A).1
      dsimp [R, WeilConjectures.SixFunctors.integralModelIntrinsicRealization]
      infer_instance
    have : PreservesFiniteColimits R := by
      have := (fixed_scalars_exact T A).2
      dsimp [R, WeilConjectures.SixFunctors.integralModelIntrinsicRealization]
      infer_instance
    have : PreservesColimitsOfSize.{u + 1, u + 1} R := by
      have := (fixed_scalars_exact T A).2
      have := (finiteCoefficientIntrinsicRealization_exact T B).1
      dsimp [R, WeilConjectures.SixFunctors.integralModelIntrinsicRealization]
      infer_instance
    let Q : ObjectProperty (DerivedCategory C) := fun L ↦ IsClassicalModuleComplex L
    let E := R.mapDerivedCategory
    let S := Q.inverseImage E
    have hs : IsLocalizingSubcategoryOfSize.{u + 1} S := by
      let := hlocal.1
      let := hlocal.2.1
      refine ⟨inferInstance, inferInstance, ?_⟩
      intro I F hF hclass
      let := hF
      have : PreservesColimitsOfShape (Discrete I) E :=
        Functor.preservesColimitsOfShape_mapDerivedCategory R I
      let : HasColimit (F ⋙ E) := ⟨_, isColimitOfPreserves E (colimit.isColimit F)⟩
      exact Q.prop_of_iso (preservesColimitIso E F).symm
        (hlocal.2.2 (F ⋙ E) inferInstance hclass)
    have hgen (L : DerivedCategory D)
        (hL : (constantModelBoundedConstructible (Profinite.continuousMapRingObj A) T ⊓
          fun N ↦ DerivedCategory.finiteTorAmplitude _ N) L) : S L := by
      intro q
      apply classical_iso ((R.mapDerivedCategoryHomologyFunctorIso q).app L)
      apply generator_classical T A
      have h := hL.1.2 q
      simpa only [IsConstantModelConstructible,
        if_pos (show CompactSpace T ∧ QuasiSeparatedSpace T from ⟨hcompact, hqs⟩)] using h
    have hh : S K := hK S hs hgen
    intro q
    exact classical_iso ((R.mapDerivedCategoryHomologyFunctorIso q).app K).symm (hh q)

end AlgebraicGeometry.ProEtale
