/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.AffineModuleComplexRepresentative
import Sheaf.AlgebraicGeometry.AffineDerivedTensorChartComparison
import all Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal
import Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde
import Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction
import WeilConjectures.Algebra.Homology.TorAmplitudeFlatModel
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.AlgebraicGeometry.TildePreservesFiniteLimits

/-! # Quasi-coherent tests on an affine scheme

Source: Stacks Project, Tag 08EA, affine paragraph, using Tags 06Z0 and 08E9.
(blueprint: lem-pc-affine-qcoh-tor-amplitude-detection).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- On an affine scheme, quasi-coherent test sheaves detect Tor amplitude.
Source: Stacks Project, Tag 08EA, affine paragraph, and Tags 06Z0, 08E9.
(blueprint: lem-pc-affine-qcoh-tor-amplitude-detection).

Proof: Write X as Spec A using its canonical affine spectrum chart. The affine
quasi-coherent derived equivalence represents E by termwise tilde of a module complex M.
Test against tilde N, for every A-module N. The affine tensor comparison and exactness
of tilde identify the tested cohomology with tilde of H^i(M tensor-derived N).
Faithfulness of tilde detects its vanishing, hence M has Tor amplitude [a,b].
The module flat-model criterion gives a flat complex P supported in [a,b] representing M.
Its tilde complex, transported along the canonical chart, is K-flat and represents E.
Tensoring it with any sheaf G in degree zero has zero terms outside [a,b], hence zero
cohomology there. This is a K-flat witness for the conclusion. The argument includes
zero rings, empty affine schemes, unbounded E, and a=b; no arbitrary model is selected
from an unproved mere existence theorem, as only the resulting vanishing is asserted. -/
theorem affineQCoh_torAmplitude_detection (X : Scheme.{u}) [IsAffine X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (a b : ℤ) (hab : a ≤ b)
    (h : ∀ F : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      F.IsQuasicoherent → ∀ i : ℤ, i < a ∨ b < i →
        schemeDerivedTensorCohomologyVanishes X E F i) :
    ∀ G : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes X E G i := by
  classical
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, ⊤))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))
  let := SheafOfModules.monoidalCategory X.sheaf
  let T : ModuleCat.{u} Γ(X, ⊤) ⥤
      SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace) :=
    tilde.functor Γ(X, ⊤)
  let : T.IsLeftAdjoint := (tilde.adjunction (R := Γ(X, ⊤))).isLeftAdjoint
  let : T.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  let : T.Faithful := (tilde.fullyFaithfulFunctor (R := Γ(X, ⊤))).faithful
  let : PreservesFiniteLimits T := tilde_preserves_finite_limits Γ(X, ⊤)
  let R : SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
    Scheme.Modules.restrictFunctor X.toSpecΓ
  have : R.Additive := by
    change (Scheme.Modules.restrictFunctor X.toSpecΓ).Additive
    infer_instance
  have : PreservesFiniteLimits R := by
    dsimp [R, Scheme.Modules.restrictFunctor]
    infer_instance
  have : PreservesFiniteColimits R := by
    change PreservesFiniteColimits (Scheme.Modules.restrictFunctor X.toSpecΓ)
    infer_instance
  let S := Scheme.Modules.restrictFunctor X.isoSpec.inv
  have eRS : R ⋙ S ≅ 𝟭 _ :=
    (Scheme.Modules.restrictFunctorComp X.isoSpec.inv X.toSpecΓ).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (by
        rw [← Scheme.isoSpec_hom]
        exact X.isoSpec.inv_hom_id) ≪≫ Scheme.Modules.restrictFunctorId
  have : R.Faithful := eRS.faithful_of_comp
  let U := T.mapHomologicalComplex (.up ℤ)
  let V := R.mapHomologicalComplex (.up ℤ)
  obtain ⟨M, ⟨eM⟩⟩ := exists_affine_module_complex_representative X E hE
  change E ≅ DerivedCategory.Q.obj (V.obj (U.obj M)) at eM
  obtain ⟨P, s, hs, _, hk⟩ := CochainComplex.exists_quasiIso_flat_kFlat M
  have : QuasiIso s := hs
  have htor : DerivedCategory.torAmplitudeIn (ModuleCat.{u} Γ(X, ⊤)) a b
      (DerivedCategory.Q.obj M) := by
    intro N
    have hN (i : ℤ) (hi : i < a ∨ b < i) :
        IsZero ((DerivedCategory.homologyFunctor _ i).obj
          (DerivedCategory.Q.obj M ⊗ (DerivedCategory.singleFunctor _ 0).obj N)) := by
      let N₀ := (HomologicalComplex.single (ModuleCat.{u} Γ(X, ⊤)) (.up ℤ) 0).obj N
      let K := CochainComplex.mapBifunctor P N₀ (curriedTensor (ModuleCat.{u} Γ(X, ⊤)))
      let eK : DerivedCategory.Q.obj M ⊗ (DerivedCategory.singleFunctor _ 0).obj N ≅
          DerivedCategory.Q.obj K :=
        whiskerRightIso (asIso (DerivedCategory.Q.map s)).symm _ ≪≫
          whiskerLeftIso (DerivedCategory.Q.obj P)
            ((DerivedCategory.singleFunctorIsoCompQ _ 0).app N) ≪≫
          DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P N₀ hk
      have hq : (R.obj (T.obj N)).IsQuasicoherent := by
        have : (T.obj N).IsQuasicoherent := by
          change (tilde.{u} (R := Γ(X, ⊤)) N).IsQuasicoherent
          infer_instance
        exact Scheme.Modules.isQuasicoherent_restrictFunctor X.toSpecΓ (T.obj N)
      have hz := (tensor_vanishes_iff X E (R.obj (T.obj N)) i).1 (h _ hq i hi)
      let eN : DerivedCategory.Q.obj (V.obj (U.obj N₀)) ≅
          (DerivedCategory.singleFunctor _ 0).obj (R.obj (T.obj N)) :=
        DerivedCategory.Q.mapIso
          (V.mapIso ((HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) 0).app N) ≪≫
            (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app (T.obj N)) ≪≫
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm
      obtain ⟨cmp⟩ := affine_derivedTensor_chart_comparison X M N₀ P s hs hk
      have hzK := hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
        ((tensorIso eM eN.symm) ≪≫ cmp).symm)
      let eH : (DerivedCategory.homologyFunctor _ i).obj
          (DerivedCategory.Q.obj (V.obj (U.obj K))) ≅ R.obj (T.obj (K.homology i)) :=
        (DerivedCategory.homologyFunctorFactors _ i).app _ ≪≫
          (R.mapHomologicalComplexHomologyIso (.up ℤ) i).app (U.obj K) ≪≫
          R.mapIso ((T.mapHomologicalComplexHomologyIso (.up ℤ) i).app K)
      have hzRT := hzK.of_iso eH.symm
      have hzModule : IsZero (K.homology i) := by
        apply (IsZero.iff_id_eq_zero _).2
        apply T.map_injective
        apply R.map_injective
        rw [T.map_id, T.map_zero, R.map_id, R.map_zero]
        exact hzRT.eq_of_src _ _
      exact hzModule.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eK ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app K)
    exact ⟨(DerivedCategory.isGE_iff _ a).2 (fun i hi ↦ hN i (Or.inl hi)),
      (DerivedCategory.isLE_iff _ b).2 (fun i hi ↦ hN i (Or.inr hi))⟩
  obtain ⟨B, hflat, hzero, ⟨eB⟩⟩ :=
    (DerivedCategory.module_torAmplitudeIn_iff_exists_flat_model M a b hab).mp htor
  let eBE : DerivedCategory.Q.obj (V.obj (U.obj B)) ≅ E :=
    (R.mapDerivedCategoryFactors.app _).symm ≪≫
      R.mapDerivedCategory.mapIso
        ((T.mapDerivedCategoryFactors.app B).symm ≪≫
          T.mapDerivedCategory.mapIso eB.symm ≪≫ T.mapDerivedCategoryFactors.app M) ≪≫
      R.mapDerivedCategoryFactors.app _ ≪≫ eM.symm
  have hB := isKFlat_tilde Γ(X, ⊤) B
    (CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat B
      ⟨b, fun i hi ↦ hzero i (Or.inr hi)⟩ hflat)
  have hVB := isKFlat_restrict X.toSpecΓ (U.obj B) hB
  intro G i hi
  refine ⟨V.obj (U.obj B), hVB, ⟨eBE⟩, ?_⟩
  let β := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) G (V.obj (U.obj B))
  apply IsZero.of_iso _ ((HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso β)
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  change IsZero ((tensorRight G).obj (R.obj (T.obj (B.X i))))
  let : (tensorRight G).PreservesZeroMorphisms := ⟨fun M N ↦
    congrArg (fun t ↦ t.app G) ((curriedTensor _).map_zero M N)⟩
  exact (tensorRight G).map_isZero (R.map_isZero (T.map_isZero (hzero i hi)))

end AlgebraicGeometry
