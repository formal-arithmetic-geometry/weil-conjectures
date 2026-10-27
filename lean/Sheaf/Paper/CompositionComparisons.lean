/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

import Sheaf.Paper.FiniteSupportCompositorExistence
import Sheaf.Paper.FiniteSupportCompositorCoefficient
public import Sheaf.Paper.TowerAdjointCompositorRealization
import all Sheaf.Paper.TowerAdjointCompositorRealization
public import Sheaf.Paper.IntegralAdjunctionBijection
public import Sheaf.Paper.IntegralDirectImageTower
public import Sheaf.Paper.SmoothPurityNormalizedEquivalence
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.SecSmoothPurity.ReductionDirectImage
public import Sheaf.SecSmoothPurity.ReductionExceptional
public import Sheaf.Paper.FiniteLocalizingExceptionalPreservation
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Sheaf.Paper.SmoothPurityTowerGluing
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-! # Composition of adjunctions and coefficient comparisons

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/
sk-prop-sp-composition-comparisons.md, (1)--(3)
(blueprint: det-sp-composition-comparisons).

Finite coefficients use the ordinary constant-ring intrinsic Dctf categories. Towers
use ordinary derived categories of strict varying-coefficient systems. Integral
coefficients use the completed sheaf and the published derived-complete category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false

universe u uIX uIY uIZ uTX uTY uTZ vIX vIY vIZ vTX vTY vTZ
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale

attribute [local implicit_reducible] reductionCtfCompactSupport reductionCtfScalar
  CategoryTheory.catToReflQuiver CategoryTheory.Functor.category

/-- The finite assertions (1)--(2), including existence of the proper/open normalized
left compositors, the canonical coefficient maps, both counit normalizations,
uniqueness of the right compositors, and the two coefficient equations.
The b fields are pinned to reductionDirectImageComparison; the c fields are pinned
by exactly the defining counit transpose of det-sp-reduction-exceptional.
Source: blueprint comparisons (1)--(2) (blueprint: det-sp-composition-comparisons). -/
structure SpCompositionFinite {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) where
  DA : FiniteAdjointCompositorDatum A cf cg ch
  DB : FiniteAdjointCompositorDatum B cf cg ch
  hSX : ∀ M : spFiniteConstructibleTorCategory X A,
    spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj)
  hSY : ∀ M : spFiniteConstructibleTorCategory Y A,
    spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj M.obj)
  hSZ : ∀ M : spFiniteConstructibleTorCategory Z A,
    spFiniteConstructibleTor Z B ((scalarExtensionFunctor φ Z).obj M.obj)
  bf : finiteAdjointSupport A cf DA.hFf ⋙ reductionCtfScalar φ Y hSY ≅
    reductionCtfScalar φ X hSX ⋙ finiteAdjointSupport B cf DB.hFf
  bg : finiteAdjointSupport A cg DA.hFg ⋙ reductionCtfScalar φ Z hSZ ≅
    reductionCtfScalar φ Y hSY ⋙ finiteAdjointSupport B cg DB.hFg
  bh : finiteAdjointSupport A ch DA.hFh ⋙ reductionCtfScalar φ Z hSZ ≅
    reductionCtfScalar φ X hSX ⋙ finiteAdjointSupport B ch DB.hFh
  hbf : ∀ M, (bf.hom.app M).hom =
    (reductionDirectImageComparison φ cf.i cf.g).app M.obj
  hbg : ∀ M, (bg.hom.app M).hom =
    (reductionDirectImageComparison φ cg.i cg.g).app M.obj
  hbh : ∀ M, (bh.hom.app M).hom =
    (reductionDirectImageComparison φ ch.i ch.g).app M.obj
  cfCoeff : DA.Hf ⋙ reductionCtfScalar φ X hSX ≅ reductionCtfScalar φ Y hSY ⋙ DB.Hf
  cgCoeff : DA.Hg ⋙ reductionCtfScalar φ Y hSY ≅ reductionCtfScalar φ Z hSZ ⋙ DB.Hg
  chCoeff : DA.Hh ⋙ reductionCtfScalar φ X hSX ≅ reductionCtfScalar φ Z hSZ ⋙ DB.Hh
  hfCounit : ∀ K,
    (finiteAdjointSupport B cf DB.hFf).map (cfCoeff.hom.app K) ≫
        DB.adjf.counit.app ((reductionCtfScalar φ Y hSY).obj K) =
      bf.inv.app (DA.Hf.obj K) ≫ (reductionCtfScalar φ Y hSY).map (DA.adjf.counit.app K)
  hgCounit : ∀ K,
    (finiteAdjointSupport B cg DB.hFg).map (cgCoeff.hom.app K) ≫
        DB.adjg.counit.app ((reductionCtfScalar φ Z hSZ).obj K) =
      bg.inv.app (DA.Hg.obj K) ≫ (reductionCtfScalar φ Z hSZ).map (DA.adjg.counit.app K)
  hhCounit : ∀ K,
    (finiteAdjointSupport B ch DB.hFh).map (chCoeff.hom.app K) ≫
        DB.adjh.counit.app ((reductionCtfScalar φ Z hSZ).obj K) =
      bh.inv.app (DA.Hh.obj K) ≫ (reductionCtfScalar φ Z hSZ).map (DA.adjh.counit.app K)
  left_composition : ∀ M,
    (reductionCtfScalar φ Z hSZ).map (DA.alpha.hom.app M) ≫ bh.hom.app M =
      bg.hom.app ((finiteAdjointSupport A cf DA.hFf).obj M) ≫
        (finiteAdjointSupport B cg DB.hFg).map (bf.hom.app M) ≫
        DB.alpha.hom.app ((reductionCtfScalar φ X hSX).obj M)
  right_composition :
    ∃ thetaA : DA.Hh ≅ DA.Hg ⋙ DA.Hf,
      ∃ thetaB : DB.Hh ≅ DB.Hg ⋙ DB.Hf,
        (∀ K, (finiteAdjointSupport A cf DA.hFf ⋙ finiteAdjointSupport A cg DA.hFg).map
            (thetaA.hom.app K) ≫ (DA.adjf.comp DA.adjg).counit.app K =
          DA.alpha.hom.app (DA.Hh.obj K) ≫ DA.adjh.counit.app K) ∧
        (∀ K, (finiteAdjointSupport B cf DB.hFf ⋙ finiteAdjointSupport B cg DB.hFg).map
            (thetaB.hom.app K) ≫ (DB.adjf.comp DB.adjg).counit.app K =
          DB.alpha.hom.app (DB.Hh.obj K) ≫ DB.adjh.counit.app K) ∧
        (∀ t : DA.Hh ≅ DA.Hg ⋙ DA.Hf,
          (∀ K, (finiteAdjointSupport A cf DA.hFf ⋙ finiteAdjointSupport A cg DA.hFg).map
              (t.hom.app K) ≫ (DA.adjf.comp DA.adjg).counit.app K =
            DA.alpha.hom.app (DA.Hh.obj K) ≫ DA.adjh.counit.app K) → t = thetaA) ∧
        (∀ t : DB.Hh ≅ DB.Hg ⋙ DB.Hf,
          (∀ K, (finiteAdjointSupport B cf DB.hFf ⋙ finiteAdjointSupport B cg DB.hFg).map
              (t.hom.app K) ≫ (DB.adjf.comp DB.adjg).counit.app K =
            DB.alpha.hom.app (DB.Hh.obj K) ≫ DB.adjh.counit.app K) → t = thetaB) ∧
        (∀ K : spFiniteConstructibleTorCategory Z A,
          (finiteAdjointSupport A cg DA.hFg).map
              (DA.adjf.counit.app (DA.Hg.obj K)) ≫ DA.adjg.counit.app K =
            (DA.adjf.comp DA.adjg).counit.app K) ∧
        (∀ K : spFiniteConstructibleTorCategory Z B,
          (finiteAdjointSupport B cg DB.hFg).map
              (DB.adjf.counit.app (DB.Hg.obj K)) ≫ DB.adjg.counit.app K =
            (DB.adjf.comp DB.adjg).counit.app K) ∧
        (∀ K : spFiniteConstructibleTorCategory Z A,
          chCoeff.hom.app K ≫ thetaB.hom.app ((reductionCtfScalar φ Z hSZ).obj K) =
            (reductionCtfScalar φ X hSX).map (thetaA.hom.app K) ≫
              cfCoeff.hom.app (DA.Hg.obj K) ≫ DB.Hf.map (cgCoeff.hom.app K))

private theorem finite_scalar_obj {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u})
    (h : ∀ M : spFiniteConstructibleTorCategory T A,
      spFiniteConstructibleTor T B ((scalarExtensionFunctor φ T).obj M.obj))
    (M : spFiniteConstructibleTorCategory T A) :
    ((reductionCtfScalar φ T h).obj M).obj = (scalarExtensionFunctor φ T).obj M.obj := rfl

private theorem finite_scalar_map {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u})
    (h : ∀ M : spFiniteConstructibleTorCategory T A,
      spFiniteConstructibleTor T B ((scalarExtensionFunctor φ T).obj M.obj))
    {M N : spFiniteConstructibleTorCategory T A} (v : M ⟶ N) :
    ((reductionCtfScalar φ T h).map v).hom = (scalarExtensionFunctor φ T).map v.hom := rfl

private theorem finite_support_obj (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ M : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R c.i c.g).obj M.obj))
    (M : spFiniteConstructibleTorCategory X R) :
    ((finiteAdjointSupport R c h).obj M).obj =
      (reductionCompactSupport R c.i c.g).obj M.obj := rfl

private theorem finite_support_map (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ M : spFiniteConstructibleTorCategory X R,
      spFiniteConstructibleTor Y R ((reductionCompactSupport R c.i c.g).obj M.obj))
    {M N : spFiniteConstructibleTorCategory X R} (v : M ⟶ N) :
    ((finiteAdjointSupport R c h).map v).hom =
      (reductionCompactSupport R c.i c.g).map v.hom := rfl

private theorem finite_bounded {T : Scheme.{u}} {A : Type u} [CommRing A] [Finite A]
    (M : spFiniteConstructibleTorCategory T A) :
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj M.obj)} := by
  obtain ⟨a, b, _, hb⟩ := M.property.1
  apply (Set.finite_Icc a b).subset
  intro i hi
  exact ⟨le_of_not_gt (fun h ↦ hi (hb i (Or.inl h))),
    le_of_not_gt (fun h ↦ hi (hb i (Or.inr h)))⟩

private structure FiniteCoefficientPair {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) where
  hFA : ∀ M : spFiniteConstructibleTorCategory X A,
    spFiniteConstructibleTor Y A ((reductionCompactSupport A c.i c.g).obj M.obj)
  hFB : ∀ M : spFiniteConstructibleTorCategory X B,
    spFiniteConstructibleTor Y B ((reductionCompactSupport B c.i c.g).obj M.obj)
  hSX : ∀ M : spFiniteConstructibleTorCategory X A,
    spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj)
  hSY : ∀ M : spFiniteConstructibleTorCategory Y A,
    spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj M.obj)
  HA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A
  HB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B
  adjA : finiteAdjointSupport A c hFA ⊣ HA
  adjB : finiteAdjointSupport B c hFB ⊣ HB
  beta : finiteAdjointSupport A c hFA ⋙ reductionCtfScalar φ Y hSY ≅
    reductionCtfScalar φ X hSX ⋙ finiteAdjointSupport B c hFB
  hbeta : ∀ M, (beta.hom.app M).hom =
    (reductionDirectImageComparison φ c.i c.g).app M.obj
  gamma : HA ⋙ reductionCtfScalar φ X hSX ≅ reductionCtfScalar φ Y hSY ⋙ HB
  counit : ∀ K, (finiteAdjointSupport B c hFB).map (gamma.hom.app K) ≫
      adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K) =
    beta.inv.app (HA.obj K) ≫ (reductionCtfScalar φ Y hSY).map (adjA.counit.app K)

private theorem finiteCoefficientIso_exists
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [QuasiCompact f]
    (c : Compactification f)
    (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime] (hpℓ : p ≠ ℓ) [CharP k p]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A c.i c.g).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B c.i c.g).obj M.obj))
    (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (hSY : ∀ M : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj M.obj)) :
    ∃ beta : finiteAdjointSupport A c hFA ⋙ reductionCtfScalar φ Y hSY ≅
      reductionCtfScalar φ X hSX ⋙ finiteAdjointSupport B c hFB,
      ∀ M, (beta.hom.app M).hom =
        (reductionDirectImageComparison φ c.i c.g).app M.obj := by
  have hbi (M : spFiniteConstructibleTorCategory X A) :
      IsIso ((reductionDirectImageComparison φ c.i c.g).app M.obj) :=
    (reductionDirectImage_isIso ℓ p (Fact.out : p.Prime).pos hpℓ k f
      c.i c.g c.comm.symm hA hB φ M.obj (finite_bounded M)
        M.property.2.1 M.property.2.2).1
  let beta : finiteAdjointSupport A c hFA ⋙ reductionCtfScalar φ Y hSY ≅
      reductionCtfScalar φ X hSX ⋙ finiteAdjointSupport B c hFB :=
    NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
      (asIso ((reductionDirectImageComparison φ c.i c.g).app M.obj))) (by
        intro M N v
        apply ObjectProperty.hom_ext
        exact (reductionDirectImageComparison φ c.i c.g).naturality v.hom)
  exact ⟨beta, fun _ ↦ rfl⟩

private theorem finiteCoefficientPair_exists
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [QuasiCompact f]
    (c : Compactification f)
    (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime] (hpℓ : p ≠ ℓ) [CharP k p]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B) :
    Nonempty (FiniteCoefficientPair c φ) := by
  obtain ⟨hFA, hFB, hSX, hSY, GA, GB, adjA, adjB, _, _, hb, c',
    ⟨hc, hi, _⟩, _⟩ :=
    reductionExceptional_isIso ℓ p (Fact.out : p.Prime).pos hpℓ k f d
      c.i c.g c.comm.symm hA hB φ
  obtain ⟨beta, hbeta⟩ :=
    finiteCoefficientIso_exists k f c ℓ p hpℓ hA hB φ hFA hFB hSX hSY
  have (K : spFiniteConstructibleTorCategory Y A) : IsIso (c'.app K) := hi K
  let gamma : GA ⋙ reductionCtfScalar φ X hSX ≅ reductionCtfScalar φ Y hSY ⋙ GB :=
    NatIso.ofComponents (fun K ↦ asIso (c'.app K)) (fun v ↦ c'.naturality v)
  refine ⟨⟨hFA, hFB, hSX, hSY, GA, GB, adjA, adjB, beta,
    hbeta, gamma, ?_⟩⟩
  intro K
  apply ObjectProperty.hom_ext
  have hinv : (beta.inv.app (GA.obj K)).hom =
      @inv _ _ _ _ ((reductionDirectImageComparison φ c.i c.g).app (GA.obj K).obj)
        (hb K) := by
    have h := (spFiniteConstructibleTor Y B).ι.map_inv (beta.hom.app (GA.obj K))
    simpa only [NatIso.inv_hom_app, ObjectProperty.ι_map, hbeta] using h
  simpa only [ObjectProperty.FullSubcategory.comp_hom, finite_scalar_map,
    finite_support_map, hinv, gamma, NatIso.ofComponents_hom_app, asIso_hom] using hc K

section Finite
variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
  [QuasiCompact (Z ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))

/-- The finite result with quasi-compactness derived from the standing setting.
Source: blueprint comparisons (1)--(2) (blueprint: det-sp-composition-comparisons). -/
def spCompositionFiniteResult {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) : Type _ :=
  letI : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  letI : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  letI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  letI : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (Z ↘ Spec (.of k))
  letI : QuasiCompact f := inferInstance
  letI : QuasiCompact g := inferInstance
  SpCompositionFinite cf cg ch φ

/-- Finite coefficient composition, with the specified canonical comparisons.
Source: blueprint comparisons (1)--(2) (blueprint: det-sp-composition-comparisons).

Proof:
1. Finite type over the field gives Noetherian schemes. Smooth dimensions add, and
scalar extension preserves Dctf (det-sp-scalar-extension-functor). Thus all six
constructible adjunctions of sk-prop-sf-rf-shriek-preservation apply.
2. Transport the proper/open normalized etale compact-support compositor through the
fully faithful constructible origin equivalence. lem-sp-finite-compact-site-coherence
identifies its site normalization, independent of compatible compactification choices.
3. An etale origin of M has the same Tor interval: exact comparison pullback commutes
with tensor and detects zero sheaves, by its invertible unit. Apply
lem-sp-et-proet-coefficient-compatibility to that origin. Its composition and refinement
equations give the displayed left coefficient identity for the specified b maps.
4. det-sp-reduction-exceptional supplies the counit-transpose coefficient maps.
lem-sp-finite-adjoint-compositor-transposes gives the unique normalized right
compositors, their composite counits, and the right coefficient identity. No flatness
or finite projective dimension of B over A occurs.
-/
theorem compositionComparisons_finite
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
  [QuasiCompact (Z ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime] (_hpℓ : p ≠ ℓ) [CharP k p]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B) :
    Nonempty (spCompositionFiniteResult k f g cf cg ch φ) := by
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : CompactSpace Z :=
    QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  let : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  let : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (Z ↘ Spec (.of k))
  let : QuasiCompact f := inferInstance
  let : QuasiCompact g := inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let : IsNoetherian Y := ⟨⟩
  let : IsNoetherian Z := ⟨⟩
  let : SmoothOfRelativeDimension (d + e) (f ≫ g) := inferInstance
  obtain ⟨Pf⟩ := finiteCoefficientPair_exists k f cf ℓ p _hpℓ d _hA _hB φ
  obtain ⟨Pg⟩ := finiteCoefficientPair_exists k g cg ℓ p _hpℓ e _hA _hB φ
  obtain ⟨Ph⟩ := finiteCoefficientPair_exists k (f ≫ g) ch ℓ p _hpℓ (d + e) _hA _hB φ
  obtain ⟨alphaA, hnA⟩ :=
    finiteSupportCompositor_exists A cf cg ch Pf.hFA Pg.hFA Ph.hFA
  obtain ⟨alphaB, hnB⟩ :=
    finiteSupportCompositor_exists B cf cg ch Pf.hFB Pg.hFB Ph.hFB
  let DA : FiniteAdjointCompositorDatum A cf cg ch :=
    ⟨Pf.hFA, Pg.hFA, Ph.hFA, Pf.HA, Pg.HA, Ph.HA,
      Pf.adjA, Pg.adjA, Ph.adjA, alphaA, hnA⟩
  let DB : FiniteAdjointCompositorDatum B cf cg ch :=
    ⟨Pf.hFB, Pg.hFB, Ph.hFB, Pf.HB, Pg.HB, Ph.HB,
      Pf.adjB, Pg.adjB, Ph.adjB, alphaB, hnB⟩
  have hleft : ∀ M,
      (reductionCtfScalar φ Z Pg.hSY).map (DA.alpha.hom.app M) ≫ Ph.beta.hom.app M =
        Pg.beta.hom.app ((finiteAdjointSupport A cf DA.hFf).obj M) ≫
          (finiteAdjointSupport B cg DB.hFg).map (Pf.beta.hom.app M) ≫
          DB.alpha.hom.app ((reductionCtfScalar φ X Pf.hSX).obj M) := by
    intro M
    apply ObjectProperty.hom_ext
    simpa only [ObjectProperty.FullSubcategory.comp_hom, finite_scalar_map,
      finite_support_map, Pf.hbeta, Pg.hbeta, Ph.hbeta] using
      finiteSupportCompositor_coefficient k f g cf cg ch ℓ p _hpℓ d e _hA _hB φ
        DA DB Pf.hSX M
  obtain ⟨ta, tb, hta, htb, hua, hub, hca, hcb, _, hr⟩ :=
    finiteAdjointCompositorTransposes ℓ p _hpℓ k f g d e cf cg ch _hA _hB φ DA DB
      Pf.hSX Pf.hSY Pg.hSY Pf.beta Pg.beta Ph.beta Pf.hbeta Pg.hbeta Ph.hbeta
      Pf.gamma Pg.gamma Ph.gamma Pf.counit Pg.counit Ph.counit hleft
  exact ⟨⟨DA, DB, Pf.hSX, Pf.hSY, Pg.hSY, Pf.beta, Pg.beta, Ph.beta,
    Pf.hbeta, Pg.hbeta, Ph.hbeta, Pf.gamma, Pg.gamma, Ph.gamma,
    Pf.counit, Pg.counit, Ph.counit, hleft,
    ⟨ta, tb, hta, htb, hua, hub, hca, hcb, hr⟩⟩⟩

end Finite

private theorem mateIsoOfCounit
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {F : C ⥤ D} {H : D ⥤ C} {F' : C' ⥤ D'} {H' : D' ⥤ C'}
    (a : F ⊣ H) (a' : F' ⊣ H') (S : C ⥤ C') (T : D ⥤ D')
    (beta : F ⋙ T ≅ S ⋙ F')
    (z : ∀ K, S.obj (H.obj K) ⟶ H'.obj (T.obj K))
    (hz : ∀ K, F'.map (z K) ≫ a'.counit.app (T.obj K) =
      beta.inv.app (H.obj K) ≫ T.map (a.counit.app K))
    (hi : ∀ K, IsIso (z K)) :
    ∃ c : H ⋙ S ≅ T ⋙ H', ∀ K, c.hom.app K = z K := by
  have natural (K L : D) (v : K ⟶ L) :
      S.map (H.map v) ≫ z L = z K ≫ H'.map (T.map v) := by
    apply (a'.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [hz, a'.counit_naturality]
    conv_rhs => rw [← Category.assoc, hz]
    have hn := beta.inv.naturality_assoc (H.map v) (T.map (a.counit.app L))
    dsimp only [Functor.comp_map] at hn
    have he := a.counit.naturality v
    dsimp only [Functor.comp_map, Functor.id_map] at he
    rw [hn, ← T.map_comp, he, T.map_comp, Category.assoc]
  let component (K : D) : (H ⋙ S).obj K ≅ (T ⋙ H').obj K := by
    let := hi K
    exact asIso (z K)
  let c : H ⋙ S ≅ T ⋙ H' := NatIso.ofComponents component (by
    intro K L v
    change S.map (H.map v) ≫ z L = z K ≫ H'.map (T.map v)
    exact natural K L v)
  exact ⟨c, fun _ ↦ rfl⟩

section Towers
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
  [QuasiCompact (Z ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))


private theorem tower_coefficient_torsion (n : ℕ) :
    ∃ r : ℕ, ∀ x : SpTowerShriek.R l E n, (l ^ r) • x = 0 := by
  refine ⟨n + 1, fun x ↦ ?_⟩
  have hz : ((l ^ (n + 1) : ℕ) : SpTowerShriek.R l E n) = 0 := by
    have hm := Ideal.pow_mem_pow
      (Ideal.mem_span_singleton_self (l : Padic.coefficientExtensionIntegers l E)) (n + 1)
    simpa only [map_pow, map_natCast, Nat.cast_pow] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr hm)
  rw [nsmul_eq_mul, hz, zero_mul]

private theorem tower_coefficient_counit
    {U V : Scheme.{u}} {h : U ⟶ V} {c : Compactification h}
    (P : TowerAdjointCompositor.Pair l E b o q c)
    {m n : ℕ} (v : m ≤ n)
    (beta : TowerAdjointCompositor.finiteLeft l E b o q P n ⋙
        reductionCtfScalar (SpTowerCalculus.quotient l E v) V (P.levels.scalarY m n v) ≅
      reductionCtfScalar (SpTowerCalculus.quotient l E v) U (P.levels.scalarX m n v) ⋙
        TowerAdjointCompositor.finiteLeft l E b o q P m)
    (hb : ∀ M, (beta.hom.app M).hom =
      (reductionDirectImageComparison (SpTowerCalculus.quotient l E v) c.i c.g).app M.obj)
    (K : spFiniteConstructibleTorCategory V (SpTowerShriek.R l E n)) :
    (TowerAdjointCompositor.finiteLeft l E b o q P m).map
        (TowerAdjointCompositor.coefficient l E b o q P v K) ≫
      (P.levels.adjunction m).counit.app
        ((reductionCtfScalar (SpTowerCalculus.quotient l E v) V
          (P.levels.scalarY m n v)).obj K) =
    beta.inv.app ((P.levels.right n).obj K) ≫
      (reductionCtfScalar (SpTowerCalculus.quotient l E v) V
        (P.levels.scalarY m n v)).map ((P.levels.adjunction n).counit.app K) := by
  have hi := P.levels.direct_image_iso m n v K
  have hinv : (beta.inv.app ((P.levels.right n).obj K)).hom =
      @inv _ _ _ _
        ((reductionDirectImageComparison (SpTowerCalculus.quotient l E v) c.i c.g).app
          ((P.levels.right n).obj K).obj) hi := by
    have h := (spFiniteConstructibleTor V (SpTowerShriek.R l E m)).ι.map_inv
      (beta.hom.app ((P.levels.right n).obj K))
    simpa only [NatIso.inv_hom_app, ObjectProperty.ι_map, hb] using h
  let S := reductionCtfScalar (SpTowerCalculus.quotient l E v) U
    (P.levels.scalarX m n v)
  let T := reductionCtfScalar (SpTowerCalculus.quotient l E v) V
    (P.levels.scalarY m n v)
  let source := S.obj ((P.levels.right n).obj K)
  let target := T.obj K
  let a : (TowerAdjointCompositor.finiteLeft l E b o q P m).obj source ⟶ target :=
    ObjectProperty.homMk
      (@inv _ _ _ _ ((reductionDirectImageComparison (SpTowerCalculus.quotient l E v)
        c.i c.g).app ((P.levels.right n).obj K).obj) hi ≫
        (scalarExtensionFunctor (SpTowerCalculus.quotient l E v) V).map
          ((P.levels.adjunction n).counit.app K).hom)
  have he := (P.levels.adjunction m).homEquiv source target |>.symm_apply_apply a
  rw [Adjunction.homEquiv_counit] at he
  apply ObjectProperty.hom_ext
  simpa only [ObjectProperty.FullSubcategory.comp_hom, finite_scalar_map,
    finite_support_map, hinv, TowerAdjointCompositor.coefficient,
    SpTowerGluing.coefficientMate, a, source, target, S, T,
    ObjectProperty.homMk_hom, Functor.id_obj, Functor.comp_obj,
    finite_scalar_obj, finite_support_obj] using
    congrArg (fun t ↦ t.hom) he

/-- The actual tower composition assertion. Auxiliary morphism properties are derived
from the standing setting inside this type, rather than added as hypotheses.
The finite compositors and finite coefficient identities are outputs as well.
Source: blueprint comparisons (3) (blueprint: det-sp-composition-comparisons). -/
def spCompositionTowerResult
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (hP : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z hP)
    (Pf : TowerAdjointCompositor.Pair l E b o q cf)
    (Pg : TowerAdjointCompositor.Pair l E b o q cg)
    (Ph : TowerAdjointCompositor.Pair l E b o q ch) : Prop :=
  letI : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  letI : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  letI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  letI : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (Z ↘ Spec (.of k))
  letI : QuasiCompact f := inferInstance
  letI : QuasiCompact g := inferInstance
  letI : IsSeparated (f ≫ (Y ↘ Spec (.of k))) :=
    (comp_over f (Spec (.of k))).symm ▸ inferInstance
  letI : IsSeparated (g ≫ (Z ↘ Spec (.of k))) :=
    (comp_over g (Spec (.of k))).symm ▸ inferInstance
  letI : IsSeparated f := IsSeparated.of_comp f (Y ↘ Spec (.of k))
  letI : IsSeparated g := IsSeparated.of_comp g (Z ↘ Spec (.of k))
  letI : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of k))) :=
    (comp_over f (Spec (.of k))).symm ▸ inferInstance
  letI : LocallyOfFiniteType (g ≫ (Z ↘ Spec (.of k))) :=
    (comp_over g (Spec (.of k))).symm ▸ inferInstance
  letI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  letI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (Z ↘ Spec (.of k))
  ∃ A : ∀ n : ℕ, FiniteAdjointCompositorDatum (SpTowerShriek.R l E n) cf cg ch,
    TowerAdjointCompositor.FiniteIdentities l E b o q Pf Pg Ph A ∧
    ∃ alpha : TowerAdjointCompositor.left l E b o q Pf ⋙
        TowerAdjointCompositor.left l E b o q Pg ≅ TowerAdjointCompositor.left l E b o q Ph,
    ∃ theta : Ph.right ≅ Pg.right ⋙ Pf.right,
      TowerAdjointCompositor.Laws l E b o q k z hP cal Pf Pg Ph A alpha theta

/-- Composition in the ordinary derived category of strict coefficient towers, before
any finite evaluation, preserving the normalized subcategories and all reduction maps.
Source: blueprint comparisons (3) (blueprint: det-sp-composition-comparisons).

Proof:
1. Apply finite composition comparisons (1)--(2) to the actual ell-power quotient
rings and quotient homomorphisms, with the finite adjunctions fixed by the level data.
This supplies the proper/open alpha family and its b and c equations, including m=n.
2. Apply lem-sp-tower-adjoint-compositor-realization. Its left compositor is the
actual tower-calculus proper/open compositor, not a chosen lift of finite morphisms.
Its right compositor is the unique composite-counit-preserving right-adjoint comparison.
3. Its Laws give both evaluated compositors, the evaluated counits, the reduction
formulas for each of f,g,gf, both reduction squares and preservation of normalized
objects by all six operations. Uniform bounds are already built into their categories.
-/
theorem compositionComparisons_towers
    (p : ℕ) [Fact p.Prime] (_hpl : p ≠ l) [CharP k p]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (hP : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z hP)
    (Pf : TowerAdjointCompositor.Pair l E b o q cf)
    (Pg : TowerAdjointCompositor.Pair l E b o q cg)
    (Ph : TowerAdjointCompositor.Pair l E b o q ch) :
    spCompositionTowerResult l E b o q k f g cf cg ch z hP cal Pf Pg Ph := by
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : CompactSpace Z :=
    QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  let : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  let : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (Z ↘ Spec (.of k))
  let : QuasiCompact f := inferInstance
  let : QuasiCompact g := inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let : IsNoetherian Y := ⟨⟩
  let : IsNoetherian Z := ⟨⟩
  let : IsSeparated (f ≫ (Y ↘ Spec (.of k))) :=
    (comp_over f (Spec (.of k))).symm ▸ inferInstance
  let : IsSeparated (g ≫ (Z ↘ Spec (.of k))) :=
    (comp_over g (Spec (.of k))).symm ▸ inferInstance
  let : IsSeparated f := IsSeparated.of_comp f (Y ↘ Spec (.of k))
  let : IsSeparated g := IsSeparated.of_comp g (Z ↘ Spec (.of k))
  let : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of k))) :=
    (comp_over f (Spec (.of k))).symm ▸ inferInstance
  let : LocallyOfFiniteType (g ≫ (Z ↘ Spec (.of k))) :=
    (comp_over g (Spec (.of k))).symm ▸ inferInstance
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  let : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (Z ↘ Spec (.of k))
  have ha (n : ℕ) := finiteSupportCompositor_exists (SpTowerShriek.R l E n) cf cg ch
    (Pf.levels.finite_closed n) (Pg.levels.finite_closed n) (Ph.levels.finite_closed n)
  choose alpha hn using ha
  let A (n : ℕ) : FiniteAdjointCompositorDatum (SpTowerShriek.R l E n) cf cg ch :=
    ⟨Pf.levels.finite_closed n, Pg.levels.finite_closed n, Ph.levels.finite_closed n,
      Pf.levels.right n, Pg.levels.right n, Ph.levels.right n,
      Pf.levels.adjunction n, Pg.levels.adjunction n, Ph.levels.adjunction n, alpha n, hn n⟩
  have ht (n : ℕ) (K : spFiniteConstructibleTorCategory Z (SpTowerShriek.R l E n)) :
      (finiteAdjointSupport (SpTowerShriek.R l E n) cf (A n).hFf ⋙
        finiteAdjointSupport (SpTowerShriek.R l E n) cg (A n).hFg).map
          ((TowerAdjointCompositor.finiteTheta l E b o q Pf Pg Ph A n).hom.app K) ≫
        ((A n).adjf.comp (A n).adjg).counit.app K =
      (A n).alpha.hom.app ((A n).Hh.obj K) ≫ (A n).adjh.counit.app K := by
    have h := (Ph.levels.adjunction n).rightAdjointUniq_hom_app_counit
      (((Pf.levels.adjunction n).comp (Pg.levels.adjunction n)).ofNatIsoLeft (A n).alpha) K
    apply (cancel_epi ((A n).alpha.inv.app _)).mp
    dsimp only [A] at h ⊢
    simpa only [TowerAdjointCompositor.finiteTheta, Adjunction.ofNatIsoLeft_counit,
      NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc,
      ← NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc] using h
  have hfinite : TowerAdjointCompositor.FiniteIdentities l E b o q Pf Pg Ph A := by
    have hdata : ∀ (m n : ℕ) (v : m ≤ n)
        (K : spFiniteConstructibleTorCategory Z (SpTowerShriek.R l E n)),
        TowerAdjointCompositor.coefficient l E b o q Ph v K ≫
            (TowerAdjointCompositor.finiteTheta l E b o q Pf Pg Ph A m).hom.app
              ((reductionCtfScalar (SpTowerCalculus.quotient l E v) Z
                (Ph.levels.scalarY m n v)).obj K) =
          (reductionCtfScalar (SpTowerCalculus.quotient l E v) X
            (Ph.levels.scalarX m n v)).map
              ((TowerAdjointCompositor.finiteTheta l E b o q Pf Pg Ph A n).hom.app K) ≫
            TowerAdjointCompositor.coefficient l E b o q Pf v ((Pg.levels.right n).obj K) ≫
            (Pf.levels.right m).map (TowerAdjointCompositor.coefficient l E b o q Pg v K) := by
      intro m n v
      let φ := SpTowerCalculus.quotient l E v
      obtain ⟨bf, hbf⟩ := finiteCoefficientIso_exists k f cf l p _hpl
        (tower_coefficient_torsion l E n) (tower_coefficient_torsion l E m) φ
        (A n).hFf (A m).hFf (Pf.levels.scalarX m n v) (Pf.levels.scalarY m n v)
      obtain ⟨bg, hbg⟩ := finiteCoefficientIso_exists k g cg l p _hpl
        (tower_coefficient_torsion l E n) (tower_coefficient_torsion l E m) φ
        (A n).hFg (A m).hFg (Pg.levels.scalarX m n v) (Pg.levels.scalarY m n v)
      obtain ⟨bh, hbh⟩ := finiteCoefficientIso_exists k (f ≫ g) ch l p _hpl
        (tower_coefficient_torsion l E n) (tower_coefficient_torsion l E m) φ
        (A n).hFh (A m).hFh (Ph.levels.scalarX m n v) (Ph.levels.scalarY m n v)
      have hleft : ∀ M,
          (reductionCtfScalar φ Z (Ph.levels.scalarY m n v)).map
              ((A n).alpha.hom.app M) ≫ bh.hom.app M =
          bg.hom.app ((finiteAdjointSupport (SpTowerShriek.R l E n) cf (A n).hFf).obj M) ≫
            (finiteAdjointSupport (SpTowerShriek.R l E m) cg (A m).hFg).map (bf.hom.app M) ≫
            (A m).alpha.hom.app
              ((reductionCtfScalar φ X (Pf.levels.scalarX m n v)).obj M) := by
        intro M
        apply ObjectProperty.hom_ext
        simpa only [ObjectProperty.FullSubcategory.comp_hom, finite_scalar_map,
          finite_support_map, hbf, hbg, hbh] using
          finiteSupportCompositor_coefficient k f g cf cg ch l p _hpl d e
            (tower_coefficient_torsion l E n) (tower_coefficient_torsion l E m) φ
            (A n) (A m) (Pf.levels.scalarX m n v) M
      obtain ⟨cf', hcf⟩ := mateIsoOfCounit (Pf.levels.adjunction n)
        (Pf.levels.adjunction m) _ _ bf
        (TowerAdjointCompositor.coefficient l E b o q Pf v)
        (tower_coefficient_counit l E b o q Pf v bf hbf)
        (Pf.levels.coefficient_iso m n v)
      obtain ⟨cg', hcg⟩ := mateIsoOfCounit (Pg.levels.adjunction n)
        (Pg.levels.adjunction m) _ _ bg
        (TowerAdjointCompositor.coefficient l E b o q Pg v)
        (tower_coefficient_counit l E b o q Pg v bg hbg)
        (Pg.levels.coefficient_iso m n v)
      obtain ⟨ch', hch⟩ := mateIsoOfCounit (Ph.levels.adjunction n)
        (Ph.levels.adjunction m) _ _ bh
        (TowerAdjointCompositor.coefficient l E b o q Ph v)
        (tower_coefficient_counit l E b o q Ph v bh hbh)
        (Ph.levels.coefficient_iso m n v)
      have hcfC := tower_coefficient_counit l E b o q Pf v bf hbf
      have hcgC := tower_coefficient_counit l E b o q Pg v bg hbg
      have hchC := tower_coefficient_counit l E b o q Ph v bh hbh
      obtain ⟨ta, tb, _, _, hua, hub, _, _, _, hr⟩ :=
        finiteAdjointCompositorTransposes l p _hpl k f g d e cf cg ch
          (tower_coefficient_torsion l E n) (tower_coefficient_torsion l E m) φ
          (A n) (A m) (Pf.levels.scalarX m n v) (Pf.levels.scalarY m n v)
          (Pg.levels.scalarY m n v) bf bg bh hbf hbg hbh cf' cg' ch'
          (by simpa only [hcf] using hcfC) (by simpa only [hcg] using hcgC)
          (by simpa only [hch] using hchC) hleft
      have heqa := hua (TowerAdjointCompositor.finiteTheta l E b o q Pf Pg Ph A n) (ht n)
      have heqb := hub (TowerAdjointCompositor.finiteTheta l E b o q Pf Pg Ph A m) (ht m)
      rw [← heqa, ← heqb] at hr
      simp only [hcf, hcg, hch] at hr
      exact hr
    exact ⟨fun m n v M ↦ finiteSupportCompositor_coefficient k f g cf cg ch l p _hpl d e
        (tower_coefficient_torsion l E n) (tower_coefficient_torsion l E m)
        (SpTowerCalculus.quotient l E v) (A n) (A m) (Pf.levels.scalarX m n v) M,
      hdata⟩
  exact ⟨A, hfinite, TowerAdjointCompositor.towerAdjointCompositorRealization l E b o q
    p _hpl k d e z hP cal Pf Pg Ph A hfinite⟩

end Towers

/-- Integral composition laws for specified operations and their canonical reduction
comparisons. This is only the equations in (3), as a proposition; the result below
instantiates every functor and comparison by its published construction.
Source: blueprint comparisons (3) (blueprint: det-sp-composition-comparisons). -/
structure SpCompositionIntegralLaws
    {IX : Type uIX} {IY : Type uIY} {IZ : Type uIZ}
    {TX : Type uTX} {TY : Type uTY} {TZ : Type uTZ}
    [Category.{vIX} IX] [Category.{vIY} IY] [Category.{vIZ} IZ]
    [Category.{vTX} TX] [Category.{vTY} TY] [Category.{vTZ} TZ]
    (Ff : IX ⥤ IY) (Fg : IY ⥤ IZ) (Fh : IX ⥤ IZ)
    (Hf : IY ⥤ IX) (Hg : IZ ⥤ IY) (Hh : IZ ⥤ IX)
    (af : Ff ⊣ Hf) (ag : Fg ⊣ Hg) (ah : Fh ⊣ Hh)
    (rX : IX ⥤ TX) (rY : IY ⥤ TY) (rZ : IZ ⥤ TZ)
    (Tf : TX ⥤ TY) (Tg : TY ⥤ TZ) (Th : TX ⥤ TZ)
    (Uf : TY ⥤ TX) (Ug : TZ ⥤ TY) (Uh : TZ ⥤ TX)
    (bf : Ff ⋙ rY ≅ rX ⋙ Tf) (bg : Fg ⋙ rZ ≅ rY ⋙ Tg)
    (bh : Fh ⋙ rZ ≅ rX ⋙ Th)
    (cf : Hf ⋙ rX ≅ rY ⋙ Uf) (cg : Hg ⋙ rY ≅ rZ ⋙ Ug)
    (ch : Hh ⋙ rX ≅ rZ ⋙ Uh)
    (alphaTower : Tf ⋙ Tg ≅ Th) (thetaTower : Uh ≅ Ug ⋙ Uf)
    (alpha : Ff ⋙ Fg ≅ Fh) (theta : Hh ≅ Hg ⋙ Hf) : Prop where
  left_reduction : ∀ M,
    rZ.map (alpha.hom.app M) ≫ bh.hom.app M =
      bg.hom.app (Ff.obj M) ≫ Tg.map (bf.hom.app M) ≫ alphaTower.hom.app (rX.obj M)
  right_reduction : ∀ K,
    rX.map (theta.hom.app K) ≫ cf.hom.app (Hg.obj K) ≫ Uf.map (cg.hom.app K) =
      ch.hom.app K ≫ thetaTower.hom.app (rZ.obj K)
  counit : ∀ K,
    (Ff ⋙ Fg).map (theta.hom.app K) ≫ (af.comp ag).counit.app K =
      alpha.hom.app (Hh.obj K) ≫ ah.counit.app K
  unique : ∀ t : Hh ≅ Hg ⋙ Hf,
    (∀ K, (Ff ⋙ Fg).map (t.hom.app K) ≫ (af.comp ag).counit.app K =
      alpha.hom.app (Hh.obj K) ≫ ah.counit.app K) → t = theta
  composite_counit : ∀ K,
    Fg.map (af.counit.app (Hg.obj K)) ≫ ag.counit.app K = (af.comp ag).counit.app K

section Descent
open WeilConjectures.SemilinearSections
variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type u} [Category.{u} C₁] [Category.{u} C₂]
  [Category.{u} C₃] [Category.{u} D₁] [Category.{u} D₂] [Category.{u} D₃]

private theorem composition_of_fully_faithful_reductions
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {H : C₁ ⥤ C₃}
    {RF : C₂ ⥤ C₁} {RG : C₃ ⥤ C₂} {RH : C₃ ⥤ C₁}
    {f : D₁ ⥤ D₂} {g : D₂ ⥤ D₃} {h : D₁ ⥤ D₃}
    {rf : D₂ ⥤ D₁} {rg : D₃ ⥤ D₂} {rh : D₃ ⥤ D₁}
    {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂} {E₃ : C₃ ⥤ D₃}
    (aF : F ⊣ RF) (aG : G ⊣ RG) (aH : H ⊣ RH)
    (af : f ⊣ rf) (ag : g ⊣ rg) (ah : h ⊣ rh)
    (AF : AdjunctionEvaluation E₁ E₂ aF af)
    (AG : AdjunctionEvaluation E₂ E₃ aG ag)
    (AH : AdjunctionEvaluation E₁ E₃ aH ah)
    (full : E₃.FullyFaithful) (alphaₙ : f ⋙ g ≅ h) (thetaₙ : rh ≅ rg ⋙ rf)
    (hcₙ : ∀ K, (f ⋙ g).map (thetaₙ.hom.app K) ≫ (af.comp ag).counit.app K =
      alphaₙ.hom.app (rh.obj K) ≫ ah.counit.app K) :
    ∃ alpha : F ⋙ G ≅ H, ∃ theta : RH ≅ RG ⋙ RF,
      SpCompositionIntegralLaws F G H RF RG RH aF aG aH E₁ E₂ E₃ f g h rf rg rh
        AF.left AG.left AH.left AF.right AG.right AH.right alphaₙ thetaₙ alpha theta := by
  let beta : (F ⋙ G) ⋙ E₃ ≅ H ⋙ E₃ :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F AG.left ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight AF.left g ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E₁ alphaₙ ≪≫ AH.left.symm
  let alpha : F ⋙ G ≅ H := (full.whiskeringRight C₁).preimageIso beta
  have ha (M : C₁) : E₃.map (alpha.hom.app M) ≫ AH.left.hom.app M =
      AG.left.hom.app (F.obj M) ≫ g.map (AF.left.hom.app M) ≫
        alphaₙ.hom.app (E₁.obj M) := by
    have hp := congrArg (fun t ↦ t.app M)
      ((full.whiskeringRight C₁).map_preimage beta.hom)
    change E₃.map (alpha.hom.app M) = beta.hom.app M at hp
    rw [hp]
    simp [beta, Category.assoc]
  let theta := (aH.ofNatIsoLeft alpha.symm).rightAdjointUniq (aF.comp aG)
  have hc (K : C₃) : (F ⋙ G).map (theta.hom.app K) ≫ (aF.comp aG).counit.app K =
      alpha.hom.app (RH.obj K) ≫ aH.counit.app K :=
    (aH.ofNatIsoLeft alpha.symm).rightAdjointUniq_hom_app_counit (aF.comp aG) K
  refine ⟨alpha, theta, ⟨ha, ?_, hc, ?_, ?_⟩⟩
  · exact evaluated_compositor aF aG aH af ag ah AF AG AH
      alpha alphaₙ theta thetaₙ hc hcₙ ha
  · intro t ht
    ext K
    apply ((aF.comp aG).homEquiv _ _).symm.injective
    simpa only [Adjunction.homEquiv_counit] using (ht K).trans (hc K).symm
  · exact fun K ↦ (aF.comp_counit_app aG K).symm
end Descent

/-- The universe lift of Q_l has degree one over Q_l. This is the existing linear
 equivalence's finite-dimensional instance, and imposes no universe equality on schemes.
Source: blueprint comparisons (3) (blueprint: det-sp-composition-comparisons). -/
instance spCompositionPadicFinite (l : ℕ) [Fact l.Prime] :
    FiniteDimensional (Padic l) (ULift.{u} (Padic l)) :=
  (ULift.moduleEquiv (R := Padic l) (M := Padic l)).symm.finiteDimensional

section Integral
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
  {X Y Z V W U : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [QuasiCompact (Z ↘ Spec (.of D.k))]
  (jf : X ⟶ V) [IsOpenImmersion jf] (pf : V ⟶ Y) [IsProper pf]
  (jg : Y ⟶ W) [IsOpenImmersion jg] (pg : W ⟶ Z) [IsProper pg]
  (jh : X ⟶ U) [IsOpenImmersion jh] (ph : U ⟶ Z) [IsProper ph]
  [(jf ≫ pf).IsOver (Spec (.of D.k))] [(jg ≫ pg).IsOver (Spec (.of D.k))]
  [(jh ≫ ph).IsOver (Spec (.of D.k))]
  (d e : ℕ)
  (b : SpTowerShriek.Base l (ULift.{u} (Padic l))) (o : SpTowerShriek.Operations l (ULift.{u}
    (Padic l)) b)
  (q : SpTowerCalculus.Coordinates l (ULift.{u} (Padic l)) b)
  (Pf : TowerAdjointCompositor.Pair l (ULift.{u} (Padic l)) b o q
    (SpTowerGamma.factorization jf pf))
  (Pg : TowerAdjointCompositor.Pair l (ULift.{u} (Padic l)) b o q
    (SpTowerGamma.factorization jg pg))
  (Ph : TowerAdjointCompositor.Pair l (ULift.{u} (Padic l)) b o q
    (SpTowerGamma.factorization jh ph))
  (wf : SpChartAdmissibility.Twists l (ULift.{u} (Padic l)) X)
  (wg : SpChartAdmissibility.Twists l (ULift.{u} (Padic l)) Y)
  (RX : SpReductionTower l (ULift.{u} (Padic l)) X (q.abelian X))
  (NX : SpNormalizedEquivalence l (ULift.{u} (Padic l)) X (q.abelian X) RX)
  (RY : SpReductionTower l (ULift.{u} (Padic l)) Y (q.abelian Y))
  (NY : SpNormalizedEquivalence l (ULift.{u} (Padic l)) Y (q.abelian Y) RY)
  (RZ : SpReductionTower l (ULift.{u} (Padic l)) Z (q.abelian Z))
  (NZ : SpNormalizedEquivalence l (ULift.{u} (Padic l)) Z (q.abelian Z) RZ)
  (If : SpIntegralAdjunction.realizationResult l (ULift.{u} (Padic l)) D jf pf d b o q wf
    RX NX RY NY Pf.closed Pf.right Pf.adj Pf.levels)
  (Ig : SpIntegralAdjunction.realizationResult l (ULift.{u} (Padic l)) D jg pg e b o q wg
    RY NY RZ NZ Pg.closed Pg.right Pg.adj Pg.levels)
  (Ih : SpIntegralAdjunction.realizationResult l (ULift.{u} (Padic l)) D jh ph (d + e) b o q wf
    RX NX RZ NZ Ph.closed Ph.right Ph.adj Ph.levels)

/-- The integral result in canonical coordinates, deriving all compactness instances
from the standing finite-type setting. Each operation is the published separately
derived support or total-limit exceptional functor, with the published adjunction.
Source: blueprint comparisons (3) (blueprint: det-sp-composition-comparisons). -/
def spCompositionIntegralResult
    (alphaTower : TowerAdjointCompositor.left l (ULift.{u} (Padic l)) b o q Pf ⋙
      TowerAdjointCompositor.left l (ULift.{u} (Padic l)) b o q Pg ≅
        TowerAdjointCompositor.left l (ULift.{u} (Padic l)) b o q Ph)
    (thetaTower : Ph.right ≅ Pg.right ⋙ Pf.right) : Prop :=
  letI : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  letI : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  letI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k))
  letI : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (Z ↘ Spec (.of D.k))
  letI : QuasiCompact (jf ≫ pf) := inferInstance
  letI : QuasiCompact (jg ≫ pg) := inferInstance
  letI : QuasiCompact (jh ≫ ph) := inferInstance
  letI : HasCompactification (jf ≫ pf) := (SpTowerGamma.factorization jf pf).hasCompactification
  letI : HasCompactification (jg ≫ pg) := (SpTowerGamma.factorization jg pg).hasCompactification
  letI : HasCompactification (jh ≫ ph) := (SpTowerGamma.factorization jh ph).hasCompactification
  ∃ alpha : (SpIntegralAdjunction.support l (ULift.{u} (Padic l)) (SpTowerGamma.factorization jf pf)
    If.support_closed) ⋙
      (SpIntegralAdjunction.support l (ULift.{u} (Padic l)) (SpTowerGamma.factorization jg pg)
        Ig.support_closed) ≅
      (SpIntegralAdjunction.support l (ULift.{u} (Padic l)) (SpTowerGamma.factorization jh ph)
        Ih.support_closed),
  ∃ theta : (SpIntegralAdjunction.right l (ULift.{u} (Padic l)) b q RX NX RZ Ih.reductionY Ph.right
    Ih.closed) ≅
      (SpIntegralAdjunction.right l (ULift.{u} (Padic l)) b q RY NY RZ Ig.reductionY Pg.right
        Ig.closed) ⋙
      (SpIntegralAdjunction.right l (ULift.{u} (Padic l)) b q RX NX RY If.reductionY Pf.right
        If.closed),
    SpCompositionIntegralLaws
      (SpIntegralAdjunction.support l (ULift.{u} (Padic l)) (SpTowerGamma.factorization jf pf)
        If.support_closed)
      (SpIntegralAdjunction.support l (ULift.{u} (Padic l)) (SpTowerGamma.factorization jg pg)
        Ig.support_closed)
      (SpIntegralAdjunction.support l (ULift.{u} (Padic l)) (SpTowerGamma.factorization jh ph)
        Ih.support_closed)
      (SpIntegralAdjunction.right l (ULift.{u} (Padic l)) b q RX NX RY If.reductionY Pf.right
        If.closed)
      (SpIntegralAdjunction.right l (ULift.{u} (Padic l)) b q RY NY RZ Ig.reductionY Pg.right
        Ig.closed)
      (SpIntegralAdjunction.right l (ULift.{u} (Padic l)) b q RX NX RZ Ih.reductionY Ph.right
        Ih.closed)
      If.adjunction Ig.adjunction Ih.adjunction
      (SpIntegralAdjunction.reduce l (ULift.{u} (Padic l)) X (q.abelian X) RX If.reductionX)
      (SpIntegralAdjunction.reduce l (ULift.{u} (Padic l)) Y (q.abelian Y) RY If.reductionY)
      (SpIntegralAdjunction.reduce l (ULift.{u} (Padic l)) Z (q.abelian Z) RZ Ig.reductionY)
      (TowerAdjointCompositor.left l (ULift.{u} (Padic l)) b o q Pf)
      (TowerAdjointCompositor.left l (ULift.{u} (Padic l)) b o q Pg)
      (TowerAdjointCompositor.left l (ULift.{u} (Padic l)) b o q Ph)
      Pf.right Pg.right Ph.right
      If.leftComparison Ig.leftComparison Ih.leftComparison
      If.rightComparison Ig.rightComparison Ih.rightComparison
      alphaTower thetaTower alpha theta

/-- Reduction/total-limit realization of the specified tower compositors, on the
completed Z_l coefficient Dbc categories and with the specified integral adjunctions.
The factorizations present f,g,gf, as the equation _hcomp specifies.
Source: blueprint comparisons (3) (blueprint: det-sp-composition-comparisons).

Proof:
1. Restrict the actual tower compositors to normalized objects. The equivalence of
 det-sp-normalized-equivalence has actual reduction as functor and scalar forgetting
followed by total derived inverse limit as inverse.
2. The comparisons in det-sp-integral-direct-image-tower and
 det-sp-integral-adjunction-bijection identify the separately derived integral support
and total-limit exceptional operations. Conjugate alphaTower by the leftComparison
maps and thetaTower by rightComparison. Full faithfulness of reduction descends both
isomorphisms. Naturality and the equivalence counit give the two reduction equations.
3. Reduce the composite integral counit and use its tower normalization. Substitute
the tower counit equation and the two reduction equations. Naturality of alphaTower
and faithfulness of reduction give the integral counit equation. Unique right adjoints
give uniqueness and identify the units as well. This is precisely the argument of
lem-sp-integral-compositor-limit-realization, with E=Q_l. The inverse equivalence is
total derived limit, so the result realizes the actual tower arrows.
-/
theorem compositionComparisons_integral (_hl : l ≠ D.p)
    [SmoothOfRelativeDimension d (jf ≫ pf)] [SmoothOfRelativeDimension e (jg ≫ pg)]
    (_hcomp : (jf ≫ pf) ≫ (jg ≫ pg) = jh ≫ ph)
    (alphaTower : TowerAdjointCompositor.left l (ULift.{u} (Padic l)) b o q Pf ⋙
      TowerAdjointCompositor.left l (ULift.{u} (Padic l)) b o q Pg ≅
        TowerAdjointCompositor.left l (ULift.{u} (Padic l)) b o q Ph)
    (thetaTower : Ph.right ≅ Pg.right ⋙ Pf.right)
    (_ht : ∀ K,
      (TowerAdjointCompositor.left l (ULift.{u} (Padic l)) b o q Pf ⋙
          TowerAdjointCompositor.left l (ULift.{u} (Padic l)) b o q Pg).map (thetaTower.hom.app K) ≫
        (Pf.adj.comp Pg.adj).counit.app K =
      alphaTower.hom.app (Ph.right.obj K) ≫ Ph.adj.counit.app K) :
    spCompositionIntegralResult l D jf pf jg pg jh ph d e b o q Pf Pg Ph wf wg
      RX NX RY NY RZ NZ If Ig Ih alphaTower thetaTower := by
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  let : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  let : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k))
  let : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (Z ↘ Spec (.of D.k))
  let : QuasiCompact (jf ≫ pf) := inferInstance
  let : QuasiCompact (jg ≫ pg) := inferInstance
  let : QuasiCompact (jh ≫ ph) := inferInstance
  let : HasCompactification (jf ≫ pf) := (SpTowerGamma.factorization jf pf).hasCompactification
  let : HasCompactification (jg ≫ pg) := (SpTowerGamma.factorization jg pg).hasCompactification
  let : HasCompactification (jh ≫ ph) := (SpTowerGamma.factorization jh ph).hasCompactification
  apply composition_of_fully_faithful_reductions If.adjunction Ig.adjunction Ih.adjunction
    Pf.adj Pg.adj Ph.adj
    (AF := {
      left := If.leftComparison
      right := If.rightComparison
      unit := ?_
      counit := ?_ })
    (AG := {
      left := Ig.leftComparison
      right := Ig.rightComparison
      unit := ?_
      counit := ?_ })
    (AH := {
      left := Ih.leftComparison
      right := Ih.rightComparison
      unit := ?_
      counit := ?_ })
    Ig.fullyFaithfulY alphaTower thetaTower _ht
  · intro M
    simp [If.unit_reduction, Category.assoc]
  · intro K
    rw [If.counit_reduction]
    simp
  · intro M
    simp [Ig.unit_reduction, Category.assoc]
  · intro K
    rw [Ig.counit_reduction]
    simp
  · intro M
    simp [Ih.unit_reduction, Category.assoc]
  · intro K
    rw [Ih.counit_reduction]
    simp

end Integral
end AlgebraicGeometry.ProEtale
