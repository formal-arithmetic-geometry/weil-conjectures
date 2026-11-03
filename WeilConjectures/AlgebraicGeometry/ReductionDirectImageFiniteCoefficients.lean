/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import all WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.AlgebraicGeometry.SupportedEtaleTensorOrigin.SupportedEtaleTensorOrigin
import WeilConjectures.AlgebraicGeometry.Proper.Etale.ProperEtaleOriginScalarData
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantProjectionFormula
import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginScalarProjectionSquare
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageScalarCocycle
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarCocycle

/-!
# Compactly supported direct image and finite coefficient extension

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/`,
`sk-lem-sp-reduction-direct-image.md`, statement and proof Steps 1-4
(blueprint: det-sp-reduction-direct-image).

The canonical comparison and scalar associators are the published constructions.
Both endpoints are required to have bounded intrinsically constructible cohomology
and finite Tor amplitude. The base field is finite or algebraically closed and its
characteristic differs from the coefficient prime; characteristic zero is included.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  directImageScalarComparison reductionOpenScalarIso
  scalarExtensionFunctor_composition
  Etale.derivedTensor Etale.lowerStar Etale.upperStar
  Etale.rightDerivedLowerStarProjectionMap Etale.scalarTensorIso

private theorem reductionGood_scalar (ℓ : ℕ) [Fact ℓ.Prime]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (T : Scheme.{u}) (K : proEtaleDerivedCategory T A) (h : ReductionGood T A K) :
    ReductionGood T B ((scalarExtensionFunctor φ T).obj K) := by
  obtain ⟨a, b, ht⟩ := h.2.2
  obtain ⟨hb, hc, htor⟩ := scalarExtensionFunctor_preserves_constructible_tor
    ℓ hA hB φ T K h.1 h.2.1 a b ht
  exact ⟨hb, hc, a, b, htor⟩

set_option maxHeartbeats 800000 in
-- Bound elaboration of the derived-functor transport.
private theorem reductionGood_compactSupport
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (hchar : ringChar k ≠ ℓ)
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) (j : X ⟶ Z) [IsOpenImmersion j]
    (p : Z ⟶ Y) [IsProper p] (hf : j ≫ p = f)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (M : proEtaleDerivedCategory X A) (hM : ReductionGood X A M) :
    ReductionGood Y A ((reductionCompactSupport A j p).obj M) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  have : HasInvertibleExponent (ULift.{u + 1} A) (Spec (.of k)) := by
    obtain ⟨n, hn⟩ := hA
    have hz : ((ℓ ^ n : ℕ) : ULift.{u + 1} A) = 0 := by
      apply ULift.ext
      change ((ℓ ^ n : ℕ) : A) = 0
      simpa only [nsmul_eq_mul, mul_one] using hn 1
    have hne : (ℓ : k) ≠ 0 :=
      CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) hchar
    have hu : IsUnit ((ℓ ^ n : ℕ) : k) := by
      rw [Nat.cast_pow]
      exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hne)
    exact ⟨ℓ ^ n, pow_pos (Fact.out : ℓ.Prime).pos _, hz, by
      simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  have : HasInvertibleExponent (ULift.{u + 1} A) Y :=
    HasInvertibleExponent.of_hom (Y ↘ Spec (.of k))
  let c : Compactification f := ⟨Z, p, j, hf.symm, inferInstance, inferInstance⟩
  have : HasCompactification f := c.hasCompactification
  let E := sfIntrinsicDerivedEquivalence X A
  let K := E.inverse.obj M
  have hK := reductionGood_iso (E.counitIso.app M).symm hM
  obtain ⟨hF, R, ha⟩ := CondensedRing.ordinary_small_adjunction A k
    (Y ↘ Spec (.of k)) f c
  have ho := hF K ((reductionGood_realization_iff X A K).mp hK)
  have ht := (reductionGood_realization_iff Y A _).mpr ho
  let er := (FiniteCompactScalar.compactRealizationIso A c).app K
  let ep := (Functor.isoWhiskerLeft
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory (properOriginPushIso A p)).app M
  exact reductionGood_iso
    (er.symm ≪≫ (sfIntrinsicCompactSupport c A).mapIso (E.counitIso.app M) ≪≫ ep.symm) ht

private theorem isIso_of_pasted_square
    {C : Type*} [Category C] {A B D E F G H : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ H)
    (e : A ⟶ F) (f : F ⟶ G) (g : G ⟶ H)
    [IsIso a] [IsIso b] [IsIso d] [IsIso e] [IsIso f] [IsIso g]
    (h : a ≫ b ≫ c ≫ d = e ≫ f ≫ g) : IsIso c := by
  have : IsIso (a ≫ b ≫ c ≫ d) := by rw [h]; infer_instance
  have : IsIso (b ≫ c ≫ d) := IsIso.of_isIso_comp_left a _
  have : IsIso (c ≫ d) := IsIso.of_isIso_comp_left b _
  exact IsIso.of_isIso_comp_right c d

set_option maxHeartbeats 800000 in
-- Bound elaboration of the derived-functor transport.
private theorem reductionEtaleProjection_isIso
    {R B : Type (u + 1)} [CommRing R] [CommRing B] [Finite R] [Finite B]
    [IsNoetherianRing R] (φ : R →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (N : ℕ)
    (hcd : ∀ (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R)) (q : ℕ),
      N < q → IsZero ((DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj F))))
    (K : Etale.DerivedCategoryModule R Z)
    (hK : ∃ b : ℤ, ∀ q : ℤ, b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) :
    IsIso (properOriginEtaleProjection φ p K) := by
  let BM := (ModuleCat.restrictScalars (φ)).obj
    (ModuleCat.of (B) (B))
  have : Finite BM := inferInstanceAs (Finite (B))
  have : Module.Finite R BM := Module.Finite.of_finite
  have : Module.FinitePresentation R BM := Module.finitePresentation_of_finite R BM
  have hπ := Etale.finiteConstantProjectionComponent_isIso R p N hcd K
    hK BM
  let ec : Etale.scalarCoefficient (φ) Y ≅
      (DerivedCategory.singleFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj BM) :=
    (DerivedCategory.singleFunctor
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) 0).mapIso
        ((constantCommuteCompose Y.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1}
            (φ))).app
              (ModuleCat.of (B) (B)))
  have : IsIso (((Etale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} R) p).app K).app
        (Etale.scalarCoefficient (φ) Y)) :=
    (NatTrans.isIso_app_iff_of_iso
      ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) p).app K) ec).mpr hπ
  have hproj : IsIso (properOriginEtaleProjection φ p K) := by
    unfold properOriginEtaleProjection
    infer_instance
  exact hproj

set_option maxHeartbeats 800000 in
-- Bound elaboration of the derived-functor transport.
private theorem reductionProper_isIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (k : Type u) [Field k] {Z Y : Scheme.{u}}
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (p : Z ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) Z)
    (hb : DerivedCategory.TStructure.t.bounded K)
    (hH : ∃ n : ℤ,
      (properOriginEtaleTensor (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z K).IsGE n) :
    IsIso ((directImageScalarComparison φ p).app
      ((finiteCoefficientIntrinsicDerivedComparison Z A).obj K)) := by
  let R := ULift.{u + 1} A
  have : IsNoetherianRing R := isNoetherian_of_finite R R
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (Z ↘ Spec (.of k))
  have hcd (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R)) (q : ℕ)
      (hq : 2 * d < q) : IsZero ((DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) :=
    (Etale.isZero_rightDerived_lowerStar_of_two_mul_lt R isAddTorsion_of_finite
      (Z ↘ Spec (.of k)) (Y ↘ Spec (.of k)) p (comp_over p _) d hd F q hq).of_iso
        ((Etale.lowerStar (ModuleCat.{u + 1} R) p).homologyRightDerivedFunctorObjSingleFunctorIso
          F q)
  have hplus := hb.1
  obtain ⟨b, hb⟩ := hb.2
  have hproj : IsIso (properOriginEtaleProjection
      (RingHom.ulift.{u + 1, u + 1, u, u} φ) p K) :=
    reductionEtaleProjection_isIso _ p (2 * d) hcd K
      ⟨b, fun q hq ↦ (DerivedCategory.isLE_iff K b).mp hb q hq⟩
  let E : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R)) := ⟨K, hplus⟩
  let U := (scalarMateRestriction φ Y).mapDerivedCategory
  have hs := etaleOriginScalarProjectionSquare φ p E hH
  have hm := isIso_of_pasted_square _ _ _ _ _ _ _ hs
  have := hm
  have : U.ReflectsIsomorphisms := scalarMateRestriction_reflectsIso φ Y
  exact isIso_of_reflects_iso _ U

set_option maxHeartbeats 800000 in
-- The finite-window and realization transports involve large derived-functor types.
/-- The specified compact-support scalar comparison is invertible, with both endpoints
in the full bounded constructible finite-Tor subcategory. Naturality is already part
of `reductionDirectImageComparison`, a natural transformation on the ambient categories.
Source: latest blueprint, `sk-lem-sp-reduction-direct-image.md`, first assertion
(blueprint: det-sp-reduction-direct-image).

Proof: transport intrinsic constructibility, boundedness and Tor amplitude through
finite-coefficient realization using lem-weil-pbc-finite-ring-constructible-derived-origin
and lem-exc-intrinsic-tor-amplitude-transport. The supported etale tensor-origin lemma
lem-sp-supported-etale-tensor-origin supplies bounded etale inputs for j_!M and its
scalar tensor. Choose a dimension bound by lem-kun-dimension-finite-type and the uniform
torsion cohomological bound lem-kun-0f10. Resolve B by finite free A-modules, allowing
an infinite left tail. The finite-window argument lem-sf-projection-finite-constant
makes the projection map invertible: in each total degree only finitely many free
terms contribute. The normalization lem-fix-etale-origin-scalar-projection-square
identifies this with the restriction of the specified B-linear proper mate.
Restriction reflects isomorphisms by lem-weil-pbc-ring-sheaf-change-adjunction.
Transport along the canonical etale/pro-etale comparison and compose with the proper
image of reductionOpenScalarIso, exactly def-sp-reduction-direct-image-comparison.
Finally sk-prop-sf-rf-shriek-preservation and lem-finite-compact-support-scalar-transport
transport compact-support preservation to reductionCompactSupport. Scalar preservation
from det-sp-scalar-extension-functor gives the three membership conditions for each
endpoint. This uses finite cohomological dimension over the stated base fields and
does not assume positive characteristic or finite projective dimension of B. -/
theorem reductionDirectImage_finiteCoefficients_isIso
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k) (hchar : ringChar k ≠ ℓ)
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (M : proEtaleDerivedCategory X A)
    (hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M)})
    (hconstructible : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M))
    (hTor : HasFiniteProEtaleTorAmplitude X A M) :
    IsIso ((reductionDirectImageComparison φ j p).app M) ∧
    (Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
        ((scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j p).obj M)))}) ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
          ((scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j p).obj M)))) ∧
    HasFiniteProEtaleTorAmplitude Y B
      ((scalarExtensionFunctor φ Y).obj ((reductionCompactSupport A j p).obj M)) ∧
    (Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
        ((reductionCompactSupport B j p).obj ((scalarExtensionFunctor φ X).obj M)))}) ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y B)) i).obj
          ((reductionCompactSupport B j p).obj ((scalarExtensionFunctor φ X).obj M)))) ∧
    HasFiniteProEtaleTorAmplitude Y B
      ((reductionCompactSupport B j p).obj ((scalarExtensionFunctor φ X).obj M)) := by
  have _ := hk
  have hM : ReductionGood X A M := ⟨hbounded, hconstructible, hTor⟩
  have hRf := reductionGood_compactSupport ℓ k hchar f j p hf A hA M hM
  have hsource := reductionGood_scalar ℓ hA hB φ Y _ hRf
  have hMB := reductionGood_scalar ℓ hA hB φ X M hM
  have htarget := reductionGood_compactSupport ℓ k hchar f j p hf B hB _ hMB
  have hiso : IsIso ((reductionDirectImageComparison φ j p).app M) := by
    let E := sfIntrinsicDerivedEquivalence X A
    let K := E.inverse.obj M
    have hK := reductionGood_iso (E.counitIso.app M).symm hM
    have hctf := (reductionGood_realization_iff X A K).mp hK
    have hc := ProEtale.DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic
      _ hctf.1
    have torsion {R : Type u} [CommRing R]
        (h : ∃ n : ℕ, ∀ x : R, (ℓ ^ n) • x = 0) : ∃ n : ℕ, (ℓ : R) ^ n = 0 := by
      obtain ⟨n, hn⟩ := h
      exact ⟨n, by simpa only [nsmul_eq_mul, mul_one, Nat.cast_pow] using hn 1⟩
    have hcf (i : ℤ) : IsConstructibleProEtaleFixedModuleSheaf X (ULift.{u + 1} A)
        ((DerivedCategory.homologyFunctor _ i).obj K) := by
      exact (fixed_constructible_iff _ X _).mpr (hc.2 i)
    obtain ⟨L, hL, hLc, e, hJ, hH, hJplus, hHplus, hex⟩ :=
      SupportedEtaleTensorOrigin.supported_etale_tensor_origin ℓ (Fact.out : ℓ.Prime)
        φ (torsion hA) (torsion hB) j K hc.1 hcf hK.2.2
    let ei : (finiteCoefficientIntrinsicDerivedComparison Z A).obj
          ((SupportedEtaleTensorOrigin.etaleOpen A j).obj L) ≅
        ((sfIntrinsicExtensionByZero j A).mapDerivedCategory).obj M :=
      (FiniteCompactScalar.intrinsicSiteFunctorIso A Z).app _ ≪≫
      (sfIntrinsicDerivedEquivalence Z A).functor.mapIso
        (SupportedEtaleTensorOrigin.supportedComparison A j L K e) ≪≫
      (SupportedEtaleTensorOrigin.openPresentation A j).symm.app K ≪≫
      ((sfIntrinsicExtensionByZero j A).mapDerivedCategory).mapIso (E.counitIso.app M)
    have hi := reductionProper_isIso φ k p
      ((SupportedEtaleTensorOrigin.etaleOpen A j).obj L) hJ hH.1
    have : IsIso ((directImageScalarComparison φ p).app
        (((sfIntrinsicExtensionByZero j A).mapDerivedCategory).obj M)) :=
      (NatTrans.isIso_app_iff_of_iso (directImageScalarComparison φ p) ei).mp hi
    dsimp only [reductionDirectImageComparison, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  exact ⟨hiso, hsource.1, hsource.2.1, hsource.2.2,
    htarget.1, htarget.2.1, htarget.2.2⟩

set_option maxHeartbeats 800000 in
-- Elaborate the composite derived-functor types before the categorical pasting.
end AlgebraicGeometry.ProEtale
