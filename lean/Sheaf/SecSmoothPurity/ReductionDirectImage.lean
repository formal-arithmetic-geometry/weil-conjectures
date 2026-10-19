/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.Compactification.NagataCompactification

import Sheaf.SecSmoothPurity.DirectImageScalarCoefficientCocycle
import Sheaf.SecSmoothPurity.OpenScalarCoefficientCocycle
import Sheaf.SecSmoothPurity.ProperIntrinsicFiniteCoefficientExtension
import Sheaf.SecSmoothPurity.IntrinsicCoefficientSiteMate
import Sheaf.Paper.CompactSupportUniformTorBound
import Sheaf.Paper.EtaleProEtaleCoefficientTransport
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.GeometricFibreDimension
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.AlgebraicGeometry.InjectiveModuleDirectImageAcyclic
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero

/-!
# Compact support and finite coefficient extension

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-direct-image.md (blueprint: det-sp-reduction-direct-image).

The comparison uses the specified counit mate and the unit-normalized open tensor
comparison. All categories are ordinary uncompleted module derived categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem compactSupport_cocycle_of_factors
    {D₀ D₁ D₂ E₀ E₁ E₂ F₀ F₁ F₂ : Type*}
    [Category* D₀] [Category* D₁] [Category* D₂]
    [Category* E₀] [Category* E₁] [Category* E₂]
    [Category* F₀] [Category* F₁] [Category* F₂]
    (J₀ : D₀ ⥤ E₀) (J₁ : D₁ ⥤ E₁) (J₂ : D₂ ⥤ E₂)
    (R₀ : E₀ ⥤ F₀) (R₁ : E₁ ⥤ F₁) (R₂ : E₂ ⥤ F₂)
    (S₀₁ : D₀ ⥤ D₁) (S₁₂ : D₁ ⥤ D₂) (S₀₂ : D₀ ⥤ D₂)
    (T₀₁ : E₀ ⥤ E₁) (T₁₂ : E₁ ⥤ E₂) (T₀₂ : E₀ ⥤ E₂)
    (U₀₁ : F₀ ⥤ F₁) (U₁₂ : F₁ ⥤ F₂) (U₀₂ : F₀ ⥤ F₂)
    (αD : S₀₁ ⋙ S₁₂ ⟶ S₀₂) (αE : T₀₁ ⋙ T₁₂ ⟶ T₀₂)
    (αF : U₀₁ ⋙ U₁₂ ⟶ U₀₂)
    (e₀₁ : J₀ ⋙ T₀₁ ⟶ S₀₁ ⋙ J₁) (e₁₂ : J₁ ⋙ T₁₂ ⟶ S₁₂ ⋙ J₂)
    (e₀₂ : J₀ ⋙ T₀₂ ⟶ S₀₂ ⋙ J₂)
    (γ₀₁ : R₀ ⋙ U₀₁ ⟶ T₀₁ ⋙ R₁) (γ₁₂ : R₁ ⋙ U₁₂ ⟶ T₁₂ ⋙ R₂)
    (γ₀₂ : R₀ ⋙ U₀₂ ⟶ T₀₂ ⋙ R₂) (M : D₀)
    (hproper : αF.app (R₀.obj (J₀.obj M)) ≫ γ₀₂.app (J₀.obj M) =
      U₁₂.map (γ₀₁.app (J₀.obj M)) ≫ γ₁₂.app (T₀₁.obj (J₀.obj M)) ≫
        R₂.map (αE.app (J₀.obj M)))
    (hopen : αE.app (J₀.obj M) ≫ e₀₂.app M =
      T₁₂.map (e₀₁.app M) ≫ e₁₂.app (S₀₁.obj M) ≫ J₂.map (αD.app M)) :
    αF.app (R₀.obj (J₀.obj M)) ≫ (γ₀₂.app (J₀.obj M) ≫ R₂.map (e₀₂.app M)) =
      U₁₂.map (γ₀₁.app (J₀.obj M) ≫ R₁.map (e₀₁.app M)) ≫
        (γ₁₂.app (J₁.obj (S₀₁.obj M)) ≫ R₂.map (e₁₂.app (S₀₁.obj M))) ≫
          R₂.map (J₂.map (αD.app M)) := by
  rw [← Category.assoc, hproper]
  simp only [Functor.map_comp, Category.assoc]
  rw [← R₂.map_comp, hopen]
  simp only [Functor.map_comp]
  have hn := γ₁₂.naturality_assoc (e₀₁.app M)
    (R₂.map (e₁₂.app (S₀₁.obj M)) ≫ R₂.map (J₂.map (αD.app M)))
  simp only [Functor.comp_map] at hn
  exact congrArg (fun t ↦ U₁₂.map (γ₀₁.app (J₀.obj M)) ≫ t) hn.symm

private theorem tor_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : HasProEtaleTorAmplitude T A K a b) : HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private noncomputable def open_coordinates (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    proEtaleRingDerivedOpenExtension j (proEtaleConstantRing Z A)
        (proEtaleConstantRing X A) (proEtaleConstantRingComparison j A) ≅
      sfIntrinsicDerivedOpen A j := by
  let a := Adjunction.ofIsRightAdjoint (proEtaleConstantRingPullback A j)
  let b := (sfIntrinsicOpenAdjunction A j).ofNatIsoRight
    (openSquarePullbackModel A j).symm
  exact Functor.mapDerivedCategoryNatIso (a.leftAdjointUniq b)


private theorem intrinsicConstructible_of_iso (X : Scheme.{u})
    (B : Type u) [CommRing B] [Finite B]
    {M N : proEtaleRingModules X (proEtaleConstantRing X B)} (e : M ≅ N)
    (h : IsConstructibleProEtaleModuleSheaf X B M) :
    IsConstructibleProEtaleModuleSheaf X B N := by
  rw [proEtaleModuleRestriction_constructible_iff] at h ⊢
  exact ProEtale.isConstructible_of_iso ((proEtaleModuleRestriction X B).mapIso e) h

private theorem support_preserves
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
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
    {A : Type u} [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (M : proEtaleDerivedCategory X A) (hM : spFiniteConstructibleTor X A M) :
    spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M) := by
  have : Fact pchar.Prime := ⟨CharP.char_prime_of_ne_zero k (Nat.ne_of_gt hp)⟩
  have : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : QuasiCompact j := quasiCompact_of_compactSpace j
  let c : Compactification f := ⟨Z, p, j, hf.symm, inferInstance, inferInstance⟩
  have : LocallyOfFiniteType f := by
    rw [← hf]
    infer_instance
  have : QuasiCompact f := by
    rw [← hf]
    infer_instance
  have : IsSeparated f := by
    rw [← hf]
    infer_instance
  have : QuasiCompact c.i := inferInstance
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_pullback_le (Y ↘ Spec (.of k)) f
  obtain ⟨a, b, ht⟩ := hM.2.2
  have hAp : ∃ r : ℕ, 0 < r ∧ (ℓ : A) ^ r = 0 := by
    obtain ⟨r, hr⟩ := hA
    refine ⟨r + 1, by omega, ?_⟩
    have hz : (ℓ : A) ^ r = 0 := by simpa using hr 1
    rw [pow_succ, hz, zero_mul]
  have ho := (compactSupport_uniform_tor_bound pchar ℓ k hℓ.symm X Y f c d
    (fun y ↦ hd _ _) a b ht.1).1 A hAp M hM ht
  let e : proEtaleRingCompactSupportImage c
      (proEtaleConstantRing Y A) (proEtaleConstantRing Z A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison p A)
      (proEtaleConstantRingComparison j A) ≅ reductionCompactSupport A j p :=
    Functor.isoWhiskerRight (open_coordinates A j) (directImageConstantPush A p)
  let eM := e.app M
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a', b', hab, hv⟩ := ho.1.1
    exact ⟨a', b', hab, fun i hi ↦ (hv i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso eM.symm)⟩
  · intro i
    exact intrinsicConstructible_of_iso Y A
      ((DerivedCategory.homologyFunctor _ i).mapIso eM) (ho.1.2.1 i)
  · exact ⟨a, b + 2 * (d : ℤ), tor_of_iso Y A eM ho.2⟩


private theorem bounded_interval (T : Scheme.{u}) (A : Type u) [CommRing A]
    (M : proEtaleDerivedCategory T A)
    (h : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ i).obj M)}) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj M) := by
  classical
  obtain ⟨a, ha⟩ := h.bddBelow
  obtain ⟨b, hb⟩ := h.bddAbove
  refine ⟨min a b, b, min_le_right _ _, ?_⟩
  intro i hi
  by_contra hz
  have hia := ha hz
  have hib := hb hz
  rcases hi with hi | hi
  · exact (not_lt_of_ge (le_trans (min_le_left a b) hia)) hi
  · exact (not_lt_of_ge hib) hi

private theorem finite_support (T : Scheme.{u}) (A : Type u) [CommRing A]
    (M : proEtaleDerivedCategory T A)
    (h : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj M)) :
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ i).obj M)} := by
  obtain ⟨a, b, _, hv⟩ := h
  apply (Set.finite_Icc a b).subset
  intro i hi
  exact ⟨le_of_not_gt (fun hlt ↦ hi (hv i (.inl hlt))),
    le_of_not_gt (fun hlt ↦ hi (hv i (.inr hlt)))⟩

private theorem scalar_preserves
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (φ : A →+* B) (T : Scheme.{u}) (M : proEtaleDerivedCategory T A)
    (hM : spFiniteConstructibleTor T A M) :
    spFiniteConstructibleTor T B ((scalarExtensionFunctor φ T).obj M) := by
  obtain ⟨a, b, ht⟩ := hM.2.2
  obtain ⟨hb, hc, ht'⟩ := scalarExtensionFunctor_preserves_constructible_tor
    ℓ hA hB φ T M (finite_support T A M hM.1) hM.2.1 a b ht
  exact ⟨bounded_interval T B _ hb, hc, a, b, ht'⟩

/-- The canonical coefficient comparison is an isomorphism in the full subcategory
of bounded intrinsically constructible complexes of finite Tor amplitude. Membership
is written out for both endpoints, so no etale-origin hypothesis replaces intrinsic
constructibility. No flatness or finite-projective-dimension condition is imposed.
Source: blueprint main-20261015, sk-lem-sp-reduction-direct-image.md
(blueprint: det-sp-reduction-direct-image).

Proof:
1. Descend M to a bounded constructible etale complex L. Exact open extension
   gives J = j!L, and the normalized open comparison identifies its intrinsic
   etale-origin image with j!M. In particular J is bounded below.
2. Scalar extension preserves bounded constructibility and finite Tor amplitude
   of M. The open scalar isomorphism identifies the intrinsic origin of the actual
   scalar extension of J with j! of the scalar extension of M. Exact open extension
   and reflection of cohomological intervals by the finite-ring origin comparison
   therefore prove that this etale scalar extension of J is also bounded below.
3. Apply properIntrinsicFiniteCoefficientExtension to p and J. Its two lower bounds
   are those proved in steps 1 and 2. The theorem uses the existing ordinary etale
   proper coefficient theorem and intrinsicCoefficientSiteMate, the separate
   normalized coefficient/site coherence equality. Naturality transports its
   conclusion along the open-origin isomorphism to j!M. The compact-support map is
   the proper comparison followed by the direct image of the open scalar isomorphism,
   so it is invertible.
4. For all six endpoint membership claims, use scalar preservation and the intrinsic
   uniform compact-support Tor-bound theorem. A uniform geometric-fibre-dimension
   bound exists for the finite-type morphism over the field. The normalized open
   coordinate isomorphism identifies the raw compact-support functor with the
   recorded one; transport boundedness, constructibility and Tor amplitude along it.
-/
theorem reductionDirectImage_isIso
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
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
  have hM : spFiniteConstructibleTor X A M :=
    ⟨bounded_interval X A M hbounded, hconstructible, hTor⟩
  have hMB := scalar_preserves ℓ hA hB φ X M hM
  have hRM := support_preserves ℓ pchar hp hℓ k f j p hf hA M hM
  have hRMB := support_preserves ℓ pchar hp hℓ k f j p hf hB _ hMB
  have hQRM := scalar_preserves ℓ hA hB φ Y _ hRM
  refine ⟨?_, finite_support Y B _ hQRM.1, hQRM.2.1, hQRM.2.2,
    finite_support Y B _ hRMB.1, hRMB.2.1, hRMB.2.2⟩
  have : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of k))
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Z := ⟨⟩
  have : IsNoetherian Y := ⟨⟩
  obtain ⟨L, ⟨eL⟩⟩ := (finiteRing_constructibleDerived_origin X A).2.2.1 M |>.mpr
    ⟨hconstructible, hM.1⟩
  let J := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.obj L.obj
  let eM : (etaleOriginOpenComparison A X).obj L.obj ≅ M :=
    ((Functor.mapDerivedCategoryCompIso _ _).app L.obj).symm ≪≫ eL
  let eN : (etaleOriginOpenComparison A Z).obj J ≅
      (sfIntrinsicExtensionByZero j A).mapDerivedCategory.obj M :=
    (etaleOriginOpenExtensionComparison A j).app L.obj ≪≫
      (sfIntrinsicExtensionByZero j A).mapDerivedCategory.mapIso eM
  obtain ⟨aL, bL, _, hvL⟩ := L.property.2
  have hJ : ∃ n : ℤ, J.IsGE n := by
    refine ⟨aL, (DerivedCategory.isGE_iff J aL).mpr ?_⟩
    intro i hi
    exact (Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).isZero_homologyFunctor_mapDerivedCategory_obj
        (hvL i (.inl hi))
  obtain ⟨aMB, bMB, _, hvMB⟩ := hMB.1
  let JB := (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z).obj J
  let eQB : (finiteCoefficientIntrinsicDerivedComparison Z B).obj JB ≅
      (sfIntrinsicExtensionByZero j B).mapDerivedCategory.obj
        ((scalarExtensionFunctor φ X).obj M) :=
    (Functor.mapDerivedCategoryCompIso _ _).app JB ≪≫
      (intrinsicCoefficientSiteScalarIso φ Z).symm.app J ≪≫
      (scalarExtensionFunctor φ Z).mapIso eN ≪≫ (reductionOpenScalarIso φ j).app M
  have hvJB : ∀ i : ℤ, (i < aMB ∨ bMB < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj JB) := by
    apply ((finiteRing_constructibleDerived_origin Z B).2.2.2 JB aMB bMB).mpr
    intro i hi
    exact ((sfIntrinsicExtensionByZero j B).isZero_homologyFunctor_mapDerivedCategory_obj
      (hvMB i hi)).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eQB)
  have hJB : ∃ n : ℤ, JB.IsGE n :=
    ⟨aMB, (DerivedCategory.isGE_iff JB aMB).mpr (fun i hi ↦ hvJB i (.inl hi))⟩
  have hi := properIntrinsicFiniteCoefficientExtension φ p J hJ hJB
  have hproper : IsIso ((directImageScalarComparison φ p).app
      ((sfIntrinsicExtensionByZero j A).mapDerivedCategory.obj M)) :=
    (NatTrans.isIso_app_iff_of_iso (directImageScalarComparison φ p) eN).mp hi
  dsimp only [reductionDirectImageComparison, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app]
  infer_instance


end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] completedAdicDerivedChange completedAdicChange
  proEtaleRingModulePullback proEtaleRingModuleDirectImage

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false in
set_option maxHeartbeats 600000 in
-- Matching the concrete derived functor interfaces requires extra definitional equality work.
/-- The coefficient cocycle for these very comparisons, with both canonical alpha maps.
Source: blueprint statement's last equation and proof Steps 10-11
(blueprint: det-sp-reduction-direct-image).
Proof: transpose the two proper composites under the C-linear adjunction. Both become
extension of the A-counit by balanced tensor associativity. The injective adjunction
bijection identifies them. On the open, both maps restrict to the same balanced tensor
map ((m tensor b) tensor c) to m tensor psi(b)c. The unit of extension/restriction is
the identity, so its adjunction detects equality of these maps between extensions.
Expand b = Rp_*(e) gamma, use naturality of gamma at e, and substitute the two cocycles.
Naturality of the canonical alpha reinserts the two displayed associativity maps. -/
theorem reductionDirectImage_cocycle
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
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
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (hC : ∃ n : ℕ, ∀ x : C, (ℓ ^ n) • x = 0) (φ : A →+* B) (ψ : B →+* C)
    (M : proEtaleDerivedCategory X A)
    (hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M)})
    (hconstructible : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M))
    (hTor : HasFiniteProEtaleTorAmplitude X A M) :
    (scalarExtensionFunctor_composition φ ψ Y).hom.app
        ((reductionCompactSupport A j p).obj M) ≫
      (reductionDirectImageComparison (ψ.comp φ) j p).app M =
    (scalarExtensionFunctor ψ Y).map ((reductionDirectImageComparison φ j p).app M) ≫
      (reductionDirectImageComparison ψ j p).app ((scalarExtensionFunctor φ X).obj M) ≫
        (reductionCompactSupport C j p).map
          ((scalarExtensionFunctor_composition φ ψ X).hom.app M) := by
  dsimp only [reductionDirectImageComparison, reductionCompactSupport, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj, Functor.comp_map,
    scalarExtensionFunctor]
  let N := (sfIntrinsicExtensionByZero j A).mapDerivedCategory.obj M
  have hproper := directImageScalarCoefficientCocycle φ ψ p N
  have hopen := reductionOpenScalarCoefficientCocycle φ ψ j M
  dsimp only [scalarExtensionFunctor] at hproper hopen
  have result := compactSupport_cocycle_of_factors
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory
    (sfIntrinsicExtensionByZero j B).mapDerivedCategory
    (sfIntrinsicExtensionByZero j C).mapDerivedCategory
    (directImageConstantPush A p) (directImageConstantPush B p) (directImageConstantPush C p)
    (directImageScalarExtension φ X) (directImageScalarExtension ψ X)
    (directImageScalarExtension (ψ.comp φ) X)
    (directImageScalarExtension φ Z) (directImageScalarExtension ψ Z)
    (directImageScalarExtension (ψ.comp φ) Z)
    (directImageScalarExtension φ Y) (directImageScalarExtension ψ Y)
    (directImageScalarExtension (ψ.comp φ) Y)
    (scalarExtensionFunctor_composition φ ψ X).hom
    (scalarExtensionFunctor_composition φ ψ Z).hom
    (scalarExtensionFunctor_composition φ ψ Y).hom
    (reductionOpenScalarIso φ j).hom (reductionOpenScalarIso ψ j).hom
    (reductionOpenScalarIso (ψ.comp φ) j).hom
    (directImageScalarComparison φ p) (directImageScalarComparison ψ p)
    (directImageScalarComparison (ψ.comp φ) p) M hproper
    hopen
  exact result


end AlgebraicGeometry.ProEtale
