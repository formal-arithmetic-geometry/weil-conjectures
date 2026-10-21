/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.SixFunctors.FrobeniusPointCoefficientPassage
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.RingTheory.Localization.BaseChange
import Sheaf.Paper.IsomorphismComparisonNatural

/-!
# Naturality of Frobenius point transport

Source: Deligne, *La conjecture de Weil II*, (1.1.7), pp. 150--151
(blueprint: lem-weil-frobenius-point-transport-natural).

The two sigma maps are linear and natural on the finite and completed integral
complex models used by `frobeniusPointFiniteSigma` and
`frobeniusPointIntegralSigma`, and they descend to natural transformations
`Γ(s, -) → Γ(s, g_s⁻¹ -)` on the derived categories (`frobeniusPointFiniteSigmaDerived`,
`frobeniusPointIntegralSigmaDerived`).  The point-transport components are natural
on the finite and integral constructible categories.  Rational components are obtained
by the recorded scalar-localization construction, and algebraically closed
components are represented at a finite coefficient stage; the final clauses
state the corresponding naturality and scalar-extension compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option linter.defProp false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local irreducible] constantSheaf completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard sfIntrinsicPullback



/-- The canonical object equality identifying rational pullback with the integral model.
Source: blueprint rational pullback object formula in
`def-weil-frobenius-point-transport`; proof postponed to the uniqueness theorem
for `rationalDerivedPullback`.
-/
theorem frobeniusPointRationalPullbackEq
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (N : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
      fun x => frobeniusPointPrimeInvertible D l hl x
    (rationalDerivedPullback l E (frobeniusPointIso D).hom).obj N =
      frobeniusPointRationalPullbackObj D l hl E N := by
  letI := frobeniusPointPrimeInvertible D l hl
  exact (rationalDerivedPullback_existsUnique l E
    (frobeniusPointIso D).hom).exists.choose_spec.2.1 N

/-- The canonical common-stage object equality for qbar pullback.
Source: blueprint common-stage pullback paragraph; proof postponed to the
specified common-stage uniqueness property.
-/
theorem frobeniusPointQbarPullbackEq
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω]
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
      fun x => frobeniusPointPrimeInvertible D l hl x
    (commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).obj A =
      frobeniusPointQbarPullbackObj D l hl Ω A := by
  letI := frobeniusPointPrimeInvertible D l hl
  refine ((commonStageDerivedPullback_existsUnique l Ω
    (frobeniusPointIso D).hom).exists.choose_spec.1 A).trans ?_
  unfold commonStagePullbackObject frobeniusPointQbarPullbackObj
  congr 1
  exact frobeniusPointRationalPullbackEq D l hl _ A.obj

/-- The canonical object equality for the chosen qbar fibre functor.
Source: blueprint algebraically closed coefficient fibre construction; proof
postponed to `pointQbarFibre_existsUnique`.
-/
theorem frobeniusPointQbarFibreObjEq
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω]
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    (pointQbarFibre D l hl Ω).obj A = pointQbarFibreObj D l hl Ω A := by
  exact (pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.1 A

/-- The derived finite sigma component `Γ(s, N) → Γ(s, g_s⁻¹ N)` on the unbounded
derived category, for the exact module inverse image `inverseImageFiniteDerived`
(no pullback comparison `κ`): conjugate the chain-level `frobeniusPointFiniteSigma`
of the localization's representative by the recorded factorization isomorphisms.
Source: Deligne, *La conjecture de Weil II*, (1.1.7), pp. 150--151; clause 1 of
(blueprint: lem-weil-frobenius-point-transport-natural). -/
noncomputable def frobeniusPointFiniteSigmaDerived
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (N : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))) :
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj N ⟶
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
        ((inverseImageFiniteDerived l E (frobeniusPointIso D).hom n).obj N) :=
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
      (DerivedCategory.Q.objObjPreimageIso N).inv ≫
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors.hom.app
      (DerivedCategory.Q.objPreimage N) ≫
    DerivedCategory.Q.map
      (frobeniusPointFiniteSigma D l E n (DerivedCategory.Q.objPreimage N)) ≫
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors.inv.app
      (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
        (.up ℤ)).obj (DerivedCategory.Q.objPreimage N)) ≫
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
      ((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapDerivedCategoryFactors.inv.app
          (DerivedCategory.Q.objPreimage N) ≫
        (inverseImageFiniteDerived l E (frobeniusPointIso D).hom n).map
          (DerivedCategory.Q.objObjPreimageIso N).hom)

/-- The derived completed-integral sigma component `Γ(s, N) → Γ(s, g_s⁻¹ N)` on the
whole derived category, for the exact module inverse image
`inverseImageIntegralDerived` (no pullback comparison `κ`): conjugate the chain-level
`frobeniusPointIntegralSigma` of the localization's representative by the recorded
factorization isomorphisms.
Source: Deligne, *La conjecture de Weil II*, (1.1.7), pp. 150--151; clause 1 of
(blueprint: lem-weil-frobenius-point-transport-natural). -/
noncomputable def frobeniusPointIntegralSigmaDerived
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :
    (pointFibreIntegralAmbient D l E).obj N ⟶
      (pointFibreIntegralAmbient D l E).obj
        ((inverseImageIntegralDerived l E (frobeniusPointIso D).hom).obj N) :=
  (pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.objObjPreimageIso N).inv ≫
    (pointIntegralSections l E D.k).mapDerivedCategoryFactors.hom.app
      (DerivedCategory.Q.objPreimage N) ≫
    DerivedCategory.Q.map
      (frobeniusPointIntegralSigma D l E (DerivedCategory.Q.objPreimage N)) ≫
    (pointIntegralSections l E D.k).mapDerivedCategoryFactors.inv.app
      (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
        (.up ℤ)).obj (DerivedCategory.Q.objPreimage N)) ≫
    (pointFibreIntegralAmbient D l E).map
      ((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapDerivedCategoryFactors.inv.app
          (DerivedCategory.Q.objPreimage N) ≫
        (inverseImageIntegralDerived l E (frobeniusPointIso D).hom).map
          (DerivedCategory.Q.objObjPreimageIso N).hom)

private def reobject
    {C T : Type*} [Category* C] [Category* T] (F : C ⥤ T)
    (obj : C → T) (h : ∀ X, F.obj X = obj X) : C ⥤ T where
  obj := obj
  map {X Y} f := eqToHom (h X).symm ≫ F.map f ≫ eqToHom (h Y)
  map_id X := by simp
  map_comp f g := by simp [Category.assoc]

private theorem raw_localization_natural
    {R C T : Type*} [CommRing R] [Category* C] [Preadditive C] [Linear R C]
    [Category* T] (p : R) (F G : ScalarLocalization R C p ⥤ T)
    (τ : ∀ K, F.obj K ⟶ G.obj K)
    (hτ : ∀ (K M : C) (f : K ⟶ M),
      F.map ((ScalarLocalization.localization R C p).map f) ≫ τ ⟨M⟩ =
        τ ⟨K⟩ ≫ G.map ((ScalarLocalization.localization R C p).map f))
    {K M : ScalarLocalization R C p} (f : K ⟶ M) :
    F.map f ≫ τ M = τ K ≫ G.map f := by
  rcases K with ⟨K⟩
  rcases M with ⟨M⟩
  let Q := ScalarLocalization.localization R C p
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers p)
    (TensorProduct.mk R (Localization.Away p) (K ⟶ M) 1) f
  let d : K ⟶ K := (s : R) • 𝟙 K
  have hd : Q.map d ≫ f = Q.map a := by
    have hd₀ : Q.map d = (s : R) • 𝟙 (Q.obj K) := by
      change (1 : Localization.Away p) ⊗ₜ[R] ((s : R) • 𝟙 K) = _
      exact TensorProduct.tmul_smul _ _ _
    rw [hd₀, Linear.smul_comp, Category.id_comp]
    exact hs
  have hu := IsLocalization.map_units (Localization.Away p) s
  have hd' : Q.map d = algebraMap R (Localization.Away p) (s : R) • 𝟙 (Q.obj K) := by
    change (1 : Localization.Away p) ⊗ₜ[R] ((s : R) • 𝟙 K) = _
    rw [TensorProduct.tmul_smul]
    exact (algebraMap_smul (Localization.Away p) (s : R) _).symm
  have hi : IsIso (Q.map d) := by
    rw [hd', ← hu.unit_spec]
    refine ⟨⟨(↑(hu.unit⁻¹) : Localization.Away p) • 𝟙 (Q.obj K), ?_, ?_⟩⟩
    all_goals simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
      smul_smul, Units.inv_mul, Units.mul_inv, one_smul]
  apply (cancel_epi (F.map (Q.map d))).1
  calc
    _ = F.map (Q.map a) ≫ τ ⟨M⟩ := by rw [← Category.assoc, ← F.map_comp, hd]
    _ = τ ⟨K⟩ ≫ G.map (Q.map a) := hτ K M a
    _ = F.map (Q.map d) ≫ τ ⟨K⟩ ≫ G.map f := by
      rw [← Category.assoc, hτ K K d, Category.assoc, ← G.map_comp, hd]

private theorem conjugate_component
    {C T : Type*} [Category* C] [Category* T]
    {F H : C ⥤ T} (τ : F ⟶ H) {X Y : C} (e : X ≅ Y) :
    F.map e.inv ≫ τ.app X ≫ H.map e.hom = τ.app Y := by
  rw [← Category.assoc, τ.naturality, Category.assoc, ← H.map_comp,
    e.inv_hom_id, H.map_id, Category.comp_id]

private theorem localized_component
    {C B T : Type*} [Category* C] [Category* B] [Category* T]
    (L : C ⥤ B) (W : MorphismProperty C) [L.IsLocalization W]
    (F H : B ⥤ T) (F₀ H₀ : C ⥤ T)
    (eF : L ⋙ F ≅ F₀) (eH : L ⋙ H ≅ H₀) (τ : F₀ ⟶ H₀) :
    ∃ η : F ⟶ H, ∀ (X : C) (Y : B) (e : L.obj X ≅ Y),
      F.map e.inv ≫ eF.hom.app X ≫ τ.app X ≫ eH.inv.app X ≫ H.map e.hom =
        η.app Y := by
  let ff := Localization.fullyFaithfulWhiskeringLeft L W T
  let η := ff.preimage (eF.hom ≫ τ ≫ eH.inv)
  have h (X : C) : η.app (L.obj X) = eF.hom.app X ≫ τ.app X ≫ eH.inv.app X :=
    congr_app (ff.map_preimage (eF.hom ≫ τ ≫ eH.inv)) X
  refine ⟨η, ?_⟩
  intro X Y e
  simpa only [h, Category.assoc] using conjugate_component η e

private theorem derived_sigma
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (S : A ⥤ B) (I : A ⥤ A) [S.Additive] [I.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (σ : S.mapHomologicalComplex (.up ℤ) ⟶
      I.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ)) :
    ∃ η : S.mapDerivedCategory ⟶ I.mapDerivedCategory ⋙ S.mapDerivedCategory,
      ∀ (K : CochainComplex A ℤ) (N : DerivedCategory A) (e : DerivedCategory.Q.obj K ≅ N),
        S.mapDerivedCategory.map e.inv ≫
          S.mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map (σ.app K) ≫
          S.mapDerivedCategoryFactors.inv.app
            ((I.mapHomologicalComplex (.up ℤ)).obj K) ≫
          S.mapDerivedCategory.map
            (I.mapDerivedCategoryFactors.inv.app K ≫
              I.mapDerivedCategory.map e.hom) =
          η.app N := by
  let eH : DerivedCategory.Q ⋙ (I.mapDerivedCategory ⋙ S.mapDerivedCategory) ≅
      (I.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight I.mapDerivedCategoryFactors S.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ S.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm
  obtain ⟨η, hη⟩ := localized_component DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) S.mapDerivedCategory
    (I.mapDerivedCategory ⋙ S.mapDerivedCategory) _ _ S.mapDerivedCategoryFactors eH
    (Functor.whiskerRight σ DerivedCategory.Q)
  refine ⟨η, ?_⟩
  intro K N e
  simpa only [eH, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Iso.symm_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Category.id_comp, Category.comp_id, Functor.map_comp,
    Category.assoc] using hη K N e

private theorem derived_sigma_comparison
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (S : A ⥤ B) (I : A ⥤ A)
    [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (P : DerivedCategory A ⥤ DerivedCategory A)
    (τ : S.mapHomologicalComplex (.up ℤ) ⟶
      I.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ))
    (κ : I.mapDerivedCategory ⟶ P) :
    ∃ η : S.mapDerivedCategory ⟶ P ⋙ S.mapDerivedCategory,
      ∀ (K : CochainComplex A ℤ) (N : DerivedCategory A) (e : DerivedCategory.Q.obj K ≅ N),
      S.mapDerivedCategory.map e.inv ≫ S.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map (τ.app K) ≫
        S.mapDerivedCategoryFactors.inv.app ((I.mapHomologicalComplex (.up ℤ)).obj K) ≫
        S.mapDerivedCategory.map
          (I.mapDerivedCategoryFactors.inv.app K ≫ κ.app (DerivedCategory.Q.obj K)) ≫
        S.mapDerivedCategory.map (P.map e.hom) = η.app N := by
  obtain ⟨σ, hσ⟩ := derived_sigma S I τ
  let η := σ ≫ Functor.whiskerRight κ S.mapDerivedCategory
  refine ⟨η, ?_⟩
  intro K N e
  refine Eq.trans ?_ (conjugate_component η e)
  dsimp only [η, NatTrans.comp_app, Functor.whiskerRight_app, Functor.comp_map]
  rw [← hσ K (DerivedCategory.Q.obj K) (Iso.refl _)]
  simp [Functor.map_comp, Category.assoc]

private theorem restriction_complex_natural
    {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (c : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj R ⟶ R) [IsIso c]
    (A : Type (u + 1)) [Ring A]
    (a : A →+* R.obj.obj (op (ProEt.mk (𝟙 X))))
    (r : (proEtaleIsoPostcompose g).obj (ProEt.mk (𝟙 X)) ⟶ ProEt.mk (𝟙 X))
    (τ : ∀ K : CochainComplex (SheafOfModules.{u + 1} R) ℤ,
      (((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj
        (op (ProEt.mk (𝟙 X)))) ⋙ ModuleCat.restrictScalars a).mapHomologicalComplex
          (.up ℤ)).obj K ⟶
      (((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj
        (op (ProEt.mk (𝟙 X)))) ⋙ ModuleCat.restrictScalars a).mapHomologicalComplex
          (.up ℤ)).obj
        (((isoSectionwiseModuleInverseImage.{u, u} g c).mapHomologicalComplex (.up ℤ)).obj K))
    (hτ : ∀ K i x, (τ K).f i x = (K.X i).val.map r.op x)
    {K L : CochainComplex (SheafOfModules.{u + 1} R) ℤ} (f : K ⟶ L) :
    (((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj
      (op (ProEt.mk (𝟙 X)))) ⋙ ModuleCat.restrictScalars a).mapHomologicalComplex
        (.up ℤ)).map f ≫ τ L =
    τ K ≫ (((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj
      (op (ProEt.mk (𝟙 X)))) ⋙ ModuleCat.restrictScalars a).mapHomologicalComplex
        (.up ℤ)).map
      (((isoSectionwiseModuleInverseImage.{u, u} g c).mapHomologicalComplex (.up ℤ)).map f) := by
  ext i x
  exact (hτ L i ((f.f i).val.app _ x)).trans
    ((PresheafOfModules.naturality_apply (f.f i).val r.op x).symm.trans
      (congrArg ((f.f i).val.app _) (hτ K i x).symm))

private theorem finite_sigma_natural
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ)
    {K K' : CochainComplex
      (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ}
    (f : K ⟶ K') :
    ((pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
        (.up ℤ)).map f ≫ frobeniusPointFiniteSigma D l E n K' =
      frobeniusPointFiniteSigma D l E n K ≫
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
            (.up ℤ)).map
          (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
            (.up ℤ)).map f) := by
  exact restriction_complex_natural (frobeniusPointIso D).hom _
    (inverseImageFiniteCoefficientMap l E (frobeniusPointIso D).hom n) _
    (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (frobeniusPointRestriction D)
    (frobeniusPointFiniteSigma D l E n) (fun K ↦ (Classical.choose_spec
      (frobeniusPointFiniteSigma_existsUnique D l E n K)).1) f

private theorem integral_sigma_natural
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {K K' : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ}
    (f : K ⟶ K') :
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map f ≫
        frobeniusPointIntegralSigma D l E K' =
      frobeniusPointIntegralSigma D l E K ≫
        ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
            (.up ℤ)).map f) := by
  exact restriction_complex_natural (frobeniusPointIso D).hom _
    (inverseImageCompletedCoefficientMap l E (frobeniusPointIso D).hom) _
    (pointIntegralSectionMap l E D.k) (frobeniusPointRestriction D)
    (frobeniusPointIntegralSigma D l E) (fun K ↦ (Classical.choose_spec
      (frobeniusPointIntegralSigma_existsUnique D l E K)).1) f

private theorem finite_transport_transformation
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    ∃ η : (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory ⟶
        finiteDerivedPullback l E n (frobeniusPointIso D).hom ⋙
          (pointFiniteSections D.k
            (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory,
      ∀ N, frobeniusPointTransportFinite D l hl E n N = η.app N := by
  let S := pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))
  let I := inverseImageFiniteModules l E (frobeniusPointIso D).hom n
  let σ₀ : S.mapHomologicalComplex (.up ℤ) ⟶
      I.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ) :=
    { app := frobeniusPointFiniteSigma D l E n
      naturality := fun _ _ f ↦ finite_sigma_natural D l E n f }
  obtain ⟨κ, hκ, _⟩ := inverseImagePullbackComparisonFinite_natural.{u, u, u, u} l E
    (frobeniusPointIso D).hom (frobeniusPointPrimeUnit D l hl)
    (frobeniusPointPrimeUnit D l hl) n
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  let e₀ : integralOperationsLevelPullback l E (frobeniusPointIso D).hom n ≅
      sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1))
        (frobeniusPointIso D).hom :=
    inverseImageFiniteIntrinsicPullbackComparison (frobeniusPointIso D).hom
      (Padic.coefficientExtensionRing l E (n + 1))
  have := integralOperationsLevelPullback_additive l E (frobeniusPointIso D).hom n
  let e := Functor.mapDerivedCategoryNatIso e₀
  let κ' := κ ≫ e.hom
  obtain ⟨η, hη⟩ := derived_sigma_comparison S I
    (finiteDerivedPullback l E n (frobeniusPointIso D).hom) σ₀ κ'
  refine ⟨η, ?_⟩
  intro N
  simpa only [frobeniusPointTransportFinite, frobeniusPointTransportFiniteComplex,
    inverseImagePullbackComparisonFiniteIntrinsic, S, I, σ₀, κ',
    NatTrans.comp_app, hκ, e, e₀, Category.assoc] using
      hη (DerivedCategory.Q.objPreimage N) N (DerivedCategory.Q.objObjPreimageIso N)

private theorem integral_transport_transformation
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ η : pointFibreIntegralAmbient D l E ⟶
        integralDerivedPullback l E (frobeniusPointIso D).hom ⋙ pointFibreIntegralAmbient D l E,
      ∀ N, frobeniusPointTransportIntegral D l hl E N = η.app N := by
  let S := pointIntegralSections l E D.k
  let I := inverseImageIntegralModules l E (frobeniusPointIso D).hom
  let σ₀ : S.mapHomologicalComplex (.up ℤ) ⟶
      I.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ) :=
    { app := frobeniusPointIntegralSigma D l E
      naturality := fun _ _ f ↦ integral_sigma_natural D l E f }
  obtain ⟨σ, hσ⟩ := derived_sigma S I σ₀
  obtain ⟨κ, _, hκ, _⟩ := inverseImagePullbackComparisonIntegral_natural.{u, u, u, u} l E
    (frobeniusPointIso D).hom (frobeniusPointPrimeUnit D l hl)
    (frobeniusPointPrimeUnit D l hl)
  let η := σ ≫ Functor.whiskerRight κ S.mapDerivedCategory
  refine ⟨η, ?_⟩
  intro N
  unfold frobeniusPointTransportIntegral
  apply (frobeniusPointTransportIntegral_existsUnique D l hl E N).unique
    (Classical.choose_spec (frobeniusPointTransportIntegral_existsUnique D l hl E N)).1
  intro K P q hq ε
  rw [← conjugate_component η ε]
  dsimp only [η, NatTrans.comp_app, Functor.whiskerRight_app]
  rw [← hσ K (DerivedCategory.Q.obj K) (Iso.refl _)]
  simp only [Iso.refl_inv, Iso.refl_hom, Functor.comp_map]
  rw [hκ K P q]
  dsimp only [S, I, σ₀]
  simp only [frobeniusPointTransportIntegralComplex,
    pointFibreIntegralAmbient, Functor.map_comp, Category.assoc]
  simp

private theorem rational_fibre_integral_map
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {K M : sfIntegralConstructibleCategory l E (Spec (.of D.k))} (f : K ⟶ M) :
    (pointRationalFibre D l hl E).map
        ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).map f) ≫
        (pointRationalFibreObjIso D l hl E ⟨M⟩).hom =
      (pointRationalFibreObjIso D l hl E ⟨K⟩).hom ≫
        (pointIntegralRationalFibre D l hl E).map f := by
  apply ObjectProperty.hom_ext
  let eK := (pointRationalFibre_existsUnique D l hl E).exists.choose_spec.1 ⟨K⟩
  let eM := (pointRationalFibre_existsUnique D l hl E).exists.choose_spec.1 ⟨M⟩
  have he := (pointRationalFibre_existsUnique D l hl E).exists.choose_spec.2 K M f 1
  simp only [map_one, one_smul] at he
  have hh := (conj_eqToHom_iff_heq _ _
    (congrArg (fun X ↦ X.obj) eK)
    (congrArg (fun X ↦ X.obj) eM)).2 he
  change ((pointRationalFibre D l hl E).map
      ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).map f)).hom = _ at hh
  change _ ≫ ((DerivedCategory.pointFiniteDimensional E).ι.map (eqToHom eM)) =
    ((DerivedCategory.pointFiniteDimensional E).ι.map (eqToHom eK)) ≫ _
  rw [eqToHom_map, eqToHom_map, hh]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

private theorem rational_integral_component_natural
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {K M : sfIntegralConstructibleCategory l E (Spec (.of D.k))} (f : K ⟶ M) :
    let J := pointIntegralRationalFibre D l hl E
    let P := frobeniusPointIntegralPullback D l hl E
    let c := fun K : sfIntegralConstructibleCategory l E (Spec (.of D.k)) ↦
      (pointFibreSizeDescent E).map
        (ObjectProperty.homMk
          ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            (pointIntegralToField l E)).mapDerivedCategory.map
            (frobeniusPointTransportIntegral D l hl E K.obj)) :
          pointFibreRationalLarge D l hl E K ⟶ pointFibreRationalLarge D l hl E (P.obj K))
    J.map f ≫ c M = c K ≫ J.map (P.map f) := by
  dsimp only
  change (pointFibreSizeDescent E).map _ ≫ _ = _ ≫ (pointFibreSizeDescent E).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply ObjectProperty.hom_ext
  change (pointFibreRationalAmbient D l E).map f.hom ≫ _ =
    _ ≫ (pointFibreRationalAmbient D l E).map
      ((integralDerivedPullback l E (frobeniusPointIso D).hom).map f.hom)
  obtain ⟨η, hη⟩ := integral_transport_transformation D l hl E
  change (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)).mapDerivedCategory.map
      ((pointFibreIntegralAmbient D l E).map f.hom) ≫
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)).mapDerivedCategory.map
      (frobeniusPointTransportIntegral D l hl E M.obj) = _
  rw [hη M.obj, hη K.obj]
  exact (Functor.whiskerRight η
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)).mapDerivedCategory).naturality f.hom

private theorem conjugate_square
    {T : Type*} [Category* T] {X₁ X₂ Y₁ Y₂ A₁ A₂ B₁ B₂ : T}
    (e₁ : X₁ ≅ A₁) (e₂ : X₂ ≅ A₂) (d₁ : Y₁ ≅ B₁) (d₂ : Y₂ ≅ B₂)
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂)
    (c₁ : A₁ ⟶ B₁) (c₂ : A₂ ⟶ B₂)
    (hf : f ≫ e₂.hom = e₁.hom ≫ a) (hg : g ≫ d₂.hom = d₁.hom ≫ b)
    (hc : a ≫ c₂ = c₁ ≫ b) :
    f ≫ (e₂.hom ≫ c₂ ≫ d₂.inv) = (e₁.hom ≫ c₁ ≫ d₁.inv) ≫ g := by
  apply (cancel_mono d₂.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hg, d₁.inv_hom_id_assoc, ← Category.assoc, hf, Category.assoc, hc]

private theorem rational_transport_natural
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {N M : sfRationalConstructibleCategory l E (Spec (.of D.k))} (f : N ⟶ M) :
    letI := frobeniusPointPrimeInvertible D l hl
    (pointRationalFibre D l hl E).map f ≫ frobeniusPointTransportRational D l hl E M =
      frobeniusPointTransportRational D l hl E N ≫
        (pointRationalFibre D l hl E).map
          (eqToHom (frobeniusPointRationalPullbackEq D l hl E N).symm ≫
            (rationalDerivedPullback l E (frobeniusPointIso D).hom).map f ≫
            eqToHom (frobeniusPointRationalPullbackEq D l hl E M)) := by
  letI := frobeniusPointPrimeInvertible D l hl
  let F := pointRationalFibre D l hl E
  let P := reobject (rationalDerivedPullback l E (frobeniusPointIso D).hom)
    (frobeniusPointRationalPullbackObj D l hl E) (frobeniusPointRationalPullbackEq D l hl E)
  apply raw_localization_natural (Padic.coefficientExtensionUniformizer l E) F (P ⋙ F)
    (frobeniusPointTransportRational D l hl E) ?_ f
  intro K L a
  let Q := sfRationalConstructibleLocalization l E (Spec (.of D.k))
  let J := pointIntegralRationalFibre D l hl E
  let Pi := frobeniusPointIntegralPullback D l hl E
  have hp : P.map (Q.map a) = Q.map (Pi.map a) := by
    have h := (rationalDerivedPullback_existsUnique l E
      (frobeniusPointIso D).hom).exists.choose_spec.2.2 K L a 1
    dsimp only [P, reobject]
    exact ((conj_eqToHom_iff_heq _ _
      (frobeniusPointRationalPullbackEq D l hl E ⟨K⟩).symm
      (frobeniusPointRationalPullbackEq D l hl E ⟨L⟩).symm).2 h.symm).symm
  change F.map (Q.map a) ≫ _ = _ ≫ F.map (P.map (Q.map a))
  rw [hp]
  exact conjugate_square
    (pointRationalFibreObjIso D l hl E (Q.obj K))
    (pointRationalFibreObjIso D l hl E (Q.obj L))
    (pointRationalFibreObjIso D l hl E (Q.obj (Pi.obj K)))
    (pointRationalFibreObjIso D l hl E (Q.obj (Pi.obj L)))
    (F.map (Q.map a)) (F.map (Q.map (Pi.map a)))
    (J.map a) (J.map (Pi.map a)) _ _
    (rational_fibre_integral_map D l hl E a)
    (rational_fibre_integral_map D l hl E (Pi.map a))
    (rational_integral_component_natural D l hl E a)

/--
The point transport along Frobenius is linear and natural.
Source: Deligne, *La conjecture de Weil II*, (1.1.7), pp. 150--151
(blueprint: lem-weil-frobenius-point-transport-natural).

Proof steps (postponed at stage 2):
1. Identify the distinguished comma-object coprojection with restriction along
   geometric Frobenius by the inverse-image evaluation isomorphism.
2. Check additivity and both coefficient actions on finite and completed integral
   sections, including the comparison `c_Λ`.
3. Check chain-map naturality of restriction and pass it through the sections and
   inverse-image functors.
4. Apply exactness of sections and of the module inverse image to descend that
   equality through the derived localization (the derived sigma components).
5. Compose the naturality square for `κ` with the square for `σ` at finite level.
6. Use the normalized completed pullback comparison to obtain the integral square.
7. Localize the integral square and use `rationalDerivedPullback`, with its
   canonical object equalities, for the rational square.
8. Represent every qbar morphism over a common finite stage and use
   `commonStageDerivedPullback`; canonical eqToHom maps identify all four fibre
   objects in the displayed square.
9. For every coefficient extension E' ⊂ L, use the fibre-level
   `pointRationalSectionsScalarExtensionIso` and the normalized
   `rationalPullbackScalarComparison` to identify scalar-extended transport with
   the L-stage map;
   coherence under a further extension makes the result independent of the stage.
-/
theorem frobeniusPointTransport_natural
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    (∀ (n : ℕ)
      (K : CochainComplex
        (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
      (i : ℤ)
      (a : ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1)))
      (x : ModuleCat.carrier
        ((((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
            (.up ℤ)).obj K).X i)),
      (ConcreteCategory.hom
        ((frobeniusPointFiniteSigma D l E n K).f i)) (a • x) =
        a • (ConcreteCategory.hom
          ((frobeniusPointFiniteSigma D l E n K).f i)) x) ∧
    (∀ (n : ℕ)
      (K K' : CochainComplex
        (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
      (f : K ⟶ K'),
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
          (.up ℤ)).map f ≫
          frobeniusPointFiniteSigma D l E n K' =
        frobeniusPointFiniteSigma D l E n K ≫
          ((pointFiniteSections D.k
            (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
              (.up ℤ)).map
            (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
              (.up ℤ)).map f)) ∧
    (∀ (n : ℕ)
      (K K' : CochainComplex
        (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
      (f : K ⟶ K'),
      DerivedCategory.Q.map
        (((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
            (.up ℤ)).map f ≫
          frobeniusPointFiniteSigma D l E n K') =
        DerivedCategory.Q.map
          (frobeniusPointFiniteSigma D l E n K ≫
            ((pointFiniteSections D.k
              (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
                (.up ℤ)).map
              (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
                (.up ℤ)).map f))) ∧
    (∀ (n : ℕ)
      (N M : proEtaleDerivedCategory (Spec (.of D.k))
        (Padic.coefficientExtensionRing l E (n + 1)))
      (f : N ⟶ M),
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map f ≫
        frobeniusPointFiniteSigmaDerived D l E n M =
      frobeniusPointFiniteSigmaDerived D l E n N ≫
        (pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
          ((inverseImageFiniteDerived l E (frobeniusPointIso D).hom n).map f)) ∧
    (∀ (K : CochainComplex
      (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (i : ℤ)
      (a : ULift.{u + 1, u}
        (Padic.coefficientExtensionIntegers l E))
      (x : ModuleCat.carrier
        ((((pointIntegralSections l E D.k).mapHomologicalComplex
            (.up ℤ)).obj K).X i)),
      (ConcreteCategory.hom
        ((frobeniusPointIntegralSigma D l E K).f i)) (a • x) =
        a • (ConcreteCategory.hom
          ((frobeniusPointIntegralSigma D l E K).f i)) x) ∧
    (∀ (K K' : CochainComplex
      (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (f : K ⟶ K'),
      ((pointIntegralSections l E D.k).mapHomologicalComplex
          (.up ℤ)).map f ≫ frobeniusPointIntegralSigma D l E K' =
        frobeniusPointIntegralSigma D l E K ≫
          ((pointIntegralSections l E D.k).mapHomologicalComplex
              (.up ℤ)).map
            (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
              (.up ℤ)).map f)) ∧
    (∀ (K K' : CochainComplex
      (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (f : K ⟶ K'),
      DerivedCategory.Q.map
        (((pointIntegralSections l E D.k).mapHomologicalComplex
          (.up ℤ)).map f ≫ frobeniusPointIntegralSigma D l E K') =
        DerivedCategory.Q.map
          (frobeniusPointIntegralSigma D l E K ≫
            ((pointIntegralSections l E D.k).mapHomologicalComplex
              (.up ℤ)).map
            (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
              (.up ℤ)).map f))) ∧
    (∀ (N M : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
      (f : N ⟶ M),
      (pointFibreIntegralAmbient D l E).map f ≫
        frobeniusPointIntegralSigmaDerived D l E M =
      frobeniusPointIntegralSigmaDerived D l E N ≫
        (pointFibreIntegralAmbient D l E).map
          ((inverseImageIntegralDerived l E (frobeniusPointIso D).hom).map f)) ∧
    (∀ (n : ℕ)
      (N M : (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n))
        (Spec (.of D.k))).FullSubcategory)
      (u : N ⟶ M),
      (pointFiniteFibre D l hl E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n))).map u ≫
          frobeniusPointTransportFiniteConstructible D l hl E n M =
        frobeniusPointTransportFiniteConstructible D l hl E n N ≫
          (pointFiniteFibre D l hl E (n + 1)
            (Nat.succ_le_succ (Nat.zero_le n))).map
            ((frobeniusPointFinitePullback D l hl E n).map u)) ∧
    (∀ (N M : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
      (u : N ⟶ M),
      (pointIntegralFibre D l hl E).map u ≫
          frobeniusPointTransportIntegralConstructible D l hl E M =
        frobeniusPointTransportIntegralConstructible D l hl E N ≫
          (pointIntegralFibre D l hl E).map
            ((frobeniusPointIntegralPullback D l hl E).map u)) ∧
    (∀ (N M : sfRationalConstructibleCategory l E (Spec (.of D.k)))
      (u : N ⟶ M),
      letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
        fun x => frobeniusPointPrimeInvertible D l hl x
      (pointRationalFibre D l hl E).map u ≫
          frobeniusPointTransportRational D l hl E M =
        frobeniusPointTransportRational D l hl E N ≫
          (pointRationalFibre D l hl E).map
            (eqToHom (frobeniusPointRationalPullbackEq D l hl E N).symm ≫
              (rationalDerivedPullback l E (frobeniusPointIso D).hom).map u ≫
              eqToHom (frobeniusPointRationalPullbackEq D l hl E M))) ∧
    (∀ (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
      [IsAlgClosure ℚ_[l] Ω]
      (A B : generalAlgebraicallyClosedConstructibleCategory l Ω
        (Spec (.of D.k)))
      (u : A ⟶ B),
      letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
        fun x => frobeniusPointPrimeInvertible D l hl x
      (eqToHom (frobeniusPointQbarFibreObjEq D l hl Ω A).symm ≫
          (pointQbarFibre D l hl Ω).map u ≫
          eqToHom (frobeniusPointQbarFibreObjEq D l hl Ω B)) ≫
          frobeniusPointTransportQbar D l hl Ω B =
        frobeniusPointTransportQbar D l hl Ω A ≫
          (eqToHom (congrArg (pointQbarFibreObj D l hl Ω)
              (frobeniusPointQbarPullbackEq D l hl Ω A).symm) ≫
            eqToHom (frobeniusPointQbarFibreObjEq D l hl Ω
              ((commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).obj A)).symm ≫
            (pointQbarFibre D l hl Ω).map
              ((commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).map u) ≫
            eqToHom (frobeniusPointQbarFibreObjEq D l hl Ω
              ((commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).obj B)) ≫
            eqToHom (congrArg (pointQbarFibreObj D l hl Ω)
              (frobeniusPointQbarPullbackEq D l hl Ω B)))) ∧
    (∀ (E' L : Type u) [Field E'] [Algebra ℚ_[l] E']
      [FiniteDimensional ℚ_[l] E'] [Field L] [Algebra ℚ_[l] L]
      [FiniteDimensional ℚ_[l] L] (ι : E' →ₐ[ℚ_[l]] L)
      (K : sfRationalConstructibleCategory l E' (Spec (.of D.k))),
      letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
        fun x => frobeniusPointPrimeInvertible D l hl x
      (pointRationalFibreScalarIso D l hl E' L ι).inv.app K ≫
          frobeniusPointTransportRational D l hl L
            ((sfRationalScalarExtension l E' (Spec (.of D.k)) 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) ≫
          (pointRationalFibre D l hl L).map
            (eqToHom (frobeniusPointRationalPullbackEq D l hl L
              ((sfRationalScalarExtension l E' (Spec (.of D.k)) 0
                (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K)).symm) ≫
          (pointRationalFibre D l hl L).map
            ((rationalPullbackScalarComparison l E' L ι
              (frobeniusPointIso D).hom).inv.app K) ≫
          (pointRationalFibreScalarIso D l hl E' L ι).hom.app
            ((rationalDerivedPullback l E' (frobeniusPointIso D).hom).obj K) =
        (DerivedCategory.pointFdScalarExtension ι.toRingHom).map
          (frobeniusPointTransportRational D l hl E' K) ≫
          (DerivedCategory.pointFdScalarExtension ι.toRingHom).map
            ((pointRationalFibre D l hl E').map
              (eqToHom (frobeniusPointRationalPullbackEq D l hl E' K).symm))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n K i a x
    exact map_smul ((frobeniusPointFiniteSigma D l E n K).f i).hom a x
  · intro n K K' f
    exact finite_sigma_natural D l E n f
  · intro n K K' f
    exact congrArg DerivedCategory.Q.map (finite_sigma_natural D l E n f)
  · intro n N M f
    let σ : (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ) ⟶
        (inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
          (.up ℤ) ⋙ (pointFiniteSections D.k
            (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ) :=
      { app := frobeniusPointFiniteSigma D l E n
        naturality := fun _ _ f ↦ finite_sigma_natural D l E n f }
    obtain ⟨η, hη⟩ := derived_sigma
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
      (inverseImageFiniteModules l E (frobeniusPointIso D).hom n) σ
    change _ ≫ frobeniusPointFiniteSigmaDerived D l E n M =
      frobeniusPointFiniteSigmaDerived D l E n N ≫ _
    unfold frobeniusPointFiniteSigmaDerived
    rw [hη (DerivedCategory.Q.objPreimage M) M (DerivedCategory.Q.objObjPreimageIso M),
      hη (DerivedCategory.Q.objPreimage N) N (DerivedCategory.Q.objObjPreimageIso N)]
    exact η.naturality f
  · intro K i a x
    exact map_smul ((frobeniusPointIntegralSigma D l E K).f i).hom a x
  · intro K K' f
    exact integral_sigma_natural D l E f
  · intro K K' f
    exact congrArg DerivedCategory.Q.map (integral_sigma_natural D l E f)
  · intro N M f
    let σ : (pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ) ⟶
        (inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
          (.up ℤ) ⋙ (pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ) :=
      { app := frobeniusPointIntegralSigma D l E
        naturality := fun _ _ f ↦ integral_sigma_natural D l E f }
    obtain ⟨η, hη⟩ := derived_sigma (pointIntegralSections l E D.k)
      (inverseImageIntegralModules l E (frobeniusPointIso D).hom) σ
    unfold frobeniusPointIntegralSigmaDerived
    rw [hη (DerivedCategory.Q.objPreimage M) M (DerivedCategory.Q.objObjPreimageIso M),
      hη (DerivedCategory.Q.objPreimage N) N (DerivedCategory.Q.objObjPreimageIso N)]
    exact η.naturality f
  · intro n N M f
    apply ObjectProperty.hom_ext
    obtain ⟨η, hη⟩ := finite_transport_transformation D l hl E n
    change _ ≫ frobeniusPointTransportFinite D l hl E n M.obj =
      frobeniusPointTransportFinite D l hl E n N.obj ≫ _
    rw [hη M.obj, hη N.obj]
    exact η.naturality f.hom
  · intro N M f
    apply ObjectProperty.hom_ext
    obtain ⟨η, hη⟩ := integral_transport_transformation D l hl E
    change _ ≫ frobeniusPointTransportIntegral D l hl E M.obj =
      frobeniusPointTransportIntegral D l hl E N.obj ≫ _
    rw [hη M.obj, hη N.obj]
    exact η.naturality f.hom
  · intro N M f
    exact rational_transport_natural D l hl E f
  · exact (frobeniusPointTransport_coefficient_passage D l hl
      (frobeniusPointRationalPullbackEq D l hl) (frobeniusPointQbarPullbackEq D l hl)
      (frobeniusPointQbarFibreObjEq D l hl)).1
  · exact (frobeniusPointTransport_coefficient_passage D l hl
      (frobeniusPointRationalPullbackEq D l hl) (frobeniusPointQbarPullbackEq D l hl)
      (frobeniusPointQbarFibreObjEq D l hl)).2

end

end WeilConjectures
