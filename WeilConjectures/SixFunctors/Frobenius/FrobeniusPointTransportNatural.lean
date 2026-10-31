/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Frobenius.FrobeniusPointTransport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonNatural
import WeilConjectures.SixFunctors.Frobenius.FrobeniusPointTransportRationalScalar
import WeilConjectures.SixFunctors.Frobenius.FrobeniusPointTransportQbarNaturalTransformation

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
set_option linter.style.haveILetI false
set_option linter.defProp false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
namespace WeilConjectures

attribute [local irreducible] frobeniusPointIso frobeniusPointRestriction

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
  letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
    fun x ↦ frobeniusPointPrimeInvertible D l hl x
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
  letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
    fun x ↦ frobeniusPointPrimeInvertible D l hl x
  refine ((commonStageDerivedPullback_existsUnique l Ω
    (frobeniusPointIso D).hom).exists.choose_spec.1 A).trans ?_
  change (⟨A.stage, (rationalDerivedPullback l _ (frobeniusPointIso D).hom).obj A.obj⟩ :
    generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) = _
  rw [frobeniusPointRationalPullbackEq D l hl]
  rfl

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
  (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
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
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
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

private theorem conjugate_component
    {C T : Type*} [Category C] [Category T] {F G : C ⥤ T}
    (τ : F ⟶ G) {X Y : C} (e : X ≅ Y) :
    τ.app Y = F.map e.inv ≫ τ.app X ≫ G.map e.hom := by
  apply (cancel_epi (F.map e.hom)).1
  simp only [← Category.assoc, ← F.map_comp, e.hom_inv_id, F.map_id, Category.id_comp]
  exact τ.naturality e.hom

attribute [local irreducible] constantSheaf completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard

private theorem localization_tensor_pure
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A] [AddCommGroup M] [Module R M]
    (z : A ⊗[R] M) : ∃ (a : A) (x : M), z = a ⊗ₜ[R] x := by
  obtain ⟨⟨x, s⟩, hx⟩ :=
    IsLocalizedModule.surj S (TensorProduct.mk R A M 1) z
  let v : Aˣ := (IsLocalization.map_units A s).unit
  have hv : (v : A) = algebraMap R A s := IsUnit.unit_spec _
  have hx' : (v : A) • z = (1 : A) ⊗ₜ[R] x := by
    rw [hv, IsScalarTower.algebraMap_smul]
    exact hx
  refine ⟨(↑(v⁻¹) : A), x, ?_⟩
  calc
    z = (↑(v⁻¹) : A) • ((v : A) • z) := by simp [smul_smul]
    _ = (↑(v⁻¹) : A) • ((1 : A) ⊗ₜ[R] x) := congrArg _ hx'
    _ = _ := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem localized_natural
    {R A C T : Type*} [CommRing R] [CommRing A]
    [Category C] [Preadditive C] [Linear R C]
    [Category T] [Preadditive T] [Linear A T] (p : R)
    (F G : C ⥤ T) (J K : ScalarLocalization R C p ⥤ T)
    (c : Localization.Away p → A)
    (hJ : ∀ N, J.obj N = F.obj N.obj) (hK : ∀ N, K.obj N = G.obj N.obj)
    (mJ : ∀ (N M : C) (f : N ⟶ M) (a : Localization.Away p),
      HEq (J.map (a ⊗ₜ[R] f)) (c a • F.map f))
    (mK : ∀ (N M : C) (f : N ⟶ M) (a : Localization.Away p),
      HEq (K.map (a ⊗ₜ[R] f)) (c a • G.map f)) (τ : F ⟶ G) :
    ∃ η : J ⟶ K, ∀ N, η.app N =
      eqToHom (hJ N) ≫ τ.app N.obj ≫ eqToHom (hK N).symm := by
  let η (N) := eqToHom (hJ N) ≫ τ.app N.obj ≫ eqToHom (hK N).symm
  have hn (N M : ScalarLocalization R C p) (f : N ⟶ M) :
      J.map f ≫ η M = η N ≫ K.map f := by
    obtain ⟨a, v, rfl⟩ := localization_tensor_pure (Submonoid.powers p) f
    rw [(conj_eqToHom_iff_heq _ _ (hJ N) (hJ M)).2 (mJ N.obj M.obj v a),
      (conj_eqToHom_iff_heq _ _ (hK N) (hK M)).2 (mK N.obj M.obj v a)]
    simp only [η, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    simp only [Linear.smul_comp, Linear.comp_smul]
    congr 1
    simpa only [Category.assoc] using
      congrArg (fun z ↦ eqToHom (hJ N) ≫ z ≫ eqToHom (hK M).symm)
        (τ.naturality v)
  exact ⟨⟨η, hn⟩, fun _ ↦ rfl⟩

section Descent
universe v w
variable {C T : Type*} [Category C] [Category T] [Abelian C] [Abelian T]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{w} T]
  (S : C ⥤ T) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  (H : C ⥤ C) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (σc : S.mapHomologicalComplex (.up ℤ) ⟶
    H.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ))

private def sigmaOnComplexes :
    DerivedCategory.Q ⋙ S.mapDerivedCategory ⟶
      DerivedCategory.Q ⋙ H.mapDerivedCategory ⋙ S.mapDerivedCategory :=
  S.mapDerivedCategoryFactors.hom ≫ Functor.whiskerRight σc DerivedCategory.Q ≫
    Functor.whiskerLeft (H.mapHomologicalComplex (.up ℤ)) S.mapDerivedCategoryFactors.inv ≫
    Functor.whiskerRight H.mapDerivedCategoryFactors.inv S.mapDerivedCategory

private def descendedSigma :
    S.mapDerivedCategory ⟶ H.mapDerivedCategory ⋙ S.mapDerivedCategory :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (DerivedCategory T)).preimage
      (sigmaOnComplexes S H σc)

private theorem descendedSigma_app_Q (K : CochainComplex C ℤ) :
    (descendedSigma S H σc).app (DerivedCategory.Q.obj K) =
      (sigmaOnComplexes S H σc).app K :=
  congrArg (fun t ↦ t.app K)
    ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ)) (DerivedCategory T)).map_preimage
        (sigmaOnComplexes S H σc))

attribute [local irreducible] descendedSigma

private theorem sigmaDescent :
    ∃ σ : S.mapDerivedCategory ⟶ H.mapDerivedCategory ⋙ S.mapDerivedCategory,
      (∀ N, σ.app N = S.mapDerivedCategory.map (DerivedCategory.Q.objObjPreimageIso N).inv ≫
        (sigmaOnComplexes S H σc).app (DerivedCategory.Q.objPreimage N) ≫
        S.mapDerivedCategory.map
          (H.mapDerivedCategory.map (DerivedCategory.Q.objObjPreimageIso N).hom)) ∧
      (∀ K, σ.app (DerivedCategory.Q.obj K) = (sigmaOnComplexes S H σc).app K) := by
  refine ⟨descendedSigma S H σc, ?_, descendedSigma_app_Q S H σc⟩
  intro N
  rw [conjugate_component (descendedSigma S H σc)
    (DerivedCategory.Q.objObjPreimageIso N), descendedSigma_app_Q]
  rfl

end Descent

attribute [local irreducible] Functor.mapDerivedCategory

private theorem apply_heq.{v, w}
    {α γ : Sort w} {β : Sort v} {f : α → β} {g : γ → β}
    (h : HEq f g) {x : α} {y : γ} (hx : HEq x y) : HEq (f x) (g y) :=
  heq_of_eq (congr_heq h hx)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem finiteSigma_apply
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) (i : ℤ) :
    HEq (fun x ↦ (frobeniusPointFiniteSigma D l E n K).f i x)
      (fun x ↦ (K.X i).val.map (frobeniusPointRestriction D).op x) := by
  exact (frobeniusPointFiniteSigma_existsUnique D l E n K).choose_spec.1 i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem chainFiniteSigmaNatural
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (K L : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
    (f : K ⟶ L) :
    ((pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).map f ≫
        frobeniusPointFiniteSigma D l E n L =
      frobeniusPointFiniteSigma D l E n K ≫
        ((pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).map
          (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
            (.up ℤ)).map f) := by
  apply HomologicalComplex.hom_ext
  intro i
  ext x
  change (frobeniusPointFiniteSigma D l E n L).f i ((f.f i).val.app _ x) =
    ((f.f i).val.app
      (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
        (ProEt.mk (𝟙 (Spec (.of D.k))))))
        ((frobeniusPointFiniteSigma D l E n K).f i x))
  apply eq_of_heq
  exact (apply_heq (finiteSigma_apply D l E n L i) HEq.rfl).trans
    ((heq_of_eq (PresheafOfModules.naturality_apply (f.f i).val
      (frobeniusPointRestriction D).op x).symm).trans
      (apply_heq HEq.rfl (apply_heq (finiteSigma_apply D l E n K i) HEq.rfl)).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private def naturalFiniteSigma
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ) ⟶
      (inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex (.up ℤ) ⋙
        (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ) :=
  { app K := frobeniusPointFiniteSigma D l E n K
    naturality _ _ f := chainFiniteSigmaNatural D l E n _ _ f }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem integralSigma_apply
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (i : ℤ) :
    HEq (fun x ↦ (frobeniusPointIntegralSigma D l E K).f i x)
      (fun x ↦ (K.X i).val.map (frobeniusPointRestriction D).op x) := by
  exact (frobeniusPointIntegralSigma_existsUnique D l E K).choose_spec.1 i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem chainIntegralSigmaNatural
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (K L : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (f : K ⟶ L) :
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map f ≫
        frobeniusPointIntegralSigma D l E L =
      frobeniusPointIntegralSigma D l E K ≫
        ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
            (.up ℤ)).map f) := by
  apply HomologicalComplex.hom_ext
  intro i
  ext x
  change (frobeniusPointIntegralSigma D l E L).f i ((f.f i).val.app _ x) =
    ((f.f i).val.app
      (op ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
        (ProEt.mk (𝟙 (Spec (.of D.k))))))
        ((frobeniusPointIntegralSigma D l E K).f i x))
  apply eq_of_heq
  exact (apply_heq (integralSigma_apply D l E L i) HEq.rfl).trans
    ((heq_of_eq (PresheafOfModules.naturality_apply (f.f i).val
      (frobeniusPointRestriction D).op x).symm).trans
      (apply_heq HEq.rfl (apply_heq (integralSigma_apply D l E K i) HEq.rfl)).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private def naturalIntegralSigma
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    (pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ) ⟶
      (inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex (.up ℤ) ⋙
        (pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ) :=
  { app K := frobeniusPointIntegralSigma D l E K
    naturality _ _ f := chainIntegralSigmaNatural D l E _ _ f }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem naturalFiniteSigmaDerived
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    ∃ σ : (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory ⟶
        (inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapDerivedCategory ⋙
          (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory,
      (∀ N, σ.app N = frobeniusPointFiniteSigmaDerived D l E n N) ∧
      (∀ K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ,
        σ.app (DerivedCategory.Q.obj K) =
          (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map (frobeniusPointFiniteSigma D l E n K) ≫
          (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors.inv.app
            (((inverseImageFiniteModules l E (frobeniusPointIso D).hom n).mapHomologicalComplex
            (.up ℤ)).obj K) ≫
          (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
            ((inverseImageFiniteModules l E (frobeniusPointIso D).hom
              n).mapDerivedCategoryFactors.inv.app K)) := by
  obtain ⟨σ, hN, hK⟩ := sigmaDescent
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (inverseImageFiniteModules l E (frobeniusPointIso D).hom n) (naturalFiniteSigma D l E n)
  refine ⟨σ, ?_, ?_⟩
  · intro N
    rw [hN]
    simp only [sigmaOnComplexes, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, frobeniusPointFiniteSigmaDerived,
      Functor.map_comp, Category.assoc]
    rfl
  · exact hK


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem naturalIntegralSigmaDerived
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    ∃ σ : (pointIntegralSections l E D.k).mapDerivedCategory ⟶
        (inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapDerivedCategory ⋙
          (pointIntegralSections l E D.k).mapDerivedCategory,
      (∀ N, σ.app N = frobeniusPointIntegralSigmaDerived D l E N) ∧
      (∀ K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ,
        σ.app (DerivedCategory.Q.obj K) =
          (pointIntegralSections l E D.k).mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map (frobeniusPointIntegralSigma D l E K) ≫
          (pointIntegralSections l E D.k).mapDerivedCategoryFactors.inv.app
            (((inverseImageIntegralModules l E (frobeniusPointIso D).hom).mapHomologicalComplex
            (.up ℤ)).obj K) ≫
          (pointIntegralSections l E D.k).mapDerivedCategory.map
            ((inverseImageIntegralModules l E
              (frobeniusPointIso D).hom).mapDerivedCategoryFactors.inv.app K)) := by
  obtain ⟨σ, hN, hK⟩ := sigmaDescent (pointIntegralSections l E D.k)
    (inverseImageIntegralModules l E (frobeniusPointIso D).hom) (naturalIntegralSigma D l E)
  refine ⟨σ, ?_, ?_⟩
  · intro N
    rw [hN]
    simp only [sigmaOnComplexes, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, frobeniusPointIntegralSigmaDerived,
      Functor.map_comp, Category.assoc]
    rfl
  · exact hK

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem naturalIntegralTransport
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ τ : pointFibreIntegralAmbient D l E ⟶
        integralDerivedPullback l E (frobeniusPointIso D).hom ⋙ pointFibreIntegralAmbient D l E,
      ∀ N, τ.app N = frobeniusPointTransportIntegral D l hl E N := by
  let S := pointIntegralSections l E D.k
  let H := inverseImageIntegralModules l E (frobeniusPointIso D).hom
  let Sd := S.mapDerivedCategory
  let Hd := H.mapDerivedCategory
  let T := integralDerivedPullback l E (frobeniusPointIso D).hom
  obtain ⟨σ, _, hσ⟩ := naturalIntegralSigmaDerived D l E
  obtain ⟨κ, hk, hres, _⟩ := inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0} l E
    (frobeniusPointIso D).hom (frobeniusPointPrimeUnit D l hl)
    (frobeniusPointPrimeUnit D l hl)
  let τ : Sd ⟶ T ⋙ Sd := σ ≫ Functor.whiskerRight κ Sd
  have hτ (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
      (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
      (q : P.obj ⟶ K) [QuasiIso q] :
      τ.app (DerivedCategory.Q.obj K) =
        frobeniusPointTransportIntegralComplex D l hl E K P q := by
    dsimp only [τ, NatTrans.comp_app, Functor.whiskerRight_app]
    rw [hσ, hres K P q]
    simp only [frobeniusPointTransportIntegralComplex, Functor.map_comp, Category.assoc]
    rfl
  refine ⟨τ, ?_⟩
  intro N
  apply (frobeniusPointTransportIntegral_existsUnique D l hl E N).choose_spec.2
  intro K P q _ e
  rw [conjugate_component τ e, hτ K P q]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem naturalFiniteTransport
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    ∃ τ : (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory ⟶
        finiteDerivedPullback l E n (frobeniusPointIso D).hom ⋙
          (pointFiniteSections D.k
            (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory,
      ∀ N, τ.app N = frobeniusPointTransportFinite D l hl E n N := by
  let g := (frobeniusPointIso D).hom
  let S := pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))
  let H := inverseImageFiniteModules l E g n
  let Sd := S.mapDerivedCategory
  let Hd := H.mapDerivedCategory
  let T := finiteDerivedPullback l E n g
  have : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  let e := inverseImageFiniteIntrinsicPullbackComparison g
    (Padic.coefficientExtensionRing l E (n + 1))
  obtain ⟨σ, _, hσ⟩ := naturalFiniteSigmaDerived D l E n
  obtain ⟨κ, hk, _⟩ := inverseImagePullbackComparisonFinite_natural.{u, u, 0, 0} l E g
    (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) n
  letI : (coefficientProEtaleModulePullback g
      (CommRingCat.of (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
    integralOperationsLevelPullback_additive l E g n
  letI : PreservesFiniteLimits (coefficientProEtaleModulePullback g
      (CommRingCat.of (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_limits l E g n
  letI : PreservesFiniteColimits (coefficientProEtaleModulePullback g
      (CommRingCat.of (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_colimits l E g n
  let κ' : Hd ⟶ T := κ ≫ (Functor.mapDerivedCategoryNatIso e).hom
  let τ : Sd ⟶ T ⋙ Sd := σ ≫ Functor.whiskerRight κ' Sd
  have hτ (K : CochainComplex
      (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
      τ.app (DerivedCategory.Q.obj K) =
        frobeniusPointTransportFiniteComplex D l hl E n K := by
    dsimp only [τ, NatTrans.comp_app, Functor.whiskerRight_app, κ']
    rw [hσ, hk]
    simp only [frobeniusPointTransportFiniteComplex, inverseImagePullbackComparisonFiniteIntrinsic,
      Functor.map_comp, Category.assoc]
    rfl
  refine Exists.intro τ ?_
  intro N
  rw [conjugate_component τ (DerivedCategory.Q.objObjPreimageIso N), hτ]
  rfl

private theorem fullSubcategory_heq
    {C : Type*} [Category C] {P : ObjectProperty C}
    {X Y X' Y' : P.FullSubcategory} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f.hom g.hom) : HEq f g := by
  cases hX
  cases hY
  exact heq_of_eq (ObjectProperty.hom_ext P (eq_of_heq h))

private theorem map_heq
    {C T : Type*} [Category C] [Category T] (F : C ⥤ T)
    {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  exact heq_of_eq (congrArg F.map (eq_of_heq h))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem naturalIntegralRationalTransport
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ η : pointIntegralRationalFibre D l hl E ⟶
        frobeniusPointIntegralPullback D l hl E ⋙ pointIntegralRationalFibre D l hl E,
      ∀ N, η.app N = (pointFibreSizeDescent E).map
        (ObjectProperty.homMk
          ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            (pointIntegralToField l E)).mapDerivedCategory.map
            (frobeniusPointTransportIntegral D l hl E N.obj))) := by
  obtain ⟨τ, hτ⟩ := naturalIntegralTransport D l hl E
  let η : pointIntegralRationalFibre D l hl E ⟶
      frobeniusPointIntegralPullback D l hl E ⋙ pointIntegralRationalFibre D l hl E :=
    { app N := (pointFibreSizeDescent E).map
        (ObjectProperty.homMk
          ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            (pointIntegralToField l E)).mapDerivedCategory.map
            (τ.app N.obj)))
      naturality := by
        intro N M f
        change (pointFibreSizeDescent E).map _ ≫ (pointFibreSizeDescent E).map _ =
          (pointFibreSizeDescent E).map _ ≫ (pointFibreSizeDescent E).map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        apply congrArg (pointFibreSizeDescent E).map
        apply ObjectProperty.hom_ext
        change _ ≫ _ = _ ≫ _
        simpa only [ObjectProperty.lift, ObjectProperty.homMk, ObjectProperty.ι,
          inducedFunctor, Functor.comp_map, pointFibreRationalAmbient,
          frobeniusPointIntegralPullback, constructibleIntegralPullback,
          ← Functor.map_comp] using
          congrArg (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            (pointIntegralToField l E)).mapDerivedCategory.map (τ.naturality f.hom) }
  refine ⟨η, ?_⟩
  intro N
  dsimp only [η]
  simp only [hτ]


attribute [local irreducible] pointFibreSizeDescent pointFibreSizeLift

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
private theorem naturalRationalTransport
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    letI := frobeniusPointPrimeInvertible D l hl
    ∃ η : pointRationalFibre D l hl E ⟶
        rationalDerivedPullback l E (frobeniusPointIso D).hom ⋙ pointRationalFibre D l hl E,
      ∀ N, HEq (η.app N) (frobeniusPointTransportRational D l hl E N) := by
  letI := frobeniusPointPrimeInvertible D l hl
  let F := pointIntegralRationalFibre D l hl E
  let P := frobeniusPointIntegralPullback D l hl E
  let J := pointRationalFibre D l hl E
  let T := rationalDerivedPullback l E (frobeniusPointIso D).hom
  have hJ (N) : J.obj N = F.obj N.obj := by
    exact (show (pointRationalFibre D l hl E).obj N =
      (pointIntegralRationalFibre D l hl E).obj N.obj from
        by unfold pointRationalFibre; exact
          (pointRationalFibre_existsUnique D l hl E).exists.choose_spec.1 N)
  have hT (N) : T.obj N = frobeniusPointRationalPullbackObj D l hl E N :=
    frobeniusPointRationalPullbackEq D l hl E N
  have hK (N) : (T ⋙ J).obj N = (P ⋙ F).obj N.obj :=
    (congrArg J.obj (hT N)).trans (hJ _)
  have mJ (N M : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
      (f : N ⟶ M) (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
      HEq (J.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f))
        ((sfRationalCoefficientEquiv l E a) • F.map f) := by
    apply fullSubcategory_heq (hJ _) (hJ _)
    exact (pointRationalFibre_existsUnique D l hl E).exists.choose_spec.2 N M f a
  have mK (N M : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
      (f : N ⟶ M) (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
      HEq ((T ⋙ J).map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f))
        ((sfRationalCoefficientEquiv l E a) • (P ⋙ F).map f) := by
    have ht := (rationalDerivedPullback_existsUnique l E
      (frobeniusPointIso D).hom).exists.choose_spec.2.2 N M f a
    have ht' : HEq (T.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f))
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] P.map f) := by
      exact ht
    exact (map_heq J (hT _) (hT _) ht').trans (mJ (P.obj N) (P.obj M) (P.map f) a)
  obtain ⟨τ, hτ⟩ := naturalIntegralRationalTransport D l hl E
  obtain ⟨η, hη⟩ := localized_natural
    (Padic.coefficientExtensionUniformizer l E) F (P ⋙ F) J (T ⋙ J)
    (fun a ↦ sfRationalCoefficientEquiv l E a) hJ hK mJ mK τ
  refine ⟨η, ?_⟩
  intro N
  rw [hη, hτ]
  dsimp only [frobeniusPointTransportRational, pointRationalFibreObjIso, eqToIso]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
/--
The point transport along Frobenius is linear and natural.
Source: Deligne, *La conjecture de Weil II*, (1.1.7), pp. 150--151
(blueprint: lem-weil-frobenius-point-transport-natural).

Proof: restriction is natural on presheaf sections, and the sigma specifications
identify its chain components. Fully faithful localization descends the resulting
chain transformation. Compose it with the natural specified comparison kappa and
use its resolution formulas to identify the literal finite and integral transports.
Restrict to constructible objects, rationalize, and use the pure-tensor description
of every scalar-localized morphism. The common-stage natural transformation gives
the algebraically closed square after conjugation by the recorded object equalities.
The separate rational scalar square supplies the final compatibility clause.
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
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n K i a x
    exact map_smul ((frobeniusPointFiniteSigma D l E n K).f i).hom a x
  · intro n K K' f
    exact (naturalFiniteSigma D l E n).naturality f
  · intro n K K' f
    exact congrArg DerivedCategory.Q.map ((naturalFiniteSigma D l E n).naturality f)
  · intro n N M f
    obtain ⟨σ, hσ, _⟩ := naturalFiniteSigmaDerived D l E n
    simpa only [hσ, Functor.comp_map] using σ.naturality f
  · intro K i a x
    exact map_smul ((frobeniusPointIntegralSigma D l E K).f i).hom a x
  · intro K K' f
    exact (naturalIntegralSigma D l E).naturality f
  · intro K K' f
    exact congrArg DerivedCategory.Q.map ((naturalIntegralSigma D l E).naturality f)
  · intro N M f
    obtain ⟨σ, hσ, _⟩ := naturalIntegralSigmaDerived D l E
    simpa only [hσ, Functor.comp_map] using σ.naturality f
  · refine ⟨?_, ?_, ?_⟩
    · intro n N M f
      obtain ⟨τ, hτ⟩ := naturalFiniteTransport D l hl E n
      apply ObjectProperty.hom_ext
      simpa only [hτ, Functor.comp_map, pointFiniteFibre,
        frobeniusPointTransportFiniteConstructible, frobeniusPointFinitePullback,
        ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.lift,
        ObjectProperty.homMk, ObjectProperty.ι, inducedFunctor] using τ.naturality f.hom
    · intro N M f
      obtain ⟨τ, hτ⟩ := naturalIntegralTransport D l hl E
      apply ObjectProperty.hom_ext
      dsimp only [pointIntegralFibre, frobeniusPointTransportIntegralConstructible,
        frobeniusPointIntegralPullback, constructibleIntegralPullback, ObjectProperty.lift,
        ObjectProperty.homMk, ObjectProperty.ι, inducedFunctor, Functor.comp_obj,
        Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom]
      simpa only [hτ, Functor.comp_map, pointIntegralFibre,
        frobeniusPointTransportIntegralConstructible, frobeniusPointIntegralPullback,
        constructibleIntegralPullback, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.lift,
        ObjectProperty.homMk, ObjectProperty.ι, inducedFunctor]
        using τ.naturality f.hom
    · refine ⟨?_, ?_, ?_⟩
      · intro N M f
        letI := frobeniusPointPrimeInvertible D l hl
        let J := pointRationalFibre D l hl E
        let T := rationalDerivedPullback l E (frobeniusPointIso D).hom
        obtain ⟨η, hη⟩ := naturalRationalTransport D l hl E
        have hc (K) : η.app K = frobeniusPointTransportRational D l hl E K ≫
            J.map (eqToHom (frobeniusPointRationalPullbackEq D l hl E K).symm) := by
          simpa only [eqToHom_map, eqToHom_refl, Category.id_comp] using
            (conj_eqToHom_iff_heq (η.app K)
              (frobeniusPointTransportRational D l hl E K) rfl
              (congrArg J.obj (frobeniusPointRationalPullbackEq D l hl E K))).2 (hη K)
        have hn := congrArg (fun z ↦ z ≫
          J.map (eqToHom (frobeniusPointRationalPullbackEq D l hl E M))) (η.naturality f)
        simpa only [hc, Functor.comp_map, Functor.map_comp, eqToHom_map,
          Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using hn
      · intro Ω _ _ _ A B f
        letI := frobeniusPointPrimeInvertible D l hl
        obtain ⟨τ, hτ⟩ := frobeniusPointTransportQbar_naturalTransformation D l hl Ω
        have he (K) :
            (commonStageDerivedPullback l Ω (frobeniusPointIso D).hom ⋙
              pointQbarFibre D l hl Ω).obj K =
            pointQbarFibreObj D l hl Ω (frobeniusPointQbarPullbackObj D l hl Ω K) :=
          by
          dsimp only [Functor.comp_obj]
          exact (frobeniusPointQbarFibreObjEq D l hl Ω _).trans
            (congrArg (pointQbarFibreObj D l hl Ω)
              (frobeniusPointQbarPullbackEq D l hl Ω K))
        have hc (K) := (conj_eqToHom_iff_heq (τ.app K)
          (frobeniusPointTransportQbar D l hl Ω K)
          (frobeniusPointQbarFibreObjEq D l hl Ω K) (he K)).2 (hτ K)
        have hn := congrArg (fun z ↦
          eqToHom (frobeniusPointQbarFibreObjEq D l hl Ω A).symm ≫ z ≫ eqToHom (he B))
          (τ.naturality f)
        simpa +instances only [hc, he, Functor.comp_map,
          eqToHom_trans, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp, Category.comp_id] using hn
      · intro E' L _ _ _ _ _ _ ι K
        letI := frobeniusPointPrimeInvertible D l hl
        convert frobeniusPointTransportRational_scalar D l hl E' L ι K using 1

end WeilConjectures
