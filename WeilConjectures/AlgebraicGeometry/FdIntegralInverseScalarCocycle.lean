/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.IntegralPullbackComparisonRealization
public import WeilConjectures.AlgebraicGeometry.ScalarCompletionAssociator
public import WeilConjectures.AlgebraicGeometry.PbcScalarExtension
public import WeilConjectures.AlgebraicGeometry.CompletedLineTensorCoherence
public import WeilConjectures.AlgebraicGeometry.FdCoefficientComparison
import all WeilConjectures.AlgebraicGeometry.PbcScalarExtension
import all WeilConjectures.AlgebraicGeometry.CompletedCoefficientPresentationTransport
import WeilConjectures.AlgebraicGeometry.ExactCompletedOrdinaryScalarModel
import all WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison

/-! # Integral inverse scalar cocycle and normalized units

Source: trace-function coefficient-category comparison, extracted steps 4--6
(blueprint: lem-fd-integral-inverse-scalar-cocycle).

The fields are embedded in the fixed algebraic closure by the final embedding and
its composites with the two inclusions. All equations use the published completion
map and the specified normalized associator, in the common integral presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem inverseScalarNaturality {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (χ : F ⟶ G) {X Y : C} (f : X ⟶ Y)
    (b : F.obj X ≅ G.obj X) (hb : b.hom = χ.app X)
    (c : F.obj Y ≅ G.obj Y) (hc : c.hom = χ.app Y) :
    b.inv ≫ F.map f = G.map f ≫ c.inv := by
  apply b.inv_comp_eq.mpr
  rw [← Category.assoc]
  apply c.eq_comp_inv.mpr
  simpa only [Category.assoc, hb, hc] using χ.naturality f

private theorem inverseScalarSquare {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (χ : F ⟶ G) {X Y : C} (b : X ≅ Y)
    (c : F.obj Y ≅ G.obj Y) (hc : c.hom = χ.app Y)
    {Z W : D} (a : F.obj X ⟶ Z) (d : G.obj Y ⟶ W) (e : Z ≅ W)
    (h : χ.app X ≫ G.map b.hom ≫ d = a ≫ e.hom) :
    c.inv ≫ F.map b.inv ≫ a = d ≫ e.inv := by
  apply e.eq_comp_inv.mpr
  simp only [Category.assoc]
  rw [← h]
  rw [← Category.assoc (F.map b.inv), χ.naturality b.inv]
  simp only [Category.assoc, ← hc, c.inv_hom_id_assoc]
  rw [← G.map_comp_assoc, b.inv_hom_id, G.map_id, Category.id_comp]

private theorem localizationIso_descent
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    {F G : D ⥤ E} {V₁ V₂ : C ⥤ E}
    (e₁ : Q ⋙ F ≅ V₁) (e₂ : Q ⋙ G ≅ V₂) (a : V₁ ≅ V₂) :
    ∃ τ : F ≅ G, ∀ P, e₁.hom.app P ≫ a.hom.app P =
      τ.hom.app (Q.obj P) ≫ e₂.hom.app P := by
  let : Localization.Lifting Q W V₁ F := ⟨e₁⟩
  let : Localization.Lifting Q W V₂ G := ⟨e₂⟩
  let τ := Localization.liftNatIso Q W V₁ V₂ F G a
  refine ⟨τ, ?_⟩
  intro P
  have h := Localization.liftNatTrans_app Q W V₁ V₂ F G a.hom P
  change τ.hom.app (Q.obj P) = e₁.hom.app P ≫ a.hom.app P ≫ e₂.inv.app P at h
  rw [h, Category.assoc, Category.assoc, e₂.inv_hom_id_app, Category.comp_id]

private theorem localizedSquare
    {A A' B B' C C' D D' : Type*}
    [Category A] [Category A'] [Category B] [Category B']
    [Category C] [Category C'] [Category D] [Category D']
    (QA : A ⥤ A') (QB : B ⥤ B') (QC : C ⥤ C') (QD : D ⥤ D')
    (W : MorphismProperty A) [QA.IsLocalization W]
    {F : A ⥤ B} {H : B ⥤ D} {G : A ⥤ C} {Z : Type*}
    (J : Z → C ⥤ D) {x y : Z} (p : x = y)
    {LF : A' ⥤ B'} {LH : B' ⥤ D'} {LG : A' ⥤ C'} {LI : C' ⥤ D'}
    (c : QA ⋙ LF ≅ F ⋙ QB) (g : QA ⋙ LG ≅ G ⋙ QC)
    (h : QB ⋙ LH ≅ H ⋙ QD) (b : QC ⋙ LI ≅ J y ⋙ QD)
    (e : F ⋙ H ≅ G ⋙ J x)
    (εF : ∀ P, LF.obj (QA.obj P) ⟶ QB.obj (F.obj P))
    (εI : ∀ P, LI.obj (QC.obj P) ⟶ QD.obj ((J y).obj P))
    (hc : ∀ P, c.hom.app P = εF P) (hb : ∀ P, b.hom.app P = εI P) :
    ∃ τ : LF ⋙ LH ≅ LG ⋙ LI, ∀ P,
      LH.map (εF P) ≫ h.hom.app (F.obj P) ≫ QD.map (e.hom.app P) ≫
        eqToHom (congrArg (fun z ↦ QD.obj ((J z).obj (G.obj P))) p) =
      τ.hom.app (QA.obj P) ≫ LI.map (g.hom.app P) ≫ εI (G.obj P) := by
  let d := e ≪≫ Functor.isoWhiskerLeft G (eqToIso (congrArg J p))
  let e₁ : QA ⋙ (LF ⋙ LH) ≅ (F ⋙ H) ⋙ QD :=
    Functor.isoWhiskerRight c LH ≪≫ Functor.isoWhiskerLeft F h
  let e₂ : QA ⋙ (LG ⋙ LI) ≅ (G ⋙ J y) ⋙ QD :=
    Functor.isoWhiskerRight g LI ≪≫ Functor.isoWhiskerLeft G b
  obtain ⟨τ, hτ⟩ := localizationIso_descent QA W e₁ e₂
    (Functor.isoWhiskerRight d QD)
  have hd (P : A) : QD.map (d.hom.app P) = QD.map (e.hom.app P) ≫
      eqToHom (congrArg (fun z ↦ QD.obj ((J z).obj (G.obj P))) p) := by
    subst y
    simp only [d, eqToIso_refl, Functor.isoWhiskerLeft_refl, Iso.trans_refl,
      eqToHom_refl, Category.comp_id]
  refine ⟨τ, ?_⟩
  intro P
  have hs := hτ P
  dsimp only [e₁, e₂, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hs
  rw [hc, hb, hd] at hs
  simpa only [Category.assoc] using hs

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (ι : E →ₐ[ℚ_[l]] L) (κ : L →ₐ[ℚ_[l]] M) (T : Scheme.{u})

/-- Forward and inverse equations for the actual quotient-cocone completion maps.
The supplied associator package is the specified framework associator normalized by
ordinary balancing; its representative and uniqueness fields retain the actual cocones
and independence from K-flat and cofinal-exponent choices.
Source: trace-function final coefficient-category sentence, extracted steps 4--6
(blueprint: lem-fd-integral-inverse-scalar-cocycle).

Proof:
1. Integral stratified-perfect characterization identifies the integral full categories
through integralDetailedTransport. Their objects are derived complete. Apply the
normalization field of lem-fix-scalar-completion-associator to the actual chi maps.
Its ordinary_model and independent clauses fix balancing on representatives and remove
all representative and cofinal-exponent choices. This gives the forward equation.
2. Ordinary presentation transport fixes tensor generators and multiplication. Thus
ordinary balancing is the integral comparison underlying prop-weil-pbc-scalar-extension;
the companion transport statement below records this identification and rationalization.
3. Put D = chi_2 at C_1 K followed by U_2(chi_1). Naturality of chi_2 at chi_1 inverse
identifies D inverse with chi_2 inverse at U_1 K followed by C_2(chi_1 inverse).
Cancel D and chi_3 from the forward equation. The result is the inverse equation.
4. No inclusion was required to be strict, so this calculation includes every repeated
field case. The companion unit statement records the two resulting comparison squares.
-/
theorem fdIntegralInverseScalarCocycle
    (_D : FiniteFieldDatum.{d}) (_hl : l ≠ _D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_e : M →ₐ[ℚ_[l]] Ω) [IsNoetherian T]
    [_hdim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [_hinv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (A : ScalarCompletionAssociatorData.{u, u} l T)
    (K : sfIntegralConstructibleCategory l E T) :
    ((completedScalarComparison l L M κ T).app
        ((completedDerivedScalarExtension l E L ι T).obj K.obj) ≫
      (integralScalarExtensionOfUniverses l L M κ T).map
        ((completedScalarComparison l E L ι T).app K.obj) ≫
      (A.associator E L M ι κ).hom.app
        ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩ =
      (A.ordinary E L M ι κ).hom.app K.obj ≫
        (completedScalarComparison l E M (κ.comp ι) T).app K.obj) ∧
    ((CompletedLineTensor.chi l L T M κ _
        (A.preserves E L ι K.obj (CompletedLineTensor.intrinsic_complete l E T K))).inv ≫
      (completedDerivedScalarExtension l L M κ T).map
        (CompletedLineTensor.chi l E T L ι K.obj
          (CompletedLineTensor.intrinsic_complete l E T K)).inv ≫
      (A.ordinary E L M ι κ).hom.app K.obj =
      (A.associator E L M ι κ).hom.app
          ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩ ≫
        (CompletedLineTensor.chi l E T M (κ.comp ι) K.obj
          (CompletedLineTensor.intrinsic_complete l E T K)).inv) := by
  let hK := CompletedLineTensor.intrinsic_complete l E T K
  have h := A.normalization E L M ι κ ⟨K.obj, hK⟩
  refine ⟨h, ?_⟩
  exact inverseScalarSquare
    (completedDerivedScalarExtension l L M κ T)
    (integralScalarExtensionOfUniverses l L M κ T)
    (completedScalarComparison l L M κ T)
    (CompletedLineTensor.chi l E T L ι K.obj hK)
    (CompletedLineTensor.chi l L T M κ _ (A.preserves E L ι K.obj hK)) rfl
    ((A.ordinary E L M ι κ).hom.app K.obj)
    ((A.associator E L M ι κ).hom.app ⟨K.obj, hK⟩)
    (CompletedLineTensor.chi l E T M (κ.comp ι) K.obj hK) h

/-- The actual identity completion map, its normalized inverse, and both unit squares.
Here A.unit is eta inverse, and A.ordinaryUnit is tensor multiplication mu.
The last equation is the all-equal-fields square after these identifications.
Source: trace-function coefficient comparison, extracted steps 4--6
(blueprint: lem-fd-integral-inverse-scalar-cocycle).

Proof:
1. The identity-extension clause of lem-weil-finite-free-completed-scalar-comparison
identifies chi, on every K-flat representative, with multiplication followed by the
actual quotient completeness unit. Descent gives b = mu followed by eta. Invert this
equality to obtain b inverse followed by mu = eta inverse.
2. Substitute L = E in the inverse cocycle. The left ordinary associator is C(mu_E)
and the left completed associator is U(eta_E inverse). Replace b_EE inverse followed
by mu_E by eta_E inverse. Naturality of b inverse gives the first displayed square.
3. Substitute M = L. The right ordinary associator is mu_L and the right completed
associator is eta_L inverse. Naturality of mu_L at b inverse reduces the second
square to b inverse followed by eta_L inverse.
4. With all fields equal substitute the identity normalization. Both routes reduce
to eta inverse followed by itself. Conjugating by eta identifies every edge with
identity. Repetitions adjacent to a strict extension are included in steps 2 and 3.
-/
theorem fdIntegralInverseScalarUnits
    (_D : FiniteFieldDatum.{d}) (_hl : l ≠ _D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_e : L →ₐ[ℚ_[l]] Ω) [IsNoetherian T]
    [_hdim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [_hinv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (A : ScalarCompletionAssociatorData.{u, u} l T)
    (K : sfIntegralConstructibleCategory l E T) :
    ((completedScalarComparison l E E (AlgHom.id ℚ_[l] E) T).app K.obj =
      (A.ordinaryUnit E).hom.app K.obj ≫
        (A.unit E).inv.app ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩) ∧
    ((CompletedLineTensor.chi l E T E (AlgHom.id ℚ_[l] E) K.obj
        (CompletedLineTensor.intrinsic_complete l E T K)).inv ≫
      (A.ordinaryUnit E).hom.app K.obj =
      (A.unit E).hom.app ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩) ∧
    ((CompletedLineTensor.chi l E T L ι _
        (A.preserves E E (AlgHom.id ℚ_[l] E) K.obj
          (CompletedLineTensor.intrinsic_complete l E T K))).inv ≫
      (completedDerivedScalarExtension l E L ι T).map
        ((A.unit E).hom.app ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩) =
      (integralScalarExtensionOfUniverses l E L ι T).map
        ((A.unit E).hom.app ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩) ≫
        (CompletedLineTensor.chi l E T L ι K.obj
          (CompletedLineTensor.intrinsic_complete l E T K)).inv) ∧
    ((CompletedLineTensor.chi l L T L (AlgHom.id ℚ_[l] L) _
        (A.preserves E L ι K.obj (CompletedLineTensor.intrinsic_complete l E T K))).inv ≫
      (completedDerivedScalarExtension l L L (AlgHom.id ℚ_[l] L) T).map
        (CompletedLineTensor.chi l E T L ι K.obj
          (CompletedLineTensor.intrinsic_complete l E T K)).inv ≫
      (A.ordinaryUnit L).hom.app
        ((completedDerivedScalarExtension l E L ι T).obj K.obj) =
      (A.unit L).hom.app
          ⟨(integralScalarExtensionOfUniverses l E L ι T).obj K.obj,
            A.preserves E L ι K.obj (CompletedLineTensor.intrinsic_complete l E T K)⟩ ≫
        (CompletedLineTensor.chi l E T L ι K.obj
          (CompletedLineTensor.intrinsic_complete l E T K)).inv) ∧
    (HEq ((A.ordinary E E L (AlgHom.id ℚ_[l] E) ι).hom.app K.obj)
      ((completedDerivedScalarExtension l E L ι T).map
        ((A.ordinaryUnit E).hom.app K.obj))) ∧
    (HEq ((A.ordinary E L L ι (AlgHom.id ℚ_[l] L)).hom.app K.obj)
      ((A.ordinaryUnit L).hom.app ((completedDerivedScalarExtension l E L ι T).obj K.obj))) ∧
    ((A.associator E E L (AlgHom.id ℚ_[l] E) ι).hom.app
        ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩ =
      (integralScalarExtensionOfUniverses l E L ι T).map
        ((A.unit E).hom.app ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩)) ∧
    ((A.associator E L L ι (AlgHom.id ℚ_[l] L)).hom.app
        ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩ =
      (A.unit L).hom.app
        ⟨(integralScalarExtensionOfUniverses l E L ι T).obj K.obj,
          A.preserves E L ι K.obj (CompletedLineTensor.intrinsic_complete l E T K)⟩) ∧
    ((A.unit E).inv.app ⟨K.obj, CompletedLineTensor.intrinsic_complete l E T K⟩ ≫
      (CompletedLineTensor.chi l E T E (AlgHom.id ℚ_[l] E) K.obj
        (CompletedLineTensor.intrinsic_complete l E T K)).inv ≫
      (A.ordinaryUnit E).hom.app K.obj = 𝟙 K.obj) := by
  let hK := CompletedLineTensor.intrinsic_complete l E T K
  let X : ObjectProperty.FullSubcategory (IsDerivedCompleteUnrestricted l E T) :=
    ⟨K.obj, hK⟩
  let b := CompletedLineTensor.chi l E T E (AlgHom.id ℚ_[l] E) K.obj hK
  have hu := A.unit_normalization E X
  have hi : b.inv ≫ (A.ordinaryUnit E).hom.app K.obj = (A.unit E).hom.app X :=
    b.inv_comp_eq.mpr hu.symm
  refine ⟨?_, hi, ?_, ?_, ?_, ?_, A.left_unit E L ι X, A.right_unit E L ι X, ?_⟩
  · exact ((A.unit E).app X).eq_comp_inv.mpr hu
  · exact inverseScalarNaturality
      (completedDerivedScalarExtension l E L ι T)
      (integralScalarExtensionOfUniverses l E L ι T)
      (completedScalarComparison l E L ι T) ((A.unit E).hom.app X)
      (CompletedLineTensor.chi l E T L ι _
        (A.preserves E E (AlgHom.id ℚ_[l] E) K.obj hK)) rfl
      (CompletedLineTensor.chi l E T L ι K.obj hK) rfl
  · let Y : ObjectProperty.FullSubcategory (IsDerivedCompleteUnrestricted l L T) :=
      ⟨_, A.preserves E L ι K.obj hK⟩
    let c := CompletedLineTensor.chi l L T L (AlgHom.id ℚ_[l] L) Y.obj Y.property
    have hc : c.inv ≫ (A.ordinaryUnit L).hom.app Y.obj = (A.unit L).hom.app Y :=
      c.inv_comp_eq.mpr (A.unit_normalization L Y).symm
    rw [(A.ordinaryUnit L).hom.naturality]
    simpa only [Category.assoc, Functor.id_map] using congrArg
      (fun f ↦ f ≫ (CompletedLineTensor.chi l E T L ι K.obj hK).inv) hc
  · have hn := A.normalization E E L (AlgHom.id ℚ_[l] E) ι X
    simp only [AlgHom.comp_id] at hn
    rw [A.left_unit] at hn
    change (completedScalarComparison l E L ι T).app _ ≫
      (integralScalarExtensionOfUniverses l E L ι T).map
        ((completedScalarComparison l E E (AlgHom.id ℚ_[l] E) T).app K.obj) ≫
      (integralScalarExtensionOfUniverses l E L ι T).map ((A.unit E).hom.app X) =
      (A.ordinary E E L (AlgHom.id ℚ_[l] E) ι).hom.app K.obj ≫
        (completedScalarComparison l E L ι T).app K.obj at hn
    rw [← Functor.map_comp, hu,
      ← (completedScalarComparison l E L ι T).naturality] at hn
    have he := (cancel_mono (CompletedLineTensor.chi l E T L ι K.obj hK).hom).mp hn
    exact heq_of_eq he.symm
  · have hn := A.normalization E L L ι (AlgHom.id ℚ_[l] L) X
    simp only [AlgHom.id_comp] at hn
    rw [A.right_unit] at hn
    rw [← (completedScalarComparison l L L (AlgHom.id ℚ_[l] L) T).naturality_assoc] at hn
    rw [A.unit_normalization L
      ⟨(integralScalarExtensionOfUniverses l E L ι T).obj X.obj,
        A.preserves E L ι X.obj X.property⟩] at hn
    rw [(A.ordinaryUnit L).hom.naturality] at hn
    simp only [Functor.id_map] at hn
    have he := (cancel_mono (CompletedLineTensor.chi l E T L ι K.obj hK).hom).mp hn
    exact heq_of_eq he.symm
  · rw [hi]
    exact (A.unit E).inv_hom_id_app X


section Presentation
variable (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {F G H : Padic.FiniteCoefficientFields l Ω}

/-- The finite-stage and ordinary coefficient maps are the same normalized map.
Source: trace-function coefficient comparison, ordinary presentation clause
(blueprint: lem-fd-integral-inverse-scalar-cocycle).

Proof: the finite-stage coefficient map is uniquely determined by its quotient
projections. The constant-presentation comparisons are their normalized sheafification
comparisons. On quotient representatives both maps are the same integer inclusion.
Thus their finite projections agree, and uniqueness of the completed limit map gives
the equality. This is an identification of existing maps, not a new construction.
-/
theorem fdIntegralCoefficientMap_eq (h : F ≤ G) :
    pbcCompletedScalarMap l Ω T h =
      pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
        (pbcFiniteFieldInclusion l Ω h) T := by
  apply (pbcCompletedScalarMap_exists l Ω T h).unique
  · exact (pbcCompletedScalarMap_exists l Ω T h).exists.choose_spec
  · intro n
    have hc := (pbcScalarCoefficientMap_exists l (pbcFiniteField.{u} l Ω F)
      (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T).exists.choose_spec n
    change pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω F)
      (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T ≫ _ = _ at hc
    rw [hc]
    congr 1
    unfold pbcFiniteScalarMap
    rw [scalarLevelConstantComparison_naturality]
    change AdicCoefficients.coefficientMap T
      (pbcScalarQuotientMap l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
        (pbcFiniteFieldInclusion l Ω h) n) =
      (pbcLevelConstantComparison T (pbcStageDatum.{u} l Ω F) n).inv ≫
        (pbcLevelConstantComparison T (pbcStageDatum.{u} l Ω F) n).hom ≫
          AdicCoefficients.coefficientMap T (pbcQuotientInclusion l Ω h n)
    erw [Iso.inv_hom_id_assoc]
    rfl

section OrdinaryPresentationConstruction

attribute [-instance] integralOperationsAbLocallyBijective integralOperationsAbSheafify
  integralOperationsSiteSmall integralOperationsCommHasDerivedCategory
  scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive
attribute [local irreducible] HasDerivedCategory.standard completedScalarChangeData
  integralOrdinaryScalar
attribute [local instance 5000] integralTowerHasDerivedCategory
private local instance : EssentiallySmall.{u+1} T.ProEt :=
  essentiallySmallSelf.{0, u, u+1} _
private local instance : HasSheafify (ProEt.topology T) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} T
private local instance :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u+1} :=
  integralCoefficientAbLocallyBijective.{u, u} T

private theorem fdIntegralOrdinaryPresentation_existsUnique_aux (h : F ≤ G)
    (o : FdOrdinaryScalarTransport l Ω T h) :
    ∃! τ :
      completedDerivedScalarExtension l (pbcFiniteField.{u} l Ω F)
          (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T ⋙
        integralDetailedTransport T l (pbcFiniteField.{u} l Ω G) ≅
      integralDetailedTransport T l (pbcFiniteField.{u} l Ω F) ⋙
        pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F)
          (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T,
      ∀ P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω F) T).FullSubcategory,
        (integralDetailedTransport T l (pbcFiniteField.{u} l Ω G)).map
            (completedScalarCounit l (pbcFiniteField.{u} l Ω F)
              (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T P.obj) ≫
          (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω G) T).hom.app
            ((completedOrdinaryScalarComplex l (pbcFiniteField.{u} l Ω F)
              (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj) ≫
          DerivedCategory.Q.map ((o.complex l Ω).hom.app P.obj) ≫
          eqToHom (congrArg
            (fun φ : pbcAdicCompletion T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω F)) ⟶
                pbcAdicCompletion T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω G)) ↦
              DerivedCategory.Q.obj (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj
                (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω F) T).mapHomologicalComplex
                  (.up ℤ)).obj P.obj)))
            (fdIntegralCoefficientMap_eq l T Ω h)) =
        τ.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F)
            (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T).map
              ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω F) T).hom.app P.obj) ≫
          pbcComplexCounit (pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω F)
            (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T)
              (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω F) T).mapHomologicalComplex
                (.up ℤ)).obj P.obj) := by
  let EF := pbcFiniteField.{u} l Ω F
  let EG := pbcFiniteField.{u} l Ω G
  let i := pbcFiniteFieldInclusion l Ω h
  let S := completedOrdinaryScalarExtension.{u, u} l EF EG i T
  let U : integralTowerModules l EF T ⥤
      pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l EF)) :=
    fdCoefficientTransport l EF T
  let V : integralTowerModules l EG T ⥤
      pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l EG)) :=
    fdCoefficientTransport l EG T
  let B := pbcExtend (pbcScalarCoefficientMap l EF EG i T)
  have : U.Additive := fdCoefficientTransportAdditive l EF T
  have : V.Additive := fdCoefficientTransportAdditive l EG T
  have : PreservesFiniteLimits U := fdCoefficientTransportLimits l EF T
  have : PreservesFiniteColimits U := fdCoefficientTransportColimits l EF T
  have : PreservesFiniteLimits V := fdCoefficientTransportLimits l EG T
  have : PreservesFiniteColimits V := fdCoefficientTransportColimits l EG T
  obtain ⟨hlim, hcolim, c, hc⟩ := exactCompletedOrdinaryScalarModel l T EF EG i
  have := hlim
  have := hcolim
  have := (scalarExtension_exact l EF EG i T).1
  have := (scalarExtension_exact l EF EG i T).2
  let hm := fdIntegralCoefficientMap_eq l T Ω h
  obtain ⟨b, hb⟩ := scalarDerivedComparison l EF EG i T
  let cc : DerivedCategory.Q ⋙ completedDerivedScalarExtension.{u, u} l EF EG i T ≅
      S.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft DerivedCategory.Q c ≪≫ S.mapDerivedCategoryFactors
  let bb : DerivedCategory.Q ⋙ pbcEmbeddingAmbientTensor l EF EG i T ≅
      B.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft DerivedCategory.Q b ≪≫ B.mapDerivedCategoryFactors
  have hcc (P : CochainComplex (integralTowerModules l EF T) ℤ) :
      cc.hom.app P = completedScalarCounit.{u, u} l EF EG i T P := by
    dsimp only [cc, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app]
    exact hc P
  have hbb (P : CochainComplex (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l EF))) ℤ) :
      bb.hom.app P = pbcComplexCounit (pbcScalarCoefficientMap l EF EG i T) P := by
    dsimp only [bb, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app]
    exact hb P
  obtain ⟨τ, hτ⟩ := localizedSquare DerivedCategory.Q DerivedCategory.Q
    DerivedCategory.Q DerivedCategory.Q
    (HomologicalComplex.quasiIso (integralTowerModules l EF T) (.up ℤ))
    (F := S.mapHomologicalComplex (.up ℤ)) (H := V.mapHomologicalComplex (.up ℤ))
    (G := U.mapHomologicalComplex (.up ℤ))
    (fun φ : pbcAdicCompletion T (pbcIntegralDatum l EF) ⟶
        pbcAdicCompletion T (pbcIntegralDatum l EG) ↦
      (pbcExtend φ).mapHomologicalComplex (.up ℤ)) hm
    cc U.mapDerivedCategoryFactors V.mapDerivedCategoryFactors bb (o.complex l Ω)
    (fun P ↦ completedScalarCounit.{u, u} l EF EG i T P)
    (fun P ↦ pbcComplexCounit (pbcScalarCoefficientMap l EF EG i T) P) hcc hbb
  refine ⟨τ, fun P ↦ hτ P.obj, ?_⟩
  intro τ' hτ'
  apply Iso.ext
  let Λ := integralOperationsGoodLocalization l EF T
  let W := (HomologicalComplex.quasiIso (integralTowerModules l EF T) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l EF T).ι
  have : Λ.IsLocalization W := integralOperationsGoodLocalization_isLocalization l EF T
  apply Localization.natTrans_ext Λ W
  intro P
  have : IsIso (pbcComplexCounit (pbcScalarCoefficientMap l EF EG i T)
      ((U.mapHomologicalComplex (.up ℤ)).obj P.obj)) := by
    rw [← hb]
    infer_instance
  exact (cancel_mono ((pbcEmbeddingAmbientTensor l EF EG i T).map
    (U.mapDerivedCategoryFactors.hom.app P.obj) ≫
    pbcComplexCounit (pbcScalarCoefficientMap l EF EG i T)
      ((U.mapHomologicalComplex (.up ℤ)).obj P.obj))).mp
        ((hτ' P).symm.trans (hτ P.obj))

end OrdinaryPresentationConstruction

/-- The derived ordinary presentation transport, uniquely fixed by its generator-normalized
cochain comparison and the two universal tensor counits.
Source: trace-function coefficient comparison, ordinary balancing clause, step 2
(blueprint: lem-fd-integral-inverse-scalar-cocycle).

Proof: finite-free exactness identifies the chosen ordinary derived scalar functor
with the exact derived functor, with its specified counit. Use the analogous PBC
comparison. Conjugate the supplied cochain isomorphism and its coefficient-map cast
by these invertible counits and the coefficient-transport factor isomorphisms.
Localization lifts this isomorphism, and its component formula gives normalization
on every complex. On good complexes cancel the same invertible counits;
localization extensionality gives uniqueness. No new scalar functor is chosen.
-/
theorem fdIntegralOrdinaryPresentation_existsUnique (h : F ≤ G)
    (o : FdOrdinaryScalarTransport l Ω T h) :
    ∃! τ :
      completedDerivedScalarExtension l (pbcFiniteField.{u} l Ω F)
          (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T ⋙
        integralDetailedTransport T l (pbcFiniteField.{u} l Ω G) ≅
      integralDetailedTransport T l (pbcFiniteField.{u} l Ω F) ⋙
        pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F)
          (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T,
      ∀ P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω F) T).FullSubcategory,
        (integralDetailedTransport T l (pbcFiniteField.{u} l Ω G)).map
            (completedScalarCounit l (pbcFiniteField.{u} l Ω F)
              (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T P.obj) ≫
          (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω G) T).hom.app
            ((completedOrdinaryScalarComplex l (pbcFiniteField.{u} l Ω F)
              (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj) ≫
          DerivedCategory.Q.map ((o.complex l Ω).hom.app P.obj) ≫
          eqToHom (congrArg
            (fun φ : pbcAdicCompletion T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω F)) ⟶
                pbcAdicCompletion T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω G)) ↦
              DerivedCategory.Q.obj (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj
                (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω F) T).mapHomologicalComplex
                  (.up ℤ)).obj P.obj)))
            (fdIntegralCoefficientMap_eq l T Ω h)) =
        τ.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F)
            (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T).map
              ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω F) T).hom.app P.obj) ≫
          pbcComplexCounit (pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω F)
            (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T)
              (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω F) T).mapHomologicalComplex
                (.up ℤ)).obj P.obj) :=
  fdIntegralOrdinaryPresentation_existsUnique_aux l T Ω h o

/-- Ordinary presentation transport chosen from its unique generator/counit normalization.
Source: trace-function coefficient comparison, step 2
(blueprint: lem-fd-integral-inverse-scalar-cocycle). -/
def fdIntegralOrdinaryPresentation (h : F ≤ G)
    (o : FdOrdinaryScalarTransport l Ω T h) :=
  (fdIntegralOrdinaryPresentation_existsUnique l T Ω h o).exists.choose

set_option linter.unusedSectionVars false in
/-- The small finite-field models retain composition of their actual inclusions.
Source: trace-function coefficient comparison, ordinary presentation identification
(blueprint: lem-fd-integral-inverse-scalar-cocycle).

Proof: expand pbcFiniteFieldInclusion. The middle Shrink equivalence and its inverse
cancel. The two intermediate-field inclusions compose to the direct inclusion on
every element. Algebra-hom extensionality gives the equality. This is solely a
presentation equality, including identity inclusions.
-/
theorem fdIntegralCoefficientInclusion_comp (h : F ≤ G) (k : G ≤ H) :
    pbcFiniteFieldInclusion.{u} l Ω (h.trans k) =
      (pbcFiniteFieldInclusion.{u} l Ω k).comp (pbcFiniteFieldInclusion.{u} l Ω h) := by
  change (Shrink.algEquiv ℚ_[l] H.val).symm.toAlgHom.comp
      ((IntermediateField.inclusion (h.trans k)).comp
        (Shrink.algEquiv ℚ_[l] F.val).toAlgHom) =
    ((Shrink.algEquiv ℚ_[l] H.val).symm.toAlgHom.comp
      ((IntermediateField.inclusion k).comp (Shrink.algEquiv ℚ_[l] G.val).toAlgHom)).comp
        ((Shrink.algEquiv ℚ_[l] G.val).symm.toAlgHom.comp
          ((IntermediateField.inclusion h).comp (Shrink.algEquiv ℚ_[l] F.val).toAlgHom))
  ext x
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.apply_symm_apply]
  rfl

/-- Ordinary balancing expressed in the PBC presentation by the fixed tensor-generator
transport. The equality casts only identify composite and direct field inclusions.
Source: trace-function coefficient comparison, ordinary balancing clause
(blueprint: lem-fd-integral-inverse-scalar-cocycle). -/
def fdIntegralOrdinaryBalancingMap (A : ScalarCompletionAssociatorData.{u, u} l T)
    (h : F ≤ G) (k : G ≤ H)
    (o₁ : FdOrdinaryScalarTransport l Ω T h)
    (o₂ : FdOrdinaryScalarTransport l Ω T k)
    (o₃ : FdOrdinaryScalarTransport l Ω T (h.trans k))
    (K : DerivedCategory (integralTowerModules l (pbcFiniteField.{u} l Ω F) T)) :
    (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω G) (pbcFiniteField.{u} l Ω H)
      (pbcFiniteFieldInclusion l Ω k) T).obj ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω
      F) (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T).obj
      ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω F)).obj K)) ⟶
      (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω H)
        ((pbcFiniteFieldInclusion l Ω k).comp (pbcFiniteFieldInclusion l Ω h)) T).obj
        ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω F)).obj K) :=
  (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω G) (pbcFiniteField.{u} l Ω H)
    (pbcFiniteFieldInclusion l Ω k) T).map ((fdIntegralOrdinaryPresentation l T Ω h o₁).inv.app K) ≫
    (fdIntegralOrdinaryPresentation l T Ω k o₂).inv.app ((completedDerivedScalarExtension l
      (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T).obj
      K) ≫
    (integralDetailedTransport T l (pbcFiniteField.{u} l Ω H)).map ((A.ordinary
      (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G) (pbcFiniteField.{u} l Ω H)
      (pbcFiniteFieldInclusion l Ω h) (pbcFiniteFieldInclusion l Ω k)).hom.app K) ≫
    (integralDetailedTransport T l (pbcFiniteField.{u} l Ω H)).map (eqToHom (congrArg
    (fun a : (pbcFiniteField.{u} l Ω F) →ₐ[ℚ_[l]] (pbcFiniteField.{u} l Ω H) ↦
      (completedDerivedScalarExtension l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω H) a
      T).obj K)
    (fdIntegralCoefficientInclusion_comp l Ω h k)).symm) ≫
    (fdIntegralOrdinaryPresentation l T Ω (h.trans k) o₃).hom.app K ≫
    eqToHom (congrArg
    (fun a : (pbcFiniteField.{u} l Ω F) →ₐ[ℚ_[l]] (pbcFiniteField.{u} l Ω H) ↦
      (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω H) a T).obj
      ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω F)).obj K))
    (fdIntegralCoefficientInclusion_comp l Ω h k))

/-- The derived ordinary balancing comparison for the chosen normalized presentations.
Source: trace-function coefficient comparison, ordinary balancing clause
(blueprint: lem-fd-integral-ordinary-balancing-core).

Proof: both normalized ordinary presentation transports fix sheafified tensor generators
(`FdOrdinaryScalarTransport.generators`), and `A.ordinary` is fixed on flat-term K-flat
models by `A.ordinary_model`. On a flat-term K-flat representative both routes send
(x tensor b) tensor c to x tensor bc, with the same quotient coefficient projections;
the coefficient-map casts are the equality `fdIntegralCoefficientInclusion_comp`. The
cochain maps are therefore equal. Conjugating by the universal tensor counits, as in the
normalization of `fdIntegralOrdinaryPresentation_existsUnique`, gives the derived
equation on good complexes; `pbcAmbientScalarComp` is by construction the
adjunction-normalized balanced comparison with the same counits. Every integral object
is isomorphic to the image of a good complex, and both sides are natural, so localization
extensionality gives the equation on every integral constructible object.
-/
theorem fdIntegralOrdinaryBalancing_core
    (_D : FiniteFieldDatum.{d}) (_hl : l ≠ _D.p) [IsNoetherian T]
    [hdim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [hinv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (A : ScalarCompletionAssociatorData.{u, u} l T)
    (h : F ≤ G) (k : G ≤ H)
    (o₁ : FdOrdinaryScalarTransport l Ω T h)
    (o₂ : FdOrdinaryScalarTransport l Ω T k)
    (o₃ : FdOrdinaryScalarTransport l Ω T (h.trans k))
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω F) T) :
    fdIntegralOrdinaryBalancingMap l T Ω A h k o₁ o₂ o₃ K.obj =
      (pbcAmbientScalarComp l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
        (pbcFiniteField.{u} l Ω H) (pbcFiniteFieldInclusion l Ω h)
        (pbcFiniteFieldInclusion l Ω k) T).hom.app
        ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω F)).obj K.obj) := by
  sorry

/-- Rationalization of the derived ordinary balancing comparison.
Source: trace-function coefficient comparison, ordinary balancing clause
(blueprint: lem-fd-integral-ordinary-balancing-rationalized).

Proof: rewrite the integral balancing map by `fdIntegralOrdinaryBalancing_core`. By its
definition, `pbcRationalScalarCompComponent` is the rationalization of the full-subcategory
isomorphism with underlying map the component of `pbcAmbientScalarComp` at `J.obj`. The
two casts along `hJ` cancel against that component by naturality (for `hJ = rfl` they
are identities), so both sides are the rationalization of the same morphism.
-/
theorem fdIntegralOrdinaryBalancing_rationalized
    (_D : FiniteFieldDatum.{d}) (_hl : l ≠ _D.p) [IsNoetherian T]
    [hdim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [hinv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (A : ScalarCompletionAssociatorData.{u, u} l T)
    (h : F ≤ G) (k : G ≤ H)
    (o₁ : FdOrdinaryScalarTransport l Ω T h)
    (o₂ : FdOrdinaryScalarTransport l Ω T k)
    (o₃ : FdOrdinaryScalarTransport l Ω T (h.trans k))
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω F) T)
    (J : PbcBoundedConstructibleComplete T
      (pbcIntegralDatum l (pbcFiniteField.{u} l Ω F)))
    (hJ : J.obj = (integralDetailedTransport T l
      (pbcFiniteField.{u} l Ω F)).obj K.obj) :
    (pbcRationalization T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω H))
      (pbcUniformizer l (pbcFiniteField.{u} l Ω H))).map
      (ObjectProperty.homMk
        ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω G)
          (pbcFiniteField.{u} l Ω H) (pbcFiniteFieldInclusion l Ω k) T).map
          ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F)
            (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T).map
            (eqToHom hJ)) ≫
          fdIntegralOrdinaryBalancingMap l T Ω A h k o₁ o₂ o₃ K.obj ≫
          (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F)
            (pbcFiniteField.{u} l Ω H)
            ((pbcFiniteFieldInclusion l Ω k).comp
              (pbcFiniteFieldInclusion l Ω h)) T).map
            (eqToHom hJ.symm)) :
        (pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω G)
          (pbcFiniteField.{u} l Ω H) (pbcFiniteFieldInclusion l Ω k) T
          hdim.out hinv.out).obj
            ((pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω F)
              (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h) T
              hdim.out hinv.out).obj J) ⟶
        (pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω F)
          (pbcFiniteField.{u} l Ω H)
          ((pbcFiniteFieldInclusion l Ω k).comp
            (pbcFiniteFieldInclusion l Ω h)) T hdim.out hinv.out).obj J) =
      (pbcRationalScalarCompComponent l (pbcFiniteField.{u} l Ω F)
        (pbcFiniteField.{u} l Ω G) (pbcFiniteField.{u} l Ω H)
        (pbcFiniteFieldInclusion l Ω h) (pbcFiniteFieldInclusion l Ω k)
        T hdim.out hinv.out ⟨J⟩).hom := by
  have key : ∀ {X Y} (p : X = Y),
      (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω G) (pbcFiniteField.{u} l Ω H)
          (pbcFiniteFieldInclusion l Ω k) T).map
          ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
            (pbcFiniteFieldInclusion l Ω h) T).map (eqToHom p)) ≫
        (pbcAmbientScalarComp l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
          (pbcFiniteField.{u} l Ω H) (pbcFiniteFieldInclusion l Ω h)
          (pbcFiniteFieldInclusion l Ω k) T).hom.app Y ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω H)
          ((pbcFiniteFieldInclusion l Ω k).comp (pbcFiniteFieldInclusion l Ω h)) T).map
          (eqToHom p.symm) =
      (pbcAmbientScalarComp l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
          (pbcFiniteField.{u} l Ω H) (pbcFiniteFieldInclusion l Ω h)
          (pbcFiniteFieldInclusion l Ω k) T).hom.app X := by
    rintro X _ rfl
    simp
  rw [fdIntegralOrdinaryBalancing_core l T Ω _D _hl A h k o₁ o₂ o₃ K,
    pbcRationalScalarCompComponent, Functor.mapIso_hom]
  congr 1
  apply ObjectProperty.hom_ext
  exact key hJ

/-- The normalized integral balancing becomes precisely the PBC balancing and its
specified raw rational associator. J is the same integral object in the PBC presentation;
hJ identifies its underlying object with the canonical integral identity image.
Source: trace-function coefficient comparison, ordinary balancing clause, step 2
(blueprint: lem-fd-integral-inverse-scalar-cocycle).

Proof: the first conjunct is `fdIntegralOrdinaryBalancing_core`, the second is
`fdIntegralOrdinaryBalancing_rationalized`.
-/
theorem fdIntegralOrdinaryBalancing
    (_D : FiniteFieldDatum.{d}) (_hl : l ≠ _D.p) [IsNoetherian T]
    [hdim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [hinv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (A : ScalarCompletionAssociatorData.{u, u} l T)
    (h : F ≤ G) (k : G ≤ H)
    (o₁ : FdOrdinaryScalarTransport l Ω T h)
    (o₂ : FdOrdinaryScalarTransport l Ω T k)
    (o₃ : FdOrdinaryScalarTransport l Ω T (h.trans k))
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω F) T) :
    (fdIntegralOrdinaryBalancingMap l T Ω A h k o₁ o₂ o₃ K.obj =
      (pbcAmbientScalarComp l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
        (pbcFiniteField.{u} l Ω H) (pbcFiniteFieldInclusion l Ω h) (pbcFiniteFieldInclusion l Ω k)
        T).hom.app
        ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω F)).obj K.obj)) ∧
    ∀ (J : PbcBoundedConstructibleComplete T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω F)))
      (hJ : J.obj = (integralDetailedTransport T l (pbcFiniteField.{u} l Ω F)).obj K.obj),
      (pbcRationalization T (pbcIntegralDatum l (pbcFiniteField.{u} l Ω H)) (pbcUniformizer l
        (pbcFiniteField.{u} l Ω H))).map
        (ObjectProperty.homMk
          ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω G) (pbcFiniteField.{u} l Ω H)
            (pbcFiniteFieldInclusion l Ω k) T).map ((pbcEmbeddingAmbientTensor l
            (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h)
            T).map (eqToHom hJ)) ≫
            fdIntegralOrdinaryBalancingMap l T Ω A h k o₁ o₂ o₃ K.obj ≫
            (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω H)
              ((pbcFiniteFieldInclusion l Ω k).comp (pbcFiniteFieldInclusion l Ω h)) T).map
              (eqToHom hJ.symm)) :
          (pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω G) (pbcFiniteField.{u} l Ω H)
            (pbcFiniteFieldInclusion l Ω k) T hdim.out hinv.out).obj
              ((pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
                (pbcFiniteFieldInclusion l Ω h) T hdim.out hinv.out).obj J) ⟶
            (pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω H)
              ((pbcFiniteFieldInclusion l Ω k).comp (pbcFiniteFieldInclusion l Ω h)) T hdim.out
              hinv.out).obj J) =
      (pbcRationalScalarCompComponent l (pbcFiniteField.{u} l Ω F) (pbcFiniteField.{u} l Ω G)
        (pbcFiniteField.{u} l Ω H) (pbcFiniteFieldInclusion l Ω h) (pbcFiniteFieldInclusion l Ω k)
        T hdim.out hinv.out ⟨J⟩).hom := by
  refine ⟨fdIntegralOrdinaryBalancing_core l T Ω _D _hl A h k o₁ o₂ o₃ K, ?_⟩
  intro J hJ
  exact fdIntegralOrdinaryBalancing_rationalized l T Ω _D _hl A h k o₁ o₂ o₃ K J hJ

end Presentation
end WeilConjectures
