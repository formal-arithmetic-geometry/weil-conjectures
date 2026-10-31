/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportCoefficientMateNormalization
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.NormalizedDVRTower
public import WeilConjectures.SixFunctors.FiniteDualizing
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.CompactSupportNativeSystemEvaluation
public import WeilConjectures.AlgebraicGeometry.CompactSupportReductionTowerData
public import WeilConjectures.AlgebraicGeometry.PointSectionsDerivedReductionData
public import WeilConjectures.SecSmoothPurity.ReductionDirectImageComparison
public import WeilConjectures.SecSmoothPurity.IntrinsicCompactSupportRestriction
public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import WeilConjectures.SecSmoothPurity.ReductionExceptional
import WeilConjectures.SixFunctors.CoefDualizingConstruction
import WeilConjectures.AlgebraicGeometry.CompactSupportNativeSystemTransition
import all WeilConjectures.AlgebraicGeometry.CompactSupportFiniteAction
import all WeilConjectures.AlgebraicGeometry.CoefficientSequenceRoosModel
import WeilConjectures.AlgebraicGeometry.EtaleProEtaleCompactScalarSquare
import all WeilConjectures.AlgebraicGeometry.EtaleCompactSupportCoefficientChange

/-! # Evaluated compact support and scalar-adjunction transitions

Source: blueprint `prop-coef-integral-dualizing.proof.md`, paragraph 2,
specified finite maps before limits (blueprint: lem-coef-dualizing-support-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.DualizingSupportEvaluation

private theorem transpose_conjugation
    {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (F : A ⥤ C) (G : B ⥤ D)
    (c : F ⋙ L' ⟶ L ⋙ G) {M W : A} {N Z : B}
    (s : M ⟶ R.obj N) (t : W ⟶ R.obj Z) (i : M ≅ W) (j : N ≅ Z)
    (h : s ≫ R.map j.hom = i.hom ≫ t) :
    b.unit.app (F.obj M) ≫ R'.map (c.app M ≫ G.map ((a.homEquiv _ _).symm s)) =
      F.map i.hom ≫ b.unit.app (F.obj W) ≫
        R'.map (c.app W ≫ G.map ((a.homEquiv _ _).symm t)) ≫ R'.map (G.map j.inv) := by
  have ht : (a.homEquiv _ _).symm s ≫ j.hom =
      L.map i.hom ≫ (a.homEquiv _ _).symm t := by
    rw [← a.homEquiv_naturality_right_symm, ← a.homEquiv_naturality_left_symm, h]
  have hs : (a.homEquiv _ _).symm s =
      L.map i.hom ≫ (a.homEquiv _ _).symm t ≫ j.inv := by
    simpa only [Category.assoc, j.hom_inv_id, Category.comp_id] using
      congrArg (fun f ↦ f ≫ j.inv) ht
  have hc := c.naturality i.hom
  change L'.map (F.map i.hom) ≫ c.app W = c.app M ≫ G.map (L.map i.hom) at hc
  have hR := congrArg R'.map hc
  simp only [Functor.map_comp] at hR
  rw [hs]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hR, ← b.unit_naturality_assoc (F.map i.hom)]

private theorem conjugate_identity
    {C : Type*} [Category C] {M N : C} (e : M ≅ N)
    (t : M ⟶ M) (d : N ⟶ N) (hs : t ≫ e.hom = e.hom ≫ d) (ht : t = 𝟙 M) :
    d = 𝟙 N := by
  apply (cancel_epi e.hom).mp
  rw [← hs, ht, Category.id_comp, Category.comp_id]

private theorem conjugate_composition
    {C : Type*} [Category C] {A₀ A₁ A₂ B₀ B₁ B₂ : C}
    (e₀ : A₀ ≅ B₀) (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂)
    (t₀₁ : A₀ ⟶ A₁) (t₁₂ : A₁ ⟶ A₂) (t₀₂ : A₀ ⟶ A₂)
    (d₀₁ : B₀ ⟶ B₁) (d₁₂ : B₁ ⟶ B₂) (d₀₂ : B₀ ⟶ B₂)
    (h₀₁ : t₀₁ ≫ e₁.hom = e₀.hom ≫ d₀₁)
    (h₁₂ : t₁₂ ≫ e₂.hom = e₁.hom ≫ d₁₂)
    (h₀₂ : t₀₂ ≫ e₂.hom = e₀.hom ≫ d₀₂)
    (ht : t₀₁ ≫ t₁₂ = t₀₂) : d₀₁ ≫ d₁₂ = d₀₂ := by
  apply (cancel_epi e₀.hom).mp
  rw [← Category.assoc, ← h₀₁, Category.assoc, ← h₁₂, ← Category.assoc, ht, h₀₂]

private theorem transport_unit
    {C : Type*} [Category C] (R : C ⥤ C) (u : R ≅ 𝟭 C)
    {M N : C} (e : M ≅ N) (t : M ⟶ R.obj M) (d : N ⟶ R.obj N)
    (hs : t ≫ R.map e.hom = e.hom ≫ d)
    (ht : t ≫ u.hom.app M = 𝟙 M) : d ≫ u.hom.app N = 𝟙 N := by
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, ← hs, Category.assoc, u.hom.naturality]
  change t ≫ u.hom.app M ≫ e.hom = e.hom ≫ 𝟙 N
  rw [← Category.assoc, ht, Category.id_comp, Category.comp_id]

private theorem transport_comp
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    (R₀₁ : C₁ ⥤ C₀) (R₁₂ : C₂ ⥤ C₁) (R₀₂ : C₂ ⥤ C₀)
    (μ : R₁₂ ⋙ R₀₁ ≅ R₀₂)
    {M₀ N₀ : C₀} {M₁ N₁ : C₁} {M₂ N₂ : C₂}
    (e₀ : M₀ ≅ N₀) (e₁ : M₁ ≅ N₁) (e₂ : M₂ ≅ N₂)
    (t₀₁ : M₀ ⟶ R₀₁.obj M₁) (t₁₂ : M₁ ⟶ R₁₂.obj M₂) (t₀₂ : M₀ ⟶ R₀₂.obj M₂)
    (d₀₁ : N₀ ⟶ R₀₁.obj N₁) (d₁₂ : N₁ ⟶ R₁₂.obj N₂) (d₀₂ : N₀ ⟶ R₀₂.obj N₂)
    (h₀₁ : t₀₁ ≫ R₀₁.map e₁.hom = e₀.hom ≫ d₀₁)
    (h₁₂ : t₁₂ ≫ R₁₂.map e₂.hom = e₁.hom ≫ d₁₂)
    (h₀₂ : t₀₂ ≫ R₀₂.map e₂.hom = e₀.hom ≫ d₀₂)
    (ht : t₀₂ ≫ μ.inv.app M₂ = t₀₁ ≫ R₀₁.map t₁₂) :
    d₀₁ ≫ R₀₁.map d₁₂ ≫ μ.hom.app N₂ = d₀₂ := by
  have hμ := μ.hom.naturality e₂.hom
  change R₀₁.map (R₁₂.map e₂.hom) ≫ μ.hom.app N₂ =
    μ.hom.app M₂ ≫ R₀₂.map e₂.hom at hμ
  apply (cancel_epi e₀.hom).mp
  simp only [← Category.assoc]
  rw [← h₀₁]
  simp only [Category.assoc]
  rw [← R₀₁.map_comp_assoc, ← h₁₂, R₀₁.map_comp, Category.assoc, hμ]
  rw [← Category.assoc, ← Category.assoc, ← ht]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact h₀₂

private theorem move_iso_square
    {A B : Type*} [Category A] [Category B]
    (R R' : B ⥤ A) (e : R ≅ R') {M P : A} {N Q : B}
    (t : M ⟶ R.obj N) (d : P ⟶ R'.obj Q) (u : M ≅ P) (v : N ≅ Q)
    (hg : (t ≫ e.hom.app N) ≫ R'.map v.hom = u.hom ≫ d) :
    t ≫ R.map v.hom = u.hom ≫ (d ≫ e.inv.app Q) := by
  apply (cancel_mono (e.hom.app Q)).mp
  rw [Category.assoc, e.hom.naturality]
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hg

private theorem completed_square_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    (R : B ⥤ A) (S : A ⥤ C) (T : B ⥤ C) (μ : R ⋙ S ⟶ T)
    {M₀ N₀ : A} {M₁ N₁ : B} {P Q : C}
    (e₀ : M₀ ⟶ N₀) (e₁ : M₁ ⟶ N₁) (t : M₀ ⟶ R.obj M₁)
    (d : N₀ ⟶ R.obj N₁) (q₀ : P ⟶ S.obj M₀) (q₁ : Q ⟶ T.obj M₁)
    (tc : P ⟶ Q)
    (ht : tc ≫ q₁ = q₀ ≫ S.map t ≫ μ.app M₁)
    (hs : t ≫ R.map e₁ = e₀ ≫ d) :
    tc ≫ q₁ ≫ T.map e₁ =
      q₀ ≫ S.map e₀ ≫ S.map d ≫ μ.app N₁ := by
  rw [← Category.assoc, ht]
  simp only [Category.assoc]
  rw [← μ.naturality]
  change q₀ ≫ S.map t ≫ S.map (R.map e₁) ≫ μ.app N₁ = _
  rw [← S.map_comp_assoc, hs, S.map_comp, Category.assoc]

private theorem exact_map_square
    {C A B D : Type*} [Category C] [Category A] [Category B] [Category D]
    [Abelian C] [Abelian A] [Abelian B] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory D]
    (U : C ⥤ A) (F F' : A ⥤ B) (G G' : C ⥤ D) (R : D ⥤ B)
    [U.Additive] [F.Additive] [F'.Additive] [G.Additive] [G'.Additive] [R.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (e₀ : U ⋙ F ≅ G ⋙ R) (e₁ : U ⋙ F' ≅ G' ⋙ R)
    (τ : F ⟶ F') (γ : G ⟶ G')
    (hc : ∀ M, τ.app (U.obj M) ≫ e₁.hom.app M = e₀.hom.app M ≫ R.map (γ.app M))
    (X : DerivedCategory C) :
    (derivedMap F F' τ).app (U.mapDerivedCategory.obj X) ≫
        (Functor.mapDerivedCategorySquareIso e₁).hom.app X =
      (Functor.mapDerivedCategorySquareIso e₀).hom.app X ≫
        R.mapDerivedCategory.map ((derivedMap G G' γ).app X) := by
  suffices hh : Functor.whiskerLeft U.mapDerivedCategory (derivedMap F F' τ) ≫
      (derivedEvaluationIso U F' G' R e₁).hom =
      (derivedEvaluationIso U F G R e₀).hom ≫
        Functor.whiskerRight (derivedMap G G' γ) R.mapDerivedCategory by
    simpa only [derivedEvaluationIso, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] using congr_app hh X
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  apply (cancel_mono (R.mapDerivedCategory.map (G'.mapDerivedCategoryFactors.hom.app K) ≫
    R.mapDerivedCategoryFactors.hom.app ((G'.mapHomologicalComplex (.up ℤ)).obj K))).mp
  simp only [Category.assoc]
  rw [derivedEvaluationIso_fac]
  have hn := (derivedMap F F' τ).naturality (U.mapDerivedCategoryFactors.hom.app K)
  rw [← reassoc_of% hn, derivedMap_fac_assoc]
  rw [← R.mapDerivedCategory.map_comp_assoc, derivedMap_fac]
  rw [R.mapDerivedCategory.map_comp]
  have hnR := R.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex γ (.up ℤ)).app K)
  dsimp only [Functor.comp_map] at hnR
  rw [Category.assoc, hnR, derivedEvaluationIso_fac_assoc]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 3
  ext i
  exact hc _

private theorem mapped_pasting
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {K : D} {M₀ M₁ M₂ M₃ M₄ M₅ Z : C} (q : K ⟶ F.obj M₀)
    (t : M₀ ⟶ M₁) (e₁ : M₁ ⟶ M₂) (v₁ : M₂ ⟶ Z)
    (e₀ : M₀ ⟶ M₃) (v₀ : M₃ ⟶ M₄) (d : M₄ ⟶ M₅) (μ : M₅ ⟶ Z)
    (h : t ≫ e₁ ≫ v₁ = e₀ ≫ v₀ ≫ d ≫ μ) :
    (q ≫ F.map t) ≫ F.map (e₁ ≫ v₁) =
      (q ≫ F.map (e₀ ≫ v₀)) ≫ F.map d ≫ F.map μ := by
  simpa only [F.map_comp, Category.assoc] using congrArg (fun k ↦ q ≫ F.map k) h

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary compact support on the whole sequence site, with j_! exact and Rp_*
derived on systems. Source: blueprint paragraph 2, before limits
(blueprint: lem-coef-dualizing-support-evaluation). -/
def support {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a) :
    coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y :=
  ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i ⋙
      ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g

/-- Exact final-object sections on strict towers, with constant integral action.
Source: blueprint paragraph 2; Stacks 03CW
(blueprint: lem-coef-dualizing-support-evaluation). -/
abbrev sectionsTowers :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pointIntegralSections l E D.k)

/-- Exactness at kernels is levelwise. Source: Stacks 03CW, 0941
(blueprint: lem-coef-dualizing-support-evaluation). -/
instance sectionsTowersLimits : PreservesFiniteLimits (sectionsTowers D l E) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Exactness at cokernels is levelwise. Source: Stacks 03CW, 0941
(blueprint: lem-coef-dualizing-support-evaluation). -/
instance sectionsTowersColimits : PreservesFiniteColimits (sectionsTowers D l E) where
  preservesFiniteColimits _ _ _ := inferInstance

/-- The ordinary derived category of constant-R module towers, with no inverse limit.
Source: blueprint paragraph 2; Stacks 05RU, 0941
(blueprint: lem-coef-dualizing-support-evaluation). -/
instance towerHasDerived : HasDerivedCategory
    (ℕᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  HasDerivedCategory.standard _

/-- B(Q): derive proper image first, then point sections on the entire tower.
The completed restriction is only an intermediate presentation: pointIntegralSections
restricts along the actual constant map R to the completed section ring. Its composite
at level n is the actual R to A_(n+1) restriction. No inverse limit is used.
Source: blueprint paragraph 2 (blueprint: lem-coef-dualizing-support-evaluation). -/
def B {X : Scheme.{u}} {a : X ⟶ Spec (.of D.k)} (c : Compactification a) :=
  support l E c ⋙ coefficientSequenceDerivedRestriction l E (Spec (.of D.k)) ⋙
    (sectionsTowers D l E).mapDerivedCategory

/-- Exact evaluation in the ordinary derived tower category.
Source: Stacks 0941 (blueprint: lem-coef-dualizing-support-evaluation). -/
abbrev ev (n : ℕ) :=
  ((evaluation ℕᵒᵖ (ModuleCat.{u + 1}
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).obj (op n)).mapDerivedCategory

/-- The actual localized horizontal map of a strict R-module tower.
Source: Stacks 0941 (blueprint: lem-coef-dualizing-support-evaluation). -/
def transition {m n : ℕ} (h : n ≤ m) : ev l E m ⟶ ev l E n :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) (.up ℤ)) _ _ _ _
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex
      ((evaluation ℕᵒᵖ (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).map (homOfLE h).op)
      (.up ℤ)) DerivedCategory.Q)

/-- Final-object sections of a finite-level complex, with the actual constant R action.
Source: blueprint paragraph 2; Stacks 03CW
(blueprint: lem-coef-dualizing-support-evaluation). -/
def sections (n : ℕ) :=
  coefficientFiniteDerivedRestriction l E (Spec (.of D.k)) n ⋙
    (pointIntegralSections l E D.k).mapDerivedCategory

/-- The canonical change from the identified-ring direct image to sectionwise direct
image. Both models use exactly the same constant-section structure map.
Source: Stacks 03D2, 0D6E (blueprint: lem-coef-dualizing-support-evaluation). -/
def supportModel {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    (A : Type u) [CommRing A] [Finite A] :
    reductionCompactSupport A c.i c.g ≅ sfIntrinsicCompactSupport c A :=
  Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
    (eqToIso (AlgebraicGeometry.ProEtale.reductionConstantPush_eq A c.g))

/-- c is the proper coefficient mate followed by the exact open coefficient map,
transported only by the specified direct-image presentation.
Source: blueprint paragraph 2; Stacks 0GL1, 0D6E
(blueprint: lem-coef-dualizing-support-evaluation). -/
def comparison {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    {m n : ℕ} (h : n ≤ m) :
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1)) ⋙
        scalarExtensionFunctor (compactSupportLevelQuotient l E m n h) Y ⟶
      scalarExtensionFunctor (compactSupportLevelQuotient l E m n h) X ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) :=
  coefficientMateComparison l E c h

/-- Exact quotient restriction in the two published coefficient presentations.
Source: Stacks 03DA, 0941 (blueprint: lem-coef-dualizing-support-evaluation). -/
def quotientRestrictionModel (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes l E X h ≅
      scalarRestriction (compactSupportLevelQuotient l E m n h) X :=
  by
    letI := proEtaleRingRestrictScalars_preservesFiniteLimits
      (proEtaleConstantRingMap (T := X) (compactSupportLevelQuotient l E m n h))
    letI := proEtaleRingRestrictScalars_preservesFiniteColimits
      (proEtaleConstantRingMap (T := X) (compactSupportLevelQuotient l E m n h))
    exact Functor.mapDerivedCategoryNatIso (eqToIso (by
      rw [finiteDualizingRestriction_eq l E X h]
      rfl))

/-- The actual sequence-site transition, transported to constant quotient restriction.
Source: Stacks 0941, blueprint paragraph 2
(blueprint: lem-coef-dualizing-support-evaluation). -/
def sigma (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (Q : coefficientSequenceDerived l E X) :=
  (coefficientSequenceDerivedTransition l E X h).app Q ≫
    (quotientRestrictionModel l E X h).hom.app
      ((coefficientSequenceDerivedEvaluation l E X n).obj Q)

/-- alpha is the tensor-restriction adjunct of the actual horizontal transition.
Source: blueprint paragraph 2; Stacks 07A6
(blueprint: lem-coef-dualizing-support-evaluation). -/
def alpha (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (Q : coefficientSequenceDerived l E X) :=
  ((proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := X) (compactSupportLevelQuotient l E m n h))).homEquiv
      _ _).symm (sigma l E X h Q)

/-- The specified restriction-form arrow eta followed by Res(F_n(alpha) c).
Source: blueprint paragraph 2, displayed d (blueprint: lem-coef-dualizing-support-evaluation). -/
def d {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    {m n : ℕ} (h : n ≤ m) (Q : coefficientSequenceDerived l E X) :=
  coefficientMateRestrictionArrow l E c h (sigma l E X h Q)

/-- R Gamma(s,d), with the canonical composition of quotient and constant-R restrictions.
Source: blueprint paragraph 2 (blueprint: lem-coef-dualizing-support-evaluation). -/
def sectionTransition {X : Scheme.{u}} {a : X ⟶ Spec (.of D.k)}
    (c : Compactification a) {m n : ℕ} (h : n ≤ m)
    (Q : coefficientSequenceDerived l E X) :=
  (sections D l E m).map (d l E c h Q) ≫
    (pointIntegralSections l E D.k).mapDerivedCategory.map
      ((compactSupportRestrictionComp l E (Spec (.of D.k)) m n h).hom.app
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
          ((coefficientSequenceDerivedEvaluation l E X n).obj Q)))

/-- The finite-level target of Theta, as a functor on the entire derived input category.
Source: blueprint paragraph 2 (blueprint: lem-coef-dualizing-support-evaluation). -/
def target {X : Scheme.{u}} {a : X ⟶ Spec (.of D.k)} (c : Compactification a) (n : ℕ) :=
  coefficientSequenceDerivedEvaluation l E X n ⋙
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) ⋙ sections D l E n

/-- The canonical evaluation of point sections on a whole strict tower.
Source: Stacks 03CW, 0941 (blueprint: lem-coef-dualizing-support-evaluation). -/
def sectionsEvaluation (n : ℕ) :
    (sectionsTowers D l E).mapDerivedCategory ⋙ ev l E n ≅
      coefficientConstantTowerEvaluation l E (Spec (.of D.k)) n ⋙
        (pointIntegralSections l E D.k).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (Iso.refl _)

/-- Theta is assembled from actual point, quotient, proper and open evaluations.
Source: blueprint paragraph 2 (blueprint: lem-coef-dualizing-support-evaluation). -/
def theta {X : Scheme.{u}} {a : X ⟶ Spec (.of D.k)}
    (c : Compactification a) (n : ℕ) : B D l E c ⋙ ev l E n ≅ target D l E c n := by
  let i₁ := Functor.isoWhiskerLeft
    (support l E c ⋙ coefficientSequenceDerivedRestriction l E (Spec (.of D.k)))
    (sectionsEvaluation D l E n)
  let i₂ := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (support l E c)
      (coefficientRestrictedEvaluationIso l E (Spec (.of D.k)) n))
    (pointIntegralSections l E D.k).mapDerivedCategory
  let i₃ := Functor.isoWhiskerRight (compactSupportSystemEvaluation l E c n)
    (sections D l E n)
  exact Functor.associator _ _ _ ≪≫ i₁ ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫ i₂ ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ i₃ ≪≫ Functor.associator _ _ _

/-- The same d arrow in the published coherent quotient-restriction coordinates.
Only the canonical restriction-presentation isomorphism is applied.
Source: blueprint paragraph 2 (blueprint: lem-coef-dualizing-support-evaluation). -/
def dNormalized {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    {m n : ℕ} (h : n ≤ m) (Q : coefficientSequenceDerived l E X) :=
  d l E c h Q ≫ (quotientRestrictionModel l E Y h).inv.app
    ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
      ((coefficientSequenceDerivedEvaluation l E X n).obj Q))

/-- The counit-defined finite-dualizing transition in the actual quotient coordinates.
Source: lem-coef-finite-dualizing, finite pro-etale realization
(blueprint: lem-coef-dualizing-support-evaluation). -/
def dualizingTransition (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m) :=
  integralDualizingExceptionalTransition l E D X hl h ≫
    (quotientRestrictionModel l E X h).hom.app (integralDualizingFiniteTerm l E D X n)

/-- The finite-dualizing site square: the transported actual proper/open coefficient
map equals the etale comparison after canonical scalar and site identifications.
Only lower-bound witnesses are existential, not maps or complexes.
Source: blueprint paragraph 2, finite counit maps
(blueprint: lem-coef-dualizing-support-evaluation). -/
def DualizingSiteCompatibility (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k))) {m n : ℕ} (h : n ≤ m) : Prop :=
  ∃ hL : DerivedCategory.TStructure.t.plus (finiteDualizingEtaleTerm l E D X m),
    ∃ hLB : DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension (finiteDualizingQuotient l E h) X).obj
        (finiteDualizingEtaleTerm l E D X m)),
    (CoefficientCompatibility.liftedScalarExtension
      (compactSupportLevelQuotient l E m n h) (Spec (.of D.k))).map
      ((compactSupportSiteComparison (finiteDualizingCoeff l E m) c).inv.app
        ⟨finiteDualizingEtaleTerm l E D X m, hL⟩) ≫
      (CoefficientCompatibility.transportedRecordedReductionDirectImageComparison
        (compactSupportLevelQuotient l E m n h) c
        (reductionDirectImageComparison (compactSupportLevelQuotient l E m n h)
          c.i c.g)).app
        ((comparisonUpperStar
          (ModuleCat.{u + 1} (finiteDualizingCoeff l E m)) X).mapDerivedCategory.obj
            (finiteDualizingEtaleTerm l E D X m)) ≫
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c).map
        ((pbcComparisonReduction X (finiteDualizingQuotient l E h)).hom.app
          (finiteDualizingEtaleTerm l E D X m)) =
    (pbcComparisonReduction (Spec (.of D.k)) (finiteDualizingQuotient l E h)).hom.app
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E m)) c).obj
          (finiteDualizingEtaleTerm l E D X m)) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
        (Spec (.of D.k))).mapDerivedCategory.map
        (Etale.ExceptionalCoefficients.compactSupportMap (finiteDualizingQuotient l E h)
          c (finiteDualizingEtaleTerm l E D X m)) ≫
      (compactSupportSiteComparison (finiteDualizingCoeff l E n) c).inv.app
        ⟨(Etale.scalarExtension (finiteDualizingQuotient l E h) X).obj
          (finiteDualizingEtaleTerm l E D X m), hLB⟩

section TowerProofs

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
attribute [local implicit_reducible] SemilinearSections.moduleAbelian
  SemilinearSections.hasDerived coefficientSequenceHasDerived
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientFiniteDerivedRestriction scalarReductionDerivedRestriction
  coefficientConstantTowerEvaluation coefficientFiniteHasDerived
  scalarReductionSourceDerived scalarReductionTargetDerived
  reductionModulesHasDerivedCategory proEtaleRingModules_hasDerivedCategory
  compactSupportSystemLevel compactSupportSystemQuotient
  ProEtale.VaryingRing.coefficientTransition coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition
  sections target support B sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat

private theorem d_restriction {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) {m n : ℕ} (h : n ≤ m)
    (Q : coefficientSequenceDerived l E X) :
    d l E c h Q =
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map
        (sigma l E X h Q) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        ((coefficientSequenceDerivedEvaluation l E X n).obj Q) := by
  exact compactSupportCoefficientMateNormalization l E c h (sigma l E X h Q)

private theorem sigma_direct (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (Q : coefficientSequenceDerived l E X) :
    sigma l E X h Q = (compactSupportCoefficientTransition l E X h).app Q := by
  have he : quotientRestrictionModel l E X h = finiteRestrictionIso l E X h := by rfl
  simpa only [sigma, he, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj,
    scalarRestriction, proEtaleCoefficientRestrictScalars,
    proEtaleConstantRingMap] using
    NatTrans.congr_app (derivedTransition_direct l E X h) Q

private theorem support_square {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) {m n : ℕ} (h : n ≤ m)
    (Q : coefficientSequenceDerived l E X) :
    (coefficientSequenceDerivedTransition l E Y h).app ((support l E c).obj Q) ≫
      (normalizedDVRRes l E Y h).map ((compactSupportSystemEvaluation l E c n).hom.app Q) =
    (compactSupportSystemEvaluation l E c m).hom.app Q ≫ dNormalized l E c h Q := by
  have hg := compactSupportNativeSystemTransition l E c h Q
  erw [← sigma_direct l E Y h, ← sigma_direct l E X h] at hg
  erw [← d_restriction l E c h Q] at hg
  exact move_iso_square (normalizedDVRRes l E Y h)
    (scalarRestriction (compactSupportLevelQuotient l E m n h) Y)
    (quotientRestrictionModel l E Y h) _ (d l E c h Q)
    ((compactSupportSystemEvaluation l E c m).app Q)
    ((compactSupportSystemEvaluation l E c n).app Q) hg

private theorem transition_id (n : ℕ) : transition l E (le_refl n) = 𝟙 _ := by
  unfold transition
  simp only [homOfLE_refl, op_id]
  erw [CategoryTheory.Functor.map_id]
  simp only [NatTrans.mapHomologicalComplex_id, Functor.whiskerRight_id',
    Localization.liftNatTrans_id]

private theorem transition_comp {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    transition l E hrm ≫ transition l E hmn = transition l E (hmn.trans hrm) := by
  simp only [transition, Localization.comp_liftNatTrans]
  congr 1
  rw [← Functor.whiskerRight_comp, ← NatTrans.mapHomologicalComplex_comp,
    ← Functor.map_comp]
  rfl

private theorem point_sections_square {m n : ℕ} (h : n ≤ m)
    (Q : DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of D.k)))) :
    (transition l E h).app ((sectionsTowers D l E).mapDerivedCategory.obj Q) ≫
      (sectionsEvaluation D l E n).hom.app Q =
    (sectionsEvaluation D l E m).hom.app Q ≫
      (pointIntegralSections l E D.k).mapDerivedCategory.map
        ((pbcTowerTransition (Spec (.of D.k))
          (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) m n h).app Q) := by
  let A := scalarReductionSource l E (Spec (.of D.k))
  let B := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
  have H := exact_map_square (sectionsTowers D l E)
    ((evaluation ℕᵒᵖ B).obj (op m)) ((evaluation ℕᵒᵖ B).obj (op n))
    ((evaluation ℕᵒᵖ A).obj (op m)) ((evaluation ℕᵒᵖ A).obj (op n))
    (pointIntegralSections l E D.k)
    (Iso.refl _) (Iso.refl _)
    ((evaluation ℕᵒᵖ B).map (homOfLE h).op)
    ((evaluation ℕᵒᵖ A).map (homOfLE h).op) (by
      intro M
      simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
      rfl) Q
  simpa only [derivedMap, sectionsEvaluation, transition, pbcTowerTransition] using H

private theorem completed_support_square {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) {m n : ℕ} (h : n ≤ m)
    (Q : coefficientSequenceDerived l E X) :
    (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y) m n h).app
        ((coefficientSequenceDerivedRestriction l E Y).obj ((support l E c).obj Q)) ≫
      (coefficientRestrictedEvaluationIso l E Y n).hom.app ((support l E c).obj Q) ≫
      (coefficientFiniteDerivedRestriction l E Y n).map
        ((compactSupportSystemEvaluation l E c n).hom.app Q) =
    (coefficientRestrictedEvaluationIso l E Y m).hom.app ((support l E c).obj Q) ≫
      (coefficientFiniteDerivedRestriction l E Y m).map
        ((compactSupportSystemEvaluation l E c m).hom.app Q) ≫
      (coefficientFiniteDerivedRestriction l E Y m).map (d l E c h Q) ≫
      (compactSupportRestrictionComp l E Y m n h).hom.app
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
          ((coefficientSequenceDerivedEvaluation l E X n).obj Q)) := by
  have ht := compactSupportCoefficientTransition_restricted l E Y h ((support l E c).obj Q)
  have hg := compactSupportNativeSystemTransition l E c h Q
  erw [← sigma_direct l E X h] at hg
  erw [← d_restriction l E c h Q] at hg
  exact completed_square_transport
    (scalarRestriction (compactSupportLevelQuotient l E m n h) Y)
    (coefficientFiniteDerivedRestriction l E Y m)
    (coefficientFiniteDerivedRestriction l E Y n)
    (compactSupportRestrictionComp l E Y m n h).hom
    ((compactSupportSystemEvaluation l E c m).hom.app Q)
    ((compactSupportSystemEvaluation l E c n).hom.app Q)
    _ (d l E c h Q) _ _ _ ht hg

private theorem theta_hom {X : Scheme.{u}} {a : X ⟶ Spec (.of D.k)}
    (c : Compactification a) (n : ℕ) (Q : coefficientSequenceDerived l E X) :
    (theta D l E c n).hom.app Q =
      (sectionsEvaluation D l E n).hom.app
          ((coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).obj
            ((support l E c).obj Q)) ≫
        (pointIntegralSections l E D.k).mapDerivedCategory.map
          ((coefficientRestrictedEvaluationIso l E (Spec (.of D.k)) n).hom.app
              ((support l E c).obj Q) ≫
            (coefficientFiniteDerivedRestriction l E (Spec (.of D.k)) n).map
              ((compactSupportSystemEvaluation l E c n).hom.app Q)) := by
  let S := (pointIntegralSections l E D.k).mapDerivedCategory
  let R := coefficientFiniteDerivedRestriction l E (Spec (.of D.k)) n
  let e := (coefficientRestrictedEvaluationIso l E (Spec (.of D.k)) n).hom.app
    ((support l E c).obj Q)
  let v := (compactSupportSystemEvaluation l E c n).hom.app Q
  let q := (sectionsEvaluation D l E n).hom.app
    ((coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).obj ((support l E c).obj Q))
  change 𝟙 _ ≫ q ≫ 𝟙 _ ≫ S.map (𝟙 _) ≫ S.map e ≫ S.map (𝟙 _) ≫
    𝟙 _ ≫ (S.map (R.map v) ≫ 𝟙 _) = q ≫ S.map (e ≫ R.map v)
  rw [S.map_id, S.map_id]
  simp only [Category.id_comp, Category.comp_id, S.map_comp]
  erw [Category.id_comp]

private theorem evaluated_square {X : Scheme.{u}} {a : X ⟶ Spec (.of D.k)}
    (c : Compactification a) {m n : ℕ} (h : n ≤ m)
    (Q : coefficientSequenceDerived l E X) :
    (transition l E h).app ((B D l E c).obj Q) ≫ (theta D l E c n).hom.app Q =
      (theta D l E c m).hom.app Q ≫ sectionTransition D l E c h Q := by
  dsimp only [B, Functor.comp_obj]
  rw [theta_hom, theta_hom, ← Category.assoc]
  erw [point_sections_square]
  exact mapped_pasting (pointIntegralSections l E D.k).mapDerivedCategory
    ((sectionsEvaluation D l E m).hom.app
      ((coefficientSequenceDerivedRestriction l E (Spec (.of D.k))).obj
        ((support l E c).obj Q)))
    _ _ _ _ _ _ _ (completed_support_square l E c h Q)

end TowerProofs

section SiteProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

private theorem dualizing_etale_plus (hl : l ≠ D.p) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] (m : ℕ) :
    DerivedCategory.TStructure.t.plus (finiteDualizingEtaleTerm l E D X m) := by
  have hbc : Etale.DerivedCategory.isBoundedConstructible
      (finiteDualizingCoeff l E m) X (finiteDualizingEtaleTerm l E D X m) :=
    (Etale.coefDualizingConstruction D l hl E X ⟨m + 1, Nat.succ_pos m⟩).2.2.1
  obtain ⟨a, b, _, hz⟩ := hbc.2
  exact ⟨a, (DerivedCategory.isGE_iff _ a).mpr fun i hi ↦ hz i (Or.inl hi)⟩

attribute [local irreducible] Etale.DerivedCategory.hasTorAmplitudeIn
  DerivedCategory.TStructure.t pbcFixedScalarExtension

private theorem dualizing_etale_tor (hl : l ≠ D.p) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] (m : ℕ) :
    ∃ a b : ℤ, a ≤ b ∧
      Etale.DerivedCategory.hasTorAmplitudeIn (finiteDualizingCoeff l E m) X a b
        (finiteDualizingEtaleTerm l E D X m) := by
  exact (Etale.coefDualizingConstruction D l hl E X
    ⟨m + 1, Nat.succ_pos m⟩).2.2.2

private theorem dualizing_scalar_plus (hl : l ≠ D.p) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    {m n : ℕ} (h : n ≤ m) :
    DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension (finiteDualizingQuotient l E h) X).obj
        (finiteDualizingEtaleTerm l E D X m)) := by
  obtain ⟨a, b, _, ht⟩ := dualizing_etale_tor D l E hl X m
  have ht' : Etale.DerivedCategory.hasTorAmplitudeIn (finiteDualizingCoeff l E m) X a b
      (finiteDualizingEtaleTerm l E D X m) := ht
  exact Etale.scalarExtension_plus_of_finiteTor
    (A := finiteDualizingCoeff l E m) (B := finiteDualizingCoeff l E n)
    (finiteDualizingQuotient l E h) X (finiteDualizingEtaleTerm l E D X m) a b ht'

attribute [local irreducible]
  CoefficientCompatibility.transportedRecordedReductionDirectImageComparison
  compactSupportSiteComparison comparisonUpperStar pbcComparisonReduction
  Etale.compactScalarMap Etale.ExceptionalCoefficients.compactSupportMap
  Functor.leftDerivedFunctor DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian

private theorem site_compatibility (hl : l ≠ D.p) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k))) {m n : ℕ} (h : n ≤ m) :
    DualizingSiteCompatibility D l E X c h := by
  have hL := dualizing_etale_plus D l E hl X m
  have hLB := dualizing_scalar_plus D l E hl X h
  refine ⟨hL, hLB, ?_⟩
  simpa only [Etale.compactScalarMap, CoefficientCompatibility.uliftRingHom,
    finiteDualizingQuotient, finiteDualizingQuotientBase, compactSupportLevelQuotient] using
    CoefficientCompatibility.transportedCompactScalar_site_square
      (compactSupportLevelQuotient l E m n h) c
      ⟨finiteDualizingEtaleTerm l E D X m, hL⟩ hLB

end SiteProof

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

attribute [local implicit_reducible] SemilinearSections.moduleAbelian
  SemilinearSections.hasDerived coefficientSequenceHasDerived
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientFiniteDerivedRestriction scalarReductionDerivedRestriction
  coefficientConstantTowerEvaluation coefficientFiniteHasDerived
  scalarReductionSourceDerived scalarReductionTargetDerived
  reductionModulesHasDerivedCategory proEtaleRingModules_hasDerivedCategory
  compactSupportSystemLevel compactSupportSystemQuotient
  ProEtale.VaryingRing.coefficientTransition coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition
  sections target support B sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat

attribute [local implicit_reducible] catToReflQuiver

private def quotientScalarAdjunction (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    scalarExtensionFunctor (compactSupportLevelQuotient l E m n h) T ⊣
      scalarRestriction (compactSupportLevelQuotient l E m n h) T :=
  proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := T) (compactSupportLevelQuotient l E m n h))

/-- Evaluated support, its scalar-unit formula, coherence, and finite-dualizing
normalization, for arbitrary unbounded strict derived inputs.

Source: blueprint prop-coef-integral-dualizing.proof.md, paragraph 2
(blueprint: lem-coef-dualizing-support-evaluation).
Proof:
1. Identify quotient-semilinear systems with modules on the vertical sequence site
(def-coef-ringed-sequence-site). Semilinear derived sections gives proper evaluation;
exact open extension gives open evaluation, without evaluated K-injectivity.
2. The open transition is j_!(alpha) after the normalized open tensor map: its
adjunction transpose is j_!(sigma). Paste with the proper coefficient mate to get c
(lem-fix-open-scalar-tensor-normalization, lem-coef-semilinear-derived-sections).
3. Transpose by derived tensor-restriction adjunction: the restriction arrow is
eta followed by Res(F_n(alpha)c), with no quotient-flatness assumption
(lem-pur-sheaf-ring-derived-coefficient-adjunction).
4. Mate pasting identifies the transpose of c with rho F(eta); naturality at alpha
then gives d=rho F(sigma) (lem-sf-compact-support-restriction-of-scalars,
def-coef-compact-support-tensor-comparison, lem-weil-pbc-mate-pasting).
5. Derive point sections separately on systems. Its evaluation and the exact
constant-R restriction give theta and the section-transition equation. Neither
operation takes an inverse limit (lem-coef-semilinear-derived-sections).
6. Conjugate the actual strict tower identity and composition by theta. This proves
coherence of the specified transitions, without detecting equality by evaluations.
7. For omega, finite dualizing construction and finite Tor site comparison supply
bounded constructible etale origins for omega and its reduction/open extension
(lem-coef-dualizing-construction, det-pe-finite-tor-comparison-noetherian,
lem-fix-reduction-open-etale-origin, lem-weil-finite-duality-site-comparison).
8. The proper scalar-mate/site square and normalized open units identify c with the
finite realization of the etale compactSupportMap. Paste the scalar/pullback cube
and open exchange (lem-sfb-etale-proetale-scalar-mate,
lem-fix-open-scalar-tensor-normalization, lem-fix-site-open-exchange,
lem-sfb-etale-proetale-scalar-pullback-cube, lem-fix-compact-support-coefficient-change).
9. Substitute the counit-defined u using lem-coef-finite-dualizing. Conjugation by
the given level isomorphisms gives exactly the displayed specialized d formula.
All maps used are the named actual operations of Q and the fixed compactification.
-/
theorem evaluatedSupport (hl : l ≠ D.p) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k))) :
    (∀ (Q : coefficientSequenceDerived l E X) {m n : ℕ} (h : n ≤ m),
      (transition l E h).app ((B D l E c).obj Q) ≫ (theta D l E c n).hom.app Q =
        (theta D l E c m).hom.app Q ≫ sectionTransition D l E c h Q) ∧
    (∀ (Q : coefficientSequenceDerived l E X) {m n : ℕ} (h : n ≤ m),
      d l E c h Q =
        (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map
          (sigma l E X h Q) ≫
        (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
          ((coefficientSequenceDerivedEvaluation l E X n).obj Q)) ∧
    (∀ (Q : coefficientSequenceDerived l E X) (n : ℕ),
      sectionTransition D l E c (le_refl n) Q = 𝟙 _) ∧
    (∀ (Q : coefficientSequenceDerived l E X) {r m n : ℕ}
      (hrm : m ≤ r) (hmn : n ≤ m),
      sectionTransition D l E c hrm Q ≫ sectionTransition D l E c hmn Q =
        sectionTransition D l E c (hmn.trans hrm) Q) ∧
    (∀ (Q : coefficientSequenceDerived l E X) (n : ℕ),
      dNormalized l E c (le_refl n) Q ≫
        (normalizedDVRResUnit l E (Spec (.of D.k)) n).hom.app
          ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
            ((coefficientSequenceDerivedEvaluation l E X n).obj Q)) = 𝟙 _) ∧
    (∀ (Q : coefficientSequenceDerived l E X) {r m n : ℕ}
      (hrm : m ≤ r) (hmn : n ≤ m),
      dNormalized l E c hrm Q ≫
        (normalizedDVRRes l E (Spec (.of D.k)) hrm).map (dNormalized l E c hmn Q) ≫
        (normalizedDVRResComp l E (Spec (.of D.k)) hrm hmn).hom.app
          ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
            ((coefficientSequenceDerivedEvaluation l E X n).obj Q)) =
        dNormalized l E c (hmn.trans hrm) Q) ∧
    (∀ {m n : ℕ} (h : n ≤ m), DualizingSiteCompatibility D l E X c h) ∧
    (∀ (Q : coefficientSequenceDerived l E X) {m n : ℕ} (h : n ≤ m)
      (iₘ : (coefficientSequenceDerivedEvaluation l E X m).obj Q ≅
        integralDualizingFiniteTerm l E D X m)
      (iₙ : (coefficientSequenceDerivedEvaluation l E X n).obj Q ≅
        integralDualizingFiniteTerm l E D X n),
      sigma l E X h Q ≫
          (scalarRestriction (compactSupportLevelQuotient l E m n h) X).map iₙ.hom =
        iₘ.hom ≫ dualizingTransition D l E X hl h →
      d l E c h Q =
        (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map
            iₘ.hom ≫
          (proEtaleRingDerivedExtensionAdjunction
            (proEtaleConstantRingMap (T := Spec (.of D.k))
              (compactSupportLevelQuotient l E m n h))).unit.app
            ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).obj
              (integralDualizingFiniteTerm l E D X m)) ≫
          (scalarRestriction (compactSupportLevelQuotient l E m n h) (Spec (.of D.k))).map
            ((comparison l E c h).app (integralDualizingFiniteTerm l E D X m) ≫
              (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
                (((proEtaleRingDerivedExtensionAdjunction
                  (proEtaleConstantRingMap (T := X)
                    (compactSupportLevelQuotient l E m n h))).homEquiv _ _).symm
                  (dualizingTransition D l E X hl h))) ≫
          (scalarRestriction (compactSupportLevelQuotient l E m n h) (Spec (.of D.k))).map
            ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
              iₙ.inv)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q m n h
    exact evaluated_square D l E c h Q
  · intro Q m n h
    exact d_restriction l E c h Q
  · intro Q n
    exact conjugate_identity ((theta D l E c n).app Q) _ _
      (evaluated_square D l E c (le_refl n) Q)
      (NatTrans.congr_app (transition_id l E n) ((B D l E c).obj Q))
  · intro Q r m n hrm hmn
    exact conjugate_composition
      ((theta D l E c r).app Q) ((theta D l E c m).app Q)
      ((theta D l E c n).app Q) _ _ _ _ _ _
      (evaluated_square D l E c hrm Q) (evaluated_square D l E c hmn Q)
      (evaluated_square D l E c (hmn.trans hrm) Q)
      (NatTrans.congr_app (transition_comp l E hrm hmn) ((B D l E c).obj Q))
  · intro Q n
    exact transport_unit (normalizedDVRRes l E (Spec (.of D.k)) (le_refl n))
      (normalizedDVRResUnit l E (Spec (.of D.k)) n)
      ((compactSupportSystemEvaluation l E c n).app Q) _ _
      (support_square l E c (le_refl n) Q)
      (derivedTransition_id l E (Spec (.of D.k)) ((support l E c).obj Q) n)
  · intro Q r m n hrm hmn
    exact transport_comp
      (normalizedDVRRes l E (Spec (.of D.k)) hrm)
      (normalizedDVRRes l E (Spec (.of D.k)) hmn)
      (normalizedDVRRes l E (Spec (.of D.k)) (hmn.trans hrm))
      (normalizedDVRResComp l E (Spec (.of D.k)) hrm hmn)
      ((compactSupportSystemEvaluation l E c r).app Q)
      ((compactSupportSystemEvaluation l E c m).app Q)
      ((compactSupportSystemEvaluation l E c n).app Q)
      _ _ _ _ _ _
      (support_square l E c hrm Q) (support_square l E c hmn Q)
      (support_square l E c (hmn.trans hrm) Q)
      (derivedTransition_comp l E (Spec (.of D.k)) ((support l E c).obj Q) hrm hmn)
  · intro m n h
    exact site_compatibility D l E hl X c h
  · intro Q m n h iₘ iₙ hs
    have hc := transpose_conjugation
        (quotientScalarAdjunction l E X h)
        (quotientScalarAdjunction l E (Spec (.of D.k)) h)
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1)))
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
      (comparison l E c h) (sigma l E X h Q) (dualizingTransition D l E X hl h)
      iₘ iₙ hs
    dsimp only [Functor.id_obj, quotientScalarAdjunction, comparison] at hc
    dsimp only [Functor.id_obj, d, coefficientMateRestrictionArrow, comparison]
    convert hc using 1 <;> rfl

end WeilConjectures.DualizingSupportEvaluation
