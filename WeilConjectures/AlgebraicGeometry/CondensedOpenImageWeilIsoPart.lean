/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedOpenImageDeltaDefs
import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The invertibility component of the condensed open-image Weil assertion.
Source: latest blueprint, p-dl-a1-exact, Step 8 (blueprint: new-dl-a1-weil-iso-part).
The four displayed maps are composites of the invertible Frobenius exchange, the
invertible supplied Weil maps, and homology maps of isomorphisms. -/
def DlOpenImageWeilIsoPart {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {U C : Scheme.{u}} {gU : U ⟶ U} {gC : C ⟶ C}
    (j : U ⟶ C) (sq : CommSq gU j j gC) : Prop :=
  ∀ (S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) (_hS : S.ShortExact),
    IsConstantModelConstructible Λ U S.X₁ →
    IsConstantModelConstructible Λ U S.X₂ →
    IsConstantModelConstructible Λ U S.X₃ →
    ∀ (φ₁ : (upperStar Λ gU).obj S.X₁ ≅ S.X₁)
      (φ₂ : (upperStar Λ gU).obj S.X₂ ≅ S.X₂)
      (φ₃ : (upperStar Λ gU).obj S.X₃ ≅ S.X₃),
    (upperStar Λ gU).map S.f ≫ φ₂.hom = φ₁.hom ≫ S.f →
    (upperStar Λ gU).map S.g ≫ φ₃.hom = φ₂.hom ≫ S.g →
    IsIso (dlOpenImageWeilMap Λ j sq S.X₁ φ₁) ∧
    IsIso (dlOpenImageWeilMap Λ j sq S.X₂ φ₂) ∧
    IsIso (dlOpenImageWeilMap Λ j sq S.X₃ φ₃) ∧
    IsIso (dlOpenImageHomologyWeilMap Λ j sq S.X₁ φ₁ 1)

/-- For a square whose horizontal maps are isomorphisms, the ordinary and the homology
Weil maps of every module are isomorphisms: the ordinary base change along isomorphisms
is invertible, derived pullback along an isomorphism is an equivalence, so the derived
exchange is invertible, and the remaining factors are images of isomorphisms. -/
private theorem isIso_dlOpenImageWeilMaps
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U C : Scheme.{u}} {gU : U ⟶ U} {gC : C ⟶ C}
    [IsIso gU] [IsIso gC] (j : U ⟶ C) (sq : CommSq gU j j gC)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (φ : (upperStar Λ gU).obj M ≅ M) :
    IsIso (dlOpenImageWeilMap Λ j sq M φ) ∧
    IsIso (dlOpenImageHomologyWeilMap Λ j sq M φ 1) := by
  let : (moduleObjectDerivedPullback Λ gU).IsEquivalence := by
    unfold moduleObjectDerivedPullback
    infer_instance
  let : (moduleObjectDerivedPullback Λ gC).IsEquivalence := by
    unfold moduleObjectDerivedPullback
    infer_instance
  have : IsIso (dlOpenImageExchange Λ j sq) :=
    Adjunction.isIso_exchangeRight_of_isEquivalence _ _ _
  refine ⟨?_, ?_⟩
  · unfold dlOpenImageWeilMap
    infer_instance
  · unfold dlOpenImageHomologyWeilMap dlOpenImageDerivedWeilMap
    infer_instance

/-- The invertibility component of the condensed open-image Weil assertion.
Source: latest blueprint, p-dl-a1-exact, Step 8 (blueprint: new-dl-a1-weil-iso-part).
Proof: the model Frobenius maps of `U` and `C` are automorphisms. The ordinary base change
of a square whose horizontal maps are isomorphisms is invertible
(`isIso_lowerStarBaseChange_of_isIso`), so each ordinary Weil map is the composite of two
isomorphisms. Derived pullback along an isomorphism is the derived functor of an exact
equivalence, hence an equivalence, so the derived exchange, a mate along equivalences, is
invertible (lem-sf-condensed-isomorphism-square-exchange); the homology Weil map is a
composite of this exchange with homology and derived images of isomorphisms. -/
theorem condensedOpenImage_weil_isoPart
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (_iota : PadicAlgCl ell →+* ℂ)
    (U₀ C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    [SmoothOfRelativeDimension 1 C₀.hom]
    (j₀ : U₀ ⟶ C₀) [IsOpenImmersion j₀.left] [QuasiCompact j₀.left]
    [IsDominant j₀.left]
    (sq : CommSq (StrictWeil.modelFrobenius D U₀).hom (dlGeometricOpen D j₀)
      (dlGeometricOpen D j₀) (StrictWeil.modelFrobenius D C₀).hom) :
    DlOpenImageWeilIsoPart (Λ := Profinite.padicAlgClRingObj ell)
      (dlGeometricOpen D j₀) sq := by
  intro S _ _ _ _ φ₁ φ₂ φ₃ _ _
  have h₁ := isIso_dlOpenImageWeilMaps _ (dlGeometricOpen D j₀) sq S.X₁ φ₁
  exact ⟨h₁.1, (isIso_dlOpenImageWeilMaps _ (dlGeometricOpen D j₀) sq S.X₂ φ₂).1,
    (isIso_dlOpenImageWeilMaps _ (dlGeometricOpen D j₀) sq S.X₃ φ₃).1, h₁.2⟩

end AlgebraicGeometry.ProEtale.CondensedRing
