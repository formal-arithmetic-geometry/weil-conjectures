/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedOpenImageDeltaDefs
import WeilConjectures.AlgebraicGeometry.CondensedOpenImageWeilH0Normalization
import WeilConjectures.AlgebraicGeometry.CondensedOpenImageWeilEqPartExchange
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The connecting-map component of the condensed open-image Weil assertion: the boundary
`j_* X₃ ⟶ R¹j_* X₁` intertwines the ordinary Weil map of `X₃` with the homology Weil map
of `X₁`. Source: latest blueprint, p-dl-a1-exact, Step 8
(blueprint: new-dl-a1-weil-eq-part). -/
def DlOpenImageWeilEqPart {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {U C : Scheme.{u}} {gU : U ⟶ U} {gC : C ⟶ C}
    (j : U ⟶ C) (sq : CommSq gU j j gC) : Prop :=
  ∀ (S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) (hS : S.ShortExact),
    IsConstantModelConstructible Λ U S.X₁ →
    IsConstantModelConstructible Λ U S.X₂ →
    IsConstantModelConstructible Λ U S.X₃ →
    ∀ (φ₁ : (upperStar Λ gU).obj S.X₁ ≅ S.X₁)
      (φ₂ : (upperStar Λ gU).obj S.X₂ ≅ S.X₂)
      (φ₃ : (upperStar Λ gU).obj S.X₃ ≅ S.X₃),
    (upperStar Λ gU).map S.f ≫ φ₂.hom = φ₁.hom ≫ S.f →
    (upperStar Λ gU).map S.g ≫ φ₃.hom = φ₂.hom ≫ S.g →
    (upperStar Λ gC).map (dlOpenImageDelta Λ j S hS) ≫
        dlOpenImageHomologyWeilMap Λ j sq S.X₁ φ₁ 1 =
      dlOpenImageWeilMap Λ j sq S.X₃ φ₃ ≫ dlOpenImageDelta Λ j S hS

private theorem dlOpenImage_weil_eqPart_generic
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U C : Scheme.{u}} {gU : U ⟶ U} {gC : C ⟶ C}
    (j : U ⟶ C) (sq : CommSq gU j j gC)
    : DlOpenImageWeilEqPart (Λ := Λ) j sq := by
  intro S hS _ _ _ φ₁ φ₂ φ₃ hf hg
  have hb := condensedOpenImage_weil_boundary Λ j sq S hS φ₁ φ₂ φ₃ hf hg
  have hn := condensedOpenImage_weil_h0_normalization Λ j sq S.X₃ φ₃
  simp only [dlOpenImageDelta, Functor.map_comp, Category.assoc]
  rw [hb, ← Category.assoc, hn, Category.assoc]

/-- The connecting-map component of the condensed open-image Weil assertion.
Source: latest blueprint, p-dl-a1-exact, Step 8 (blueprint: new-dl-a1-weil-eq-part).
Proof: first at generic coefficients and a generic commuting square
(`dlOpenImage_weil_eqPart_generic`). Unfold `dlOpenImageDelta` as the inverse
`singleRightDerivedH0Iso` of `S.X₃` followed by the raw homology boundary `δ`, and expand
`gC^*` of this composite. The raw boundary square
(`condensedOpenImage_weil_boundary`, new-dl-a1-weil-eq-part-exchange) moves `δ` past the
homology Weil maps, giving `gC^*(η) ≫ W₀(S.X₃) ≫ δ`; the degree-zero normalization
(`condensedOpenImage_weil_h0_normalization`, new-dl-a1-weil-h0-normalization) rewrites
`gC^*(η) ≫ W₀(S.X₃)` as the ordinary Weil map followed by `η`. Associativity gives the
square; the theorem is the specialization to the geometric Frobenius square. -/
theorem condensedOpenImage_weil_eqPart
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
    DlOpenImageWeilEqPart (Λ := Profinite.padicAlgClRingObj ell)
      (dlGeometricOpen D j₀) sq := by
  exact dlOpenImage_weil_eqPart_generic (Profinite.padicAlgClRingObj ell)
    (dlGeometricOpen D j₀) sq

end AlgebraicGeometry.ProEtale.CondensedRing
