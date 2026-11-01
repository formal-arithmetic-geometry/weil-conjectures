/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData

/-! # Rational exceptional scalar cocycles

Source: blueprint thm-coef-qbar-verdier, proof steps 6--9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] WeilConjectures.CoefQbarTensor
  WeilConjectures.CoefQbarPullback
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageCategory
  WeilConjectures.sfRationalScalarExtension WeilConjectures.sfRationalScalarComp
  WeilConjectures.sfRationalScalarUnit WeilConjectures.sfRationalConstructibleLocalization
  CategoryTheory.ScalarLocalization.category CategoryTheory.ScalarLocalization.composition

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

/-- The component cocycle equation for three finite functors and scalar comparisons.
Source: exceptional scalar cocycle, retained steps 6--8
(blueprint: lem-coef-qbar-rational-scalar-cocycles). -/
structure CoefficientCocycleCondition
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    {U₀ : C₀ ⥤ C₁} {U₁ : C₁ ⥤ C₂} {U₂ : C₀ ⥤ C₂}
    {V₀ : D₀ ⥤ D₁} {V₁ : D₁ ⥤ D₂} {V₂ : D₀ ⥤ D₂}
    (b₀ : F₀ ⋙ V₀ ≅ U₀ ⋙ F₁) (b₁ : F₁ ⋙ V₁ ≅ U₁ ⋙ F₂)
    (b₂ : F₀ ⋙ V₂ ≅ U₂ ⋙ F₂)
    (aU : U₀ ⋙ U₁ ≅ U₂) (aV : V₀ ⋙ V₁ ≅ V₂) : Prop where
  equation (x : C₀) : V₁.map (b₀.hom.app x) ≫ b₁.hom.app (U₀.obj x) ≫ F₂.map (aU.hom.app x) =
    aV.hom.app (F₀.obj x) ≫ b₂.hom.app x

namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition associator unitor)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

omit [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))] in
private theorem rationalCocycle_reindex (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    (E L M : ConstructibleExceptionalCoefficients.FieldStage.{u} l)
    (i : E.carrier →ₐ[Padic l] L.carrier) (j : L.carrier →ₐ[Padic l] M.carrier)
    (k : E.carrier →ₐ[Padic l] M.carrier) (hk : j.comp i = k) :
    ConstructibleExceptionalCoefficients.FieldCocycle l (AuxiliaryClosure.{u} l)
      (S.fields.rationalComparison c E L i) (S.fields.rationalComparison c L M j)
      (S.fields.rationalComparison c E M k)
      (GeneralAlgebraicallyClosedCoefficients.scalarAssociator
        l E.carrier L.carrier M.carrier i j k hk X)
      (GeneralAlgebraicallyClosedCoefficients.scalarAssociator
        l E.carrier L.carrier M.carrier i j k hk Y) := by
  subst k
  simpa [GeneralAlgebraicallyClosedCoefficients.scalarAssociator] using
    S.fields.rationalCocycle c E L M i j

omit [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))] in
/-- Reindex both exceptional scalar cocycles by a specified composite algebra map.
Source: thm-coef-qbar-verdier, retained steps 6--8
(blueprint: lem-coef-qbar-rational-scalar-cocycles).

Proof: substitute the composite algebra map using hk. The defining scalar associator
then reduces to the published rational scalar composition comparison. Apply the
coefficient system's rationalCocycle and retain its two component equations. -/
theorem rational_scalar_cocycles (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    (E L M : ConstructibleExceptionalCoefficients.FieldStage.{u} l)
    (i : E.carrier →ₐ[Padic l] L.carrier) (j : L.carrier →ₐ[Padic l] M.carrier)
    (k : E.carrier →ₐ[Padic l] M.carrier) (hk : j.comp i = k) :
    let r₀ := S.fields.rationalComparison c E L i
    let r₁ := S.fields.rationalComparison c L M j
    let r₂ := S.fields.rationalComparison c E M k
    let aX := GeneralAlgebraicallyClosedCoefficients.scalarAssociator
      l E.carrier L.carrier M.carrier i j k hk X
    let aY := GeneralAlgebraicallyClosedCoefficients.scalarAssociator
      l E.carrier L.carrier M.carrier i j k hk Y
    CoefficientCocycleCondition (S.ring.operation c (.rational E)).F
      (S.ring.operation c (.rational L)).F (S.ring.operation c (.rational M)).F
      r₀.q r₁.q r₂.q aX aY ∧
    CoefficientCocycleCondition (S.ring.operation c (.rational E)).G
      (S.ring.operation c (.rational L)).G (S.ring.operation c (.rational M)).G
      r₀.b r₁.b r₂.b aY aX := by
  have H := rationalCocycle_reindex D l hl X f c S E L M i j k hk
  dsimp only [ConstructibleExceptionalCoefficients.FieldCocycle] at H
  rcases H with ⟨Hleft, Hright⟩
  exact ⟨⟨Hleft⟩, ⟨Hright⟩⟩

end WeilConjectures.CoefQbarVerdier
