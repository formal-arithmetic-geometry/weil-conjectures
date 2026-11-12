/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemScalarFiniteEvaluation
public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionComparisonPasting
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import WeilConjectures.SmoothPurity.Compact.CompactSupportScalarDirectNormalization
public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOpenScalarPullbackMate
import all WeilConjectures.SixFunctors.FrobeniusExchange.SystemOpenScalarPullbackMate
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.SmoothPurity.FrobeniusExchange.SystemScalarFiniteEvaluation
import all WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralScalarPullbackMateNormalization

/-! # Scalar mates of the system scalar/pullback comparison for arbitrary morphisms

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 06YY and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace CategoryTheory.Functor

/-- A derived square is the localization of an ordinary square of exact functors, read
through the exact-localization factors. -/
def IsDerivedSquareOf {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {F₃ : A ⥤ C} {F₄ : C ⥤ D}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [F₃.Additive] [PreservesFiniteLimits F₃] [PreservesFiniteColimits F₃]
    [F₄.Additive] [PreservesFiniteLimits F₄] [PreservesFiniteColimits F₄]
    (σ : F₁ ⋙ F₂ ⟶ F₃ ⋙ F₄)
    (Δ : F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ⟶
      F₃.mapDerivedCategory ⋙ F₄.mapDerivedCategory) : Prop :=
  ∀ P : CochainComplex A ℤ,
    Δ.app (DerivedCategory.Q.obj P) ≫
        F₄.mapDerivedCategory.map (F₃.mapDerivedCategoryFactors.hom.app P) ≫
        F₄.mapDerivedCategoryFactors.hom.app ((F₃.mapHomologicalComplex (.up ℤ)).obj P) =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ (.up ℤ)).app P)

section Helpers

variable {C D : Type*} [Category C] [Category D]

/-- Cancelling an isomorphism against a factorization: if `j ≫ f₁ ≫ f₂ = g`,
`n ≫ g = g' ≫ q` and `i.hom ≫ e₁ ≫ e₂ = g'`, then `i.inv ≫ n ≫ j ≫ f₁ ≫ f₂ = e₁ ≫ e₂ ≫ q`. -/
theorem inv_comp_eq_of_factors {X Y Z W U V S T : D} (i : X ≅ Y) {n : X ⟶ Z} {j : Z ⟶ W}
    {f₁ : W ⟶ U} {f₂ : U ⟶ V} {g : Z ⟶ V} {g' : X ⟶ T} {q : T ⟶ V} {e₁ : Y ⟶ S}
    {e₂ : S ⟶ T} (h₁ : j ≫ f₁ ≫ f₂ = g) (h₂ : n ≫ g = g' ≫ q) (h₃ : i.hom ≫ e₁ ≫ e₂ = g') :
    i.inv ≫ n ≫ j ≫ f₁ ≫ f₂ = e₁ ≫ e₂ ≫ q := by
  rw [h₁, h₂, ← h₃]
  simp

/-- Pasting six commuting squares along a commuting hexagon `a ≫ b ≫ c = a' ≫ b' ≫ c'`
mapped by a functor `F`: the two composites `ΔE₀ ≫ eQ ≫ ΔX₀` and `n₁ ≫ n₂ ≫ n₃` agree
after post-composition with `ψ₁ ≫ ψ₂ ≫ ψ₃`. -/
theorem hexagon_paste (F : C ⥤ D) {P₀ P₁ P₂ P₃ P₁' P₂' : C} {a : P₀ ⟶ P₁} {b : P₁ ⟶ P₂}
    {c : P₂ ⟶ P₃} {a' : P₀ ⟶ P₁'} {b' : P₁' ⟶ P₂'} {c' : P₂' ⟶ P₃}
    (hord : a ≫ b ≫ c = a' ≫ b' ≫ c')
    {X₀ X₁ X₂ X₃ X₄ X₅ Y₁ Y₂ Z₁ Z₂ W₁ W₂ V₁ V₂ U₁ U₂ T₁ T₂ : D}
    {ΔE₀ : X₀ ⟶ X₁} {eQ : X₁ ⟶ X₂} {ΔX₀ : X₂ ⟶ X₃} {ψ₁ : X₃ ⟶ X₄} {ψ₂ : X₄ ⟶ X₅}
    {ψ₃ : X₅ ⟶ F.obj P₃} {u₁ : X₂ ⟶ Y₁} {ΔX₁ : Y₁ ⟶ X₄} {u₂ : Y₁ ⟶ Y₂}
    {u₃ : Y₂ ⟶ F.obj P₂} {w₁ : X₁ ⟶ Z₁} {w₂ : Z₁ ⟶ Z₂} {w₃ : Z₂ ⟶ Y₂} {φ₁ : X₀ ⟶ W₁}
    {ΔE₁ : W₁ ⟶ Z₁} {v₁ : Z₂ ⟶ F.obj P₁} {φ₂ : W₁ ⟶ W₂} {φ₃ : W₂ ⟶ F.obj P₀}
    (x₁ : ΔX₀ ≫ ψ₁ = u₁ ≫ ΔX₁) (x₂ : ΔX₁ ≫ ψ₂ ≫ ψ₃ = u₂ ≫ u₃ ≫ F.map c)
    (q₁ : eQ ≫ u₁ ≫ u₂ = w₁ ≫ w₂ ≫ w₃) (e₁ : ΔE₀ ≫ w₁ = φ₁ ≫ ΔE₁)
    (e₂ : w₃ ≫ u₃ = v₁ ≫ F.map b) (e₃ : ΔE₁ ≫ w₂ ≫ v₁ = φ₂ ≫ φ₃ ≫ F.map a)
    {n₁ : X₀ ⟶ V₁} {n₂ : V₁ ⟶ V₂} {n₃ : V₂ ⟶ X₃} {k₁ : V₂ ⟶ U₁} {k₂ : U₁ ⟶ U₂}
    {k₃ : U₂ ⟶ X₅} {t₁ : U₂ ⟶ F.obj P₂'} {g₁ : V₁ ⟶ T₁} {Δq₁ : T₁ ⟶ U₁} {g₂ : T₁ ⟶ T₂}
    {g₃ : T₂ ⟶ F.obj P₁'} {h₃ : W₂ ⟶ T₂}
    (l₁ : n₃ ≫ ψ₁ ≫ ψ₂ = k₁ ≫ k₂ ≫ k₃) (l₂ : k₃ ≫ ψ₃ = t₁ ≫ F.map c')
    (l₃ : n₂ ≫ k₁ = g₁ ≫ Δq₁) (l₄ : Δq₁ ≫ k₂ ≫ t₁ = g₂ ≫ g₃ ≫ F.map b')
    (l₅ : n₁ ≫ g₁ ≫ g₂ = φ₁ ≫ φ₂ ≫ h₃) (l₆ : h₃ ≫ g₃ = φ₃ ≫ F.map a') :
    ΔE₀ ≫ eQ ≫ ΔX₀ ≫ ψ₁ ≫ ψ₂ ≫ ψ₃ = n₁ ≫ n₂ ≫ n₃ ≫ ψ₁ ≫ ψ₂ ≫ ψ₃ := by
  have hF : F.map a ≫ F.map b ≫ F.map c = F.map a' ≫ F.map b' ≫ F.map c' := by
    simp only [← F.map_comp, hord]
  rw [reassoc_of% x₁, x₂, reassoc_of% q₁, reassoc_of% e₁, reassoc_of% e₂, reassoc_of% e₃,
    hF, reassoc_of% l₁, l₂, reassoc_of% l₃, reassoc_of% l₄, reassoc_of% l₅, reassoc_of% l₆]

end Helpers

section Square

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {F₃ : A ⥤ C} {F₄ : C ⥤ D}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [F₃.Additive] [PreservesFiniteLimits F₃] [PreservesFiniteColimits F₃]
    [F₄.Additive] [PreservesFiniteLimits F₄] [PreservesFiniteColimits F₄]

/-- Every ordinary square of exact functors has a localized derived square. -/
theorem exists_isDerivedSquareOf (σ : F₁ ⋙ F₂ ⟶ F₃ ⋙ F₄) :
    ∃ Δ, IsDerivedSquareOf σ Δ := by
  refine ⟨(mapDerivedCategoryCompIso F₁ F₂).hom ≫ mapDerivedCategoryNatTrans σ ≫
    (mapDerivedCategoryCompIso F₃ F₄).inv, fun P ↦ ?_⟩
  simp only [NatTrans.comp_app, Category.assoc]
  exact inv_comp_eq_of_factors ((mapDerivedCategoryCompIso F₁ F₂).app _).symm
    (mapDerivedCategoryCompIso_hom_app_factors F₃ F₄ P) (mapDerivedCategoryNatTrans_fac σ P)
    (mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ P)

/-- The derived square isomorphism is the localization of its ordinary square. -/
theorem isDerivedSquareOf_mapDerivedCategorySquareIso (σ : F₁ ⋙ F₂ ≅ F₃ ⋙ F₄) :
    IsDerivedSquareOf σ.hom (mapDerivedCategorySquareIso σ).hom :=
  AlgebraicGeometry.Scheme.mapDerivedCategorySquareIso_hom_app_factors F₁ F₂ F₃ F₄ σ

end Square

/-- Localization preserves commuting hexagons of squares of exact functors. -/
theorem derivedCube_of_isDerivedSquareOf
    {A A' B B' a a' b b' : Type*} [Category A] [Category A'] [Category B] [Category B']
    [Category a] [Category a'] [Category b] [Category b']
    [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
    [Abelian a] [Abelian a'] [Abelian b] [Abelian b']
    [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B]
    [HasDerivedCategory B'] [HasDerivedCategory a] [HasDerivedCategory a']
    [HasDerivedCategory b] [HasDerivedCategory b']
    {RY : A' ⥤ A} {RX : B' ⥤ B} {rY : a' ⥤ a} {rX : b' ⥤ b}
    {JE : A ⥤ B} {JL : A' ⥤ B'} {jE : a ⥤ b} {jL : a' ⥤ b'}
    {eA : A ⥤ a} {eB : B ⥤ b} {eA' : A' ⥤ a'} {eB' : B' ⥤ b'}
    [RY.Additive] [PreservesFiniteLimits RY] [PreservesFiniteColimits RY]
    [RX.Additive] [PreservesFiniteLimits RX] [PreservesFiniteColimits RX]
    [rY.Additive] [PreservesFiniteLimits rY] [PreservesFiniteColimits rY]
    [rX.Additive] [PreservesFiniteLimits rX] [PreservesFiniteColimits rX]
    [JE.Additive] [PreservesFiniteLimits JE] [PreservesFiniteColimits JE]
    [JL.Additive] [PreservesFiniteLimits JL] [PreservesFiniteColimits JL]
    [jE.Additive] [PreservesFiniteLimits jE] [PreservesFiniteColimits jE]
    [jL.Additive] [PreservesFiniteLimits jL] [PreservesFiniteColimits jL]
    [eA.Additive] [PreservesFiniteLimits eA] [PreservesFiniteColimits eA]
    [eB.Additive] [PreservesFiniteLimits eB] [PreservesFiniteColimits eB]
    [eA'.Additive] [PreservesFiniteLimits eA'] [PreservesFiniteColimits eA']
    [eB'.Additive] [PreservesFiniteLimits eB'] [PreservesFiniteColimits eB']
    {δE : eA ⋙ jE ⟶ JE ⋙ eB} {δL : eA' ⋙ jL ⟶ JL ⋙ eB'}
    {Q : RY ⋙ JE ⟶ JL ⋙ RX} {qn : rY ⋙ jE ⟶ jL ⋙ rX}
    {ρY : RY ⋙ eA ⟶ eA' ⋙ rY} {ρX : RX ⋙ eB ⟶ eB' ⋙ rX}
    (hcube : ∀ M : A', δE.app (RY.obj M) ≫ eB.map (Q.app M) ≫ ρX.app (JL.obj M) =
      jE.map (ρY.app M) ≫ qn.app (eA'.obj M) ≫ rX.map (δL.app M))
    {ΔE : eA.mapDerivedCategory ⋙ jE.mapDerivedCategory ⟶
      JE.mapDerivedCategory ⋙ eB.mapDerivedCategory} (hΔE : IsDerivedSquareOf δE ΔE)
    {ΔL : eA'.mapDerivedCategory ⋙ jL.mapDerivedCategory ⟶
      JL.mapDerivedCategory ⋙ eB'.mapDerivedCategory} (hΔL : IsDerivedSquareOf δL ΔL)
    {ΔQ : RY.mapDerivedCategory ⋙ JE.mapDerivedCategory ⟶
      JL.mapDerivedCategory ⋙ RX.mapDerivedCategory} (hΔQ : IsDerivedSquareOf Q ΔQ)
    {Δq : rY.mapDerivedCategory ⋙ jE.mapDerivedCategory ⟶
      jL.mapDerivedCategory ⋙ rX.mapDerivedCategory} (hΔq : IsDerivedSquareOf qn Δq)
    {ΔY : RY.mapDerivedCategory ⋙ eA.mapDerivedCategory ⟶
      eA'.mapDerivedCategory ⋙ rY.mapDerivedCategory} (hΔY : IsDerivedSquareOf ρY ΔY)
    {ΔX : RX.mapDerivedCategory ⋙ eB.mapDerivedCategory ⟶
      eB'.mapDerivedCategory ⋙ rX.mapDerivedCategory} (hΔX : IsDerivedSquareOf ρX ΔX)
    (M : DerivedCategory A') :
    ΔE.app (RY.mapDerivedCategory.obj M) ≫ eB.mapDerivedCategory.map (ΔQ.app M) ≫
        ΔX.app (JL.mapDerivedCategory.obj M) =
      jE.mapDerivedCategory.map (ΔY.app M) ≫ Δq.app (eA'.mapDerivedCategory.obj M) ≫
        rX.mapDerivedCategory.map (ΔL.app M) := by
  have key : ∀ K : CochainComplex A' ℤ,
      ΔE.app (RY.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
          eB.mapDerivedCategory.map (ΔQ.app (DerivedCategory.Q.obj K)) ≫
          ΔX.app (JL.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) =
        jE.mapDerivedCategory.map (ΔY.app (DerivedCategory.Q.obj K)) ≫
          Δq.app (eA'.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
          rX.mapDerivedCategory.map (ΔL.app (DerivedCategory.Q.obj K)) := by
    intro K
    have x1 : ΔX.app (JL.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
        rX.mapDerivedCategory.map (eB'.mapDerivedCategory.map
          (JL.mapDerivedCategoryFactors.hom.app K)) =
        eB.mapDerivedCategory.map (RX.mapDerivedCategory.map
          (JL.mapDerivedCategoryFactors.hom.app K)) ≫
        ΔX.app (DerivedCategory.Q.obj ((JL.mapHomologicalComplex (.up ℤ)).obj K)) :=
      (ΔX.naturality _).symm
    have q1 : eB.mapDerivedCategory.map (ΔQ.app (DerivedCategory.Q.obj K)) ≫
        eB.mapDerivedCategory.map (RX.mapDerivedCategory.map
          (JL.mapDerivedCategoryFactors.hom.app K)) ≫
        eB.mapDerivedCategory.map (RX.mapDerivedCategoryFactors.hom.app
          ((JL.mapHomologicalComplex (.up ℤ)).obj K)) =
        eB.mapDerivedCategory.map (JE.mapDerivedCategory.map
          (RY.mapDerivedCategoryFactors.hom.app K)) ≫
        eB.mapDerivedCategory.map (JE.mapDerivedCategoryFactors.hom.app
          ((RY.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        eB.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex Q (.up ℤ)).app K)) := by
      simp only [← Functor.map_comp]
      exact congrArg eB.mapDerivedCategory.map (hΔQ K)
    have e1 : ΔE.app (RY.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
        eB.mapDerivedCategory.map (JE.mapDerivedCategory.map
          (RY.mapDerivedCategoryFactors.hom.app K)) =
        jE.mapDerivedCategory.map (eA.mapDerivedCategory.map
          (RY.mapDerivedCategoryFactors.hom.app K)) ≫
        ΔE.app (DerivedCategory.Q.obj ((RY.mapHomologicalComplex (.up ℤ)).obj K)) :=
      (ΔE.naturality _).symm
    have e2 : eB.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex Q (.up ℤ)).app K)) ≫
        eB.mapDerivedCategoryFactors.hom.app ((RX.mapHomologicalComplex (.up ℤ)).obj
          ((JL.mapHomologicalComplex (.up ℤ)).obj K)) =
        eB.mapDerivedCategoryFactors.hom.app ((JE.mapHomologicalComplex (.up ℤ)).obj
          ((RY.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        DerivedCategory.Q.map ((eB.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex Q (.up ℤ)).app K)) :=
      eB.mapDerivedCategoryFactors.hom.naturality _
    have l1 : rX.mapDerivedCategory.map (ΔL.app (DerivedCategory.Q.obj K)) ≫
        rX.mapDerivedCategory.map (eB'.mapDerivedCategory.map
          (JL.mapDerivedCategoryFactors.hom.app K)) ≫
        rX.mapDerivedCategory.map (eB'.mapDerivedCategoryFactors.hom.app
          ((JL.mapHomologicalComplex (.up ℤ)).obj K)) =
        rX.mapDerivedCategory.map (jL.mapDerivedCategory.map
          (eA'.mapDerivedCategoryFactors.hom.app K)) ≫
        rX.mapDerivedCategory.map (jL.mapDerivedCategoryFactors.hom.app
          ((eA'.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        rX.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex δL (.up ℤ)).app K)) := by
      simp only [← Functor.map_comp]
      exact congrArg rX.mapDerivedCategory.map (hΔL K)
    have l2 : rX.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex δL (.up ℤ)).app K)) ≫
        rX.mapDerivedCategoryFactors.hom.app ((eB'.mapHomologicalComplex (.up ℤ)).obj
          ((JL.mapHomologicalComplex (.up ℤ)).obj K)) =
        rX.mapDerivedCategoryFactors.hom.app ((jL.mapHomologicalComplex (.up ℤ)).obj
          ((eA'.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        DerivedCategory.Q.map ((rX.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex δL (.up ℤ)).app K)) :=
      rX.mapDerivedCategoryFactors.hom.naturality _
    have l3 : Δq.app (eA'.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
        rX.mapDerivedCategory.map (jL.mapDerivedCategory.map
          (eA'.mapDerivedCategoryFactors.hom.app K)) =
        jE.mapDerivedCategory.map (rY.mapDerivedCategory.map
          (eA'.mapDerivedCategoryFactors.hom.app K)) ≫
        Δq.app (DerivedCategory.Q.obj ((eA'.mapHomologicalComplex (.up ℤ)).obj K)) :=
      (Δq.naturality _).symm
    have l5 : jE.mapDerivedCategory.map (ΔY.app (DerivedCategory.Q.obj K)) ≫
        jE.mapDerivedCategory.map (rY.mapDerivedCategory.map
          (eA'.mapDerivedCategoryFactors.hom.app K)) ≫
        jE.mapDerivedCategory.map (rY.mapDerivedCategoryFactors.hom.app
          ((eA'.mapHomologicalComplex (.up ℤ)).obj K)) =
        jE.mapDerivedCategory.map (eA.mapDerivedCategory.map
          (RY.mapDerivedCategoryFactors.hom.app K)) ≫
        jE.mapDerivedCategory.map (eA.mapDerivedCategoryFactors.hom.app
          ((RY.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        jE.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ρY (.up ℤ)).app K)) := by
      simp only [← Functor.map_comp]
      exact congrArg jE.mapDerivedCategory.map (hΔY K)
    have l6 : jE.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ρY (.up ℤ)).app K)) ≫
        jE.mapDerivedCategoryFactors.hom.app ((rY.mapHomologicalComplex (.up ℤ)).obj
          ((eA'.mapHomologicalComplex (.up ℤ)).obj K)) =
        jE.mapDerivedCategoryFactors.hom.app ((eA.mapHomologicalComplex (.up ℤ)).obj
          ((RY.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        DerivedCategory.Q.map ((jE.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex ρY (.up ℤ)).app K)) :=
      jE.mapDerivedCategoryFactors.hom.naturality _
    have hord : (NatTrans.mapHomologicalComplex δE (.up ℤ)).app
            ((RY.mapHomologicalComplex (.up ℤ)).obj K) ≫
          (eB.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex Q (.up ℤ)).app K) ≫
          (NatTrans.mapHomologicalComplex ρX (.up ℤ)).app
            ((JL.mapHomologicalComplex (.up ℤ)).obj K) =
        (jE.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex ρY (.up ℤ)).app K) ≫
          (NatTrans.mapHomologicalComplex qn (.up ℤ)).app
            ((eA'.mapHomologicalComplex (.up ℤ)).obj K) ≫
          (rX.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex δL (.up ℤ)).app K) := by
      ext n
      simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
        Functor.mapHomologicalComplex_map_f]
      exact hcube (K.X n)
    rw [← cancel_mono (rX.mapDerivedCategory.map (eB'.mapDerivedCategory.map
        (JL.mapDerivedCategoryFactors.hom.app K)) ≫
      rX.mapDerivedCategory.map (eB'.mapDerivedCategoryFactors.hom.app
        ((JL.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      rX.mapDerivedCategoryFactors.hom.app ((eB'.mapHomologicalComplex (.up ℤ)).obj
        ((JL.mapHomologicalComplex (.up ℤ)).obj K)))]
    simp only [Category.assoc]
    exact hexagon_paste DerivedCategory.Q hord x1 (hΔX _) q1 e1 e2 (hΔE _) l1 l2 l3 (hΔq _)
      l5 l6
  have h : (Functor.whiskerLeft RY.mapDerivedCategory ΔE ≫
      Functor.whiskerRight ΔQ eB.mapDerivedCategory ≫
      Functor.whiskerLeft JL.mapDerivedCategory ΔX :
        RY.mapDerivedCategory ⋙ eA.mapDerivedCategory ⋙ jE.mapDerivedCategory ⟶
          JL.mapDerivedCategory ⋙ eB'.mapDerivedCategory ⋙ rX.mapDerivedCategory) =
      Functor.whiskerRight ΔY jE.mapDerivedCategory ≫
        Functor.whiskerLeft eA'.mapDerivedCategory Δq ≫
        Functor.whiskerRight ΔL rX.mapDerivedCategory :=
    Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A' (ComplexShape.up ℤ)) (fun K ↦ key K)
  exact congr_app h M

end CategoryTheory.Functor

namespace WeilConjectures.FrobeniusExchange

/-- An iterated inverse mate of an isomorphism is inverse to the iterated inverse mate of
its inverse. -/
theorem iteratedMate_symm_hom_inv
    {a a' b b' : Type*} [Category a] [Category a'] [Category b] [Category b']
    {jE : a ⥤ b} {jL : a' ⥤ b'} {kE : b ⥤ a} {kL : b' ⥤ a'}
    (levelE : jE ⊣ kE) (levelL : jL ⊣ kL)
    {sY : a ⥤ a'} {rY : a' ⥤ a} (τY : sY ⊣ rY)
    {sX : b ⥤ b'} {rX : b' ⥤ b} (τX : sX ⊣ rX)
    (D : rX ⋙ kE ≅ kL ⋙ rY) :
    ((mateEquiv levelE levelL).symm ((mateEquiv τX τY).symm
        (TwoSquare.mk _ _ _ _ D.hom))) ≫
      ((mateEquiv τY τX).symm ((mateEquiv levelL levelE).symm
        (TwoSquare.mk _ _ _ _ D.inv))) = 𝟙 _ ∧
    ((mateEquiv τY τX).symm ((mateEquiv levelL levelE).symm
        (TwoSquare.mk _ _ _ _ D.inv))) ≫
      ((mateEquiv levelE levelL).symm ((mateEquiv τX τY).symm
        (TwoSquare.mk _ _ _ _ D.hom))) = 𝟙 _ := by
  have h1 := iterated_mateEquiv_conjugateEquiv_symm levelE levelL τY τX
    (TwoSquare.mk _ _ _ _ D.hom)
  have h2 := iterated_mateEquiv_conjugateEquiv_symm τY τX levelE levelL
    (TwoSquare.mk _ _ _ _ D.inv)
  constructor
  · erw [h1, h2]
    exact conjugateEquiv_symm_comm (τY.comp levelL) (levelE.comp τX) D.inv_hom_id
  · erw [h1, h2]
    exact conjugateEquiv_symm_comm (levelE.comp τX) (τY.comp levelL) D.hom_inv_id

/-- Pasting of scalar inverse mates: if the right-adjoint cube commutes, the inverse mates of
its faces satisfy the corresponding left-adjoint equation. -/
theorem scalarPullback_mate_pasting
    {A A' B B' a a' b b' : Type*} [Category A] [Category A'] [Category B] [Category B']
    [Category a] [Category a'] [Category b] [Category b']
    {JE : A ⥤ B} {JL : A' ⥤ B'} {jE : a ⥤ b} {jL : a' ⥤ b'}
    {SY : A ⥤ A'} {RY : A' ⥤ A} (σY : SY ⊣ RY)
    {SX : B ⥤ B'} {RX : B' ⥤ B} (σX : SX ⊣ RX)
    {sY : a ⥤ a'} {rY : a' ⥤ a} (τY : sY ⊣ rY)
    {sX : b ⥤ b'} {rX : b' ⥤ b} (τX : sX ⊣ rX)
    (eA : A ⥤ a) (eA' : A' ⥤ a') (eB : B ⥤ b) (eB' : B' ⥤ b')
    (Q : RY ⋙ JE ⟶ JL ⋙ RX) (ρX : RX ⋙ eB ⟶ eB' ⋙ rX) (ρY : RY ⋙ eA ⟶ eA' ⋙ rY)
    (pE : eA ⋙ jE ⟶ JE ⋙ eB) (pL : eA' ⋙ jL ⟶ JL ⋙ eB') (qn : rY ⋙ jE ⟶ jL ⋙ rX)
    (hcube : ∀ M : A', pE.app (RY.obj M) ≫ eB.map (Q.app M) ≫ ρX.app (JL.obj M) =
      jE.map (ρY.app M) ≫ qn.app (eA'.obj M) ≫ rX.map (pL.app M))
    (N : A) :
    sX.map (pE.app N) ≫
        ((mateEquiv σX τX).symm (TwoSquare.mk _ _ _ _ ρX)).app (JE.obj N) ≫
        eB'.map (((mateEquiv σY σX).symm (TwoSquare.mk _ _ _ _ Q)).app N) =
      ((mateEquiv τY τX).symm (TwoSquare.mk _ _ _ _ qn)).app (eA.obj N) ≫
        jL.map (((mateEquiv σY τY).symm (TwoSquare.mk _ _ _ _ ρY)).app N) ≫
        pL.app (SY.obj N) := by
  let SSP := ((mateEquiv σY σX).symm (TwoSquare.mk _ _ _ _ Q))
  let βX := ((mateEquiv σX τX).symm (TwoSquare.mk _ _ _ _ ρX))
  let βY := ((mateEquiv σY τY).symm (TwoSquare.mk _ _ _ _ ρY))
  let β := ((mateEquiv τY τX).symm (TwoSquare.mk _ _ _ _ qn))
  let M := SY.obj N
  have uQ : JE.map (σY.unit.app N) ≫ Q.app M = σX.unit.app (JE.obj N) ≫ RX.map (SSP.app N) :=
    unit_mateEquiv_symm σY σX (TwoSquare.mk _ _ _ _ Q) N
  have uX : eB.map (σX.unit.app (JE.obj N)) ≫ ρX.app (SX.obj (JE.obj N)) =
      τX.unit.app (eB.obj (JE.obj N)) ≫ rX.map (βX.app (JE.obj N)) :=
    unit_mateEquiv_symm σX τX (TwoSquare.mk _ _ _ _ ρX) (JE.obj N)
  have uY : eA.map (σY.unit.app N) ≫ ρY.app M =
      τY.unit.app (eA.obj N) ≫ rY.map (βY.app N) :=
    unit_mateEquiv_symm σY τY (TwoSquare.mk _ _ _ _ ρY) N
  have uβ : jE.map (τY.unit.app (eA.obj N)) ≫ qn.app (sY.obj (eA.obj N)) =
      τX.unit.app (jE.obj (eA.obj N)) ≫ rX.map (β.app (eA.obj N)) :=
    unit_mateEquiv_symm τY τX (TwoSquare.mk _ _ _ _ qn) (eA.obj N)
  have nX := ρX.naturality (SSP.app N)
  have nE := pE.naturality (σY.unit.app N)
  have nq := qn.naturality (βY.app N)
  simp only [Functor.comp_map] at nX nE nq
  apply (τX.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  erw [← reassoc_of% uβ]
  erw [τX.unit_naturality_assoc, reassoc_of% (Eq.symm uX), ← nX]
  rw [← eB.map_comp_assoc, ← uQ, eB.map_comp_assoc, ← reassoc_of% nE]
  erw [hcube M]
  erw [← reassoc_of% nq]
  rw [← jE.map_comp_assoc, ← jE.map_comp_assoc]
  erw [uY]

/-- If `f' ≫ f = 𝟙` and `g ≫ g' = 𝟙`, then `f = g` implies `f' = g'`. -/
theorem eq_of_inverse_eq {C : Type*} [Category C] {X Y : C} {f g : X ⟶ Y} {f' g' : Y ⟶ X}
    (hf : f' ≫ f = 𝟙 Y) (hg : g ≫ g' = 𝟙 X) (h : f = g) : f' = g' := by
  rw [← Category.comp_id f', ← hg, ← h, reassoc_of% hf]

/-- Assembly of the scalar/pullback evaluation cube from a cube of right-adjoint squares. -/
theorem scalarPullback_evaluation_cube
    {A A' B B' a a' b b' : Type*} [Category A] [Category A'] [Category B] [Category B']
    [Category a] [Category a'] [Category b] [Category b']
    {JE : A ⥤ B} {JL : A' ⥤ B'} {jE : a ⥤ b} {jL : a' ⥤ b'} {kE : b ⥤ a} {kL : b' ⥤ a'}
    (levelE : jE ⊣ kE) (levelL : jL ⊣ kL)
    {SY : A ⥤ A'} {RY : A' ⥤ A} (σY : SY ⊣ RY) {SX : B ⥤ B'} {RX : B' ⥤ B} (σX : SX ⊣ RX)
    {sY : a ⥤ a'} {rY : a' ⥤ a} (τY : sY ⊣ rY) {sX : b ⥤ b'} {rX : b' ⥤ b} (τX : sX ⊣ rX)
    (eA : A ⥤ a) (eA' : A' ⥤ a') (eB : B ⥤ b) (eB' : B' ⥤ b')
    (SSP : JE ⋙ SX ≅ SY ⋙ JL) (Q : RY ⋙ JE ⟶ JL ⋙ RX)
    (hSSP : SSP.hom = ((mateEquiv σY σX).symm (TwoSquare.mk _ _ _ _ Q)))
    (EX : SX ⋙ eB' ≅ eB ⋙ sX) (ρX : RX ⋙ eB ⟶ eB' ⋙ rX)
    (hEX : EX.inv = ((mateEquiv σX τX).symm (TwoSquare.mk _ _ _ _ ρX)))
    (EY : SY ⋙ eA' ≅ eA ⋙ sY) (ρY : RY ⋙ eA ⟶ eA' ⋙ rY)
    (hEY : EY.inv = ((mateEquiv σY τY).symm (TwoSquare.mk _ _ _ _ ρY)))
    (PE : eA ⋙ jE ≅ JE ⋙ eB) (PL : eA' ⋙ jL ≅ JL ⋙ eB')
    (D : rX ⋙ kE ≅ kL ⋙ rY)
    (hcube : ∀ M : A', PE.hom.app (RY.obj M) ≫ eB.map (Q.app M) ≫ ρX.app (JL.obj M) =
      jE.map (ρY.app M) ≫
        ((mateEquiv levelL levelE).symm (TwoSquare.mk _ _ _ _ D.inv)).app
          (eA'.obj M) ≫ rX.map (PL.hom.app M))
    (α : sY ⋙ jL ⟶ jE ⋙ sX)
    (hα : α = ((mateEquiv levelE levelL).symm ((mateEquiv τX τY).symm
        (TwoSquare.mk _ _ _ _ D.hom))))
    (N : A) :
    eB'.map (SSP.inv.app N) ≫ EX.hom.app (JE.obj N) ≫ sX.map (PE.inv.app N) =
      PL.inv.app (SY.obj N) ≫ jL.map (EY.hom.app N) ≫ α.app (eA.obj N) := by
  obtain ⟨-, hβα⟩ := iteratedMate_symm_hom_inv levelE levelL τY τX D
  rw [← hα] at hβα
  have h := scalarPullback_mate_pasting σY σX τY τX eA eA' eB eB' Q ρX ρY PE.hom PL.hom
    ((mateEquiv levelL levelE).symm (TwoSquare.mk _ _ _ _ D.inv)) hcube N
  rw [← hSSP, ← hEX, ← hEY] at h
  refine eq_of_inverse_eq ?_ ?_ h
  · simp [← Functor.map_comp_assoc, ← Functor.map_comp]
  · have e := congr_app hβα (eA.obj N)
    simp only [NatTrans.comp_app, NatTrans.id_app] at e
    simp only [Category.assoc]
    erw [Iso.hom_inv_id_app_assoc, ← jL.map_comp_assoc, Iso.inv_hom_id_app, jL.map_id,
      Category.id_comp]
    exact e


/-- Left mates of a commuting cube of right-adjoint squares form a commuting hexagon. -/
theorem leftMate_cube_of_rightCube
    {A A' B B' a a' b b' : Type*} [Category A] [Category A'] [Category B] [Category B']
    [Category a] [Category a'] [Category b] [Category b']
    {JE : A ⥤ B} {KE : B ⥤ A} (adjE : JE ⊣ KE) {JL : A' ⥤ B'} {KL : B' ⥤ A'} (adjL : JL ⊣ KL)
    {jE : a ⥤ b} {kE : b ⥤ a} (adjfE : jE ⊣ kE) {jL : a' ⥤ b'} {kL : b' ⥤ a'}
    (adjfL : jL ⊣ kL)
    {RY : A' ⥤ A} {RX : B' ⥤ B} {rY : a' ⥤ a} {rX : b' ⥤ b}
    {eA : A ⥤ a} {eB : B ⥤ b} {eA' : A' ⥤ a'} {eB' : B' ⥤ b'}
    (dE : KE ⋙ eA ⟶ eB ⋙ kE) (dL : KL ⋙ eA' ⟶ eB' ⋙ kL)
    (Qr : KL ⋙ RY ⟶ RX ⋙ KE) (qr : kL ⋙ rY ⟶ rX ⋙ kE)
    (ρY : RY ⋙ eA ⟶ eA' ⋙ rY) (ρX : RX ⋙ eB ⟶ eB' ⋙ rX)
    (hcube : ∀ N : B', eA.map (Qr.app N) ≫ dE.app (RX.obj N) ≫ kE.map (ρX.app N) =
      ρY.app (KL.obj N) ≫ rY.map (dL.app N) ≫ qr.app (eB'.obj N))
    (M : A') :
    ((mateEquiv adjE adjfE).symm (TwoSquare.mk _ _ _ _ dE)).app (RY.obj M) ≫
        eB.map (((mateEquiv adjL adjE).symm (TwoSquare.mk _ _ _ _ Qr)).app M) ≫
        ρX.app (JL.obj M) =
      jE.map (ρY.app M) ≫
        ((mateEquiv adjfL adjfE).symm (TwoSquare.mk _ _ _ _ qr)).app (eA'.obj M) ≫
        rX.map (((mateEquiv adjL adjfL).symm (TwoSquare.mk _ _ _ _ dL)).app M) := by
  let δE := ((mateEquiv adjE adjfE).symm (TwoSquare.mk _ _ _ _ dE))
  let Q := ((mateEquiv adjL adjE).symm (TwoSquare.mk _ _ _ _ Qr))
  let qn := ((mateEquiv adjfL adjfE).symm (TwoSquare.mk _ _ _ _ qr))
  let δL := ((mateEquiv adjL adjfL).symm (TwoSquare.mk _ _ _ _ dL))
  have uδE : eA.map (adjE.unit.app (RY.obj M)) ≫ dE.app (JE.obj (RY.obj M)) =
      adjfE.unit.app (eA.obj (RY.obj M)) ≫ kE.map (δE.app (RY.obj M)) :=
    unit_mateEquiv_symm adjE adjfE (TwoSquare.mk _ _ _ _ dE) (RY.obj M)
  have uQ : RY.map (adjL.unit.app M) ≫ Qr.app (JL.obj M) =
      adjE.unit.app (RY.obj M) ≫ KE.map (Q.app M) :=
    unit_mateEquiv_symm adjL adjE (TwoSquare.mk _ _ _ _ Qr) M
  have uqn : rY.map (adjfL.unit.app (eA'.obj M)) ≫ qr.app (jL.obj (eA'.obj M)) =
      adjfE.unit.app (rY.obj (eA'.obj M)) ≫ kE.map (qn.app (eA'.obj M)) :=
    unit_mateEquiv_symm adjfL adjfE (TwoSquare.mk _ _ _ _ qr) (eA'.obj M)
  have uδL : eA'.map (adjL.unit.app M) ≫ dL.app (JL.obj M) =
      adjfL.unit.app (eA'.obj M) ≫ kL.map (δL.app M) :=
    unit_mateEquiv_symm adjL adjfL (TwoSquare.mk _ _ _ _ dL) M
  have dEnat := dE.naturality (Q.app M)
  have ρYnat := ρY.naturality (adjL.unit.app M)
  have qrnat := qr.naturality (δL.app M)
  simp only [Functor.comp_map] at dEnat ρYnat qrnat
  have hL : adjfE.homEquiv _ _
      (δE.app (RY.obj M) ≫ eB.map (Q.app M) ≫ ρX.app (JL.obj M)) =
      eA.map (RY.map (adjL.unit.app M)) ≫ ρY.app (KL.obj (JL.obj M)) ≫
        rY.map (dL.app (JL.obj M)) ≫ qr.app (eB'.obj (JL.obj M)) := by
    rw [Adjunction.homEquiv_unit, kE.map_comp, kE.map_comp, ← Category.assoc,
      ← Category.assoc]
    erw [← uδE]
    rw [Category.assoc, Category.assoc]
    erw [← reassoc_of% dEnat]
    rw [← eA.map_comp_assoc]
    erw [← uQ]
    rw [eA.map_comp, Category.assoc, ← hcube (JL.obj M)]
  have hR : adjfE.homEquiv _ _
      (jE.map (ρY.app M) ≫ qn.app (eA'.obj M) ≫ rX.map (δL.app M)) =
      eA.map (RY.map (adjL.unit.app M)) ≫ ρY.app (KL.obj (JL.obj M)) ≫
        rY.map (dL.app (JL.obj M)) ≫ qr.app (eB'.obj (JL.obj M)) := by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit, kE.map_comp,
      ← Category.assoc (adjfE.unit.app _)]
    erw [← uqn]
    rw [Category.assoc]
    erw [← qrnat]
    rw [← rY.map_comp_assoc]
    erw [← uδL]
    rw [rY.map_comp, Category.assoc]
    erw [← reassoc_of% ρYnat]
    rfl
  apply (adjfE.homEquiv _ _).injective
  erw [hL, hR]


section General

variable (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory WeilConjectures.integralComparisonSequenceScalarModel

set_option profiler true in
set_option maxHeartbeats 5000000 in
-- the derived mate comparison unfolds several large adjunction composites
/-- The derived scalar/pullback comparison is the derived scalar mate of any localization
of an ordinary restriction/pullback square whose ordinary scalar mate is the ordinary
scalar/pullback comparison. No invertibility of the restriction square is needed. -/
theorem systemScalarPullback_eq_mate_general {X B : Scheme.{u}} (j : X ⟶ B)
    (AB : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (integralComparisonSequenceScalarMap l E L ι B))
    (AX : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (integralComparisonSequenceScalarMap l E L ι X))
    (MB : type_of% (integralComparisonSequenceScalarModel l E L ι B))
    (MX : type_of% (integralComparisonSequenceScalarModel l E L ι X))
    (hAB : AB.model = MB) (hAX : AX.model = MX)
    (σB : MB.T ⊣ (sequenceRestriction l E L ι B).mapDerivedCategory)
    (σX : MX.T ⊣ (sequenceRestriction l E L ι X).mapDerivedCategory)
    (hσB : HEq σB AB.adjunction) (hσX : HEq σX AX.adjunction)
    (oB : MB.E ⊣ sequenceRestriction l E L ι B)
    (oX : MX.E ⊣ sequenceRestriction l E L ι X)
    (huB : ∀ P U x, (oB.unit.app P).val.app U x =
      SheafOfModules.systemModelTmul MB P U 1 x)
    (huX : ∀ P U x, (oX.unit.app P).val.app U x =
      SheafOfModules.systemModelTmul MX P U 1 x)
    (q : sequenceRestriction l E L ι B ⋙ integralComparisonSequencePullback l E j ⟶
      integralComparisonSequencePullback l L j ⋙ sequenceRestriction l E L ι X)
    (Qd : (sequenceRestriction l E L ι B).mapDerivedCategory ⋙
        (integralComparisonSequencePullback l E j).mapDerivedCategory ⟶
      (integralComparisonSequencePullback l L j).mapDerivedCategory ⋙
        (sequenceRestriction l E L ι X).mapDerivedCategory)
    (hQd : Functor.IsDerivedSquareOf q Qd)
    (a : integralComparisonSequencePullback l E j ⋙ MX.E ≅
      MB.E ⋙ integralComparisonSequencePullback l L j)
    (ha : a.hom = ((mateEquiv oB oX).symm (TwoSquare.mk _ _ _ _ q)))
    (S : integralComparisonDerivedSequencePullback l E j ⋙ MX.T ≅
      MB.T ⋙ integralComparisonDerivedSequencePullback l L j)
    (hS : ∀ (P : CochainComplex (coefficientSequenceModules l E B) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E B) P →
      MX.T.map
          ((integralComparisonSequencePullback l E j).mapDerivedCategoryFactors.hom.app P) ≫
        MX.ε.app (((integralComparisonSequencePullback l E j).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app P) =
      S.hom.app (DerivedCategory.Q.obj P) ≫
        (integralComparisonDerivedSequencePullback l L j).map (MB.ε.app P) ≫
        (integralComparisonSequencePullback l L j).mapDerivedCategoryFactors.hom.app
          ((MB.E.mapHomologicalComplex (.up ℤ)).obj P)) :
    S.hom = ((mateEquiv σB σX).symm (TwoSquare.mk _ _ _ _ Qd)) := by
  subst hAB hAX
  obtain rfl := eq_of_heq hσB
  obtain rfl := eq_of_heq hσX
  have hoB : oB.unit = AB.ordinaryAdj.unit := by
    ext P U x
    rw [huB, AB.unit_normalized]
  have hoX : oX.unit = AX.ordinaryAdj.unit := by
    ext P U x
    rw [huX, AX.unit_normalized]
  unfold integralComparisonDerivedSequencePullback at S hS ⊢
  apply sequenceDerived_kflat_ext l E B
  intro P hP
  have : IsIso (AB.model.ε.app P) := AB.model.computes P hP
  let K := (AB.model.E.mapHomologicalComplex (.up ℤ)).obj P
  let kP : (AX.model.E.mapHomologicalComplex (.up ℤ)).obj
      (((integralComparisonSequencePullback l E j).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((integralComparisonSequencePullback l L j).mapHomologicalComplex (.up ℤ)).obj K :=
    (NatIso.mapHomologicalComplex a (.up ℤ)).hom.app P
  have hS' : AX.model.T.map
        ((integralComparisonSequencePullback l E j).mapDerivedCategoryFactors.hom.app P) ≫
      AX.model.ε.app (((integralComparisonSequencePullback l E j).mapHomologicalComplex
        (.up ℤ)).obj P) ≫ DerivedCategory.Q.map kP =
      S.hom.app (DerivedCategory.Q.obj P) ≫
        (integralComparisonSequencePullback l L j).mapDerivedCategory.map (AB.model.ε.app P) ≫
        (integralComparisonSequencePullback l L j).mapDerivedCategoryFactors.hom.app K :=
    hS P hP
  have h1 : AB.adjunction.homEquiv (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj ((AB.model.E.mapHomologicalComplex (.up ℤ)).obj P))
      (AB.model.ε.app P) =
      DerivedCategory.Q.map ((AB.ordinaryAdj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        (sequenceRestriction l E L ι B).mapDerivedCategoryFactors.inv.app K := by
    have e1 : AB.model.ε.app P ≫ DerivedCategory.Q.map (𝟙 K) = AB.model.ε.app P := by
      rw [CategoryTheory.Functor.map_id]
      exact Category.comp_id _
    rw [← e1]
    refine (AB.transpose P _ (𝟙 _)).trans ?_
    rw [Adjunction.homEquiv_id]
  have h2 := Qd.naturality (AB.model.ε.app P)
  simp only [Functor.comp_map] at h2
  have h3 := hQd K
  have h5 := (integralComparisonSequencePullback l E j).mapDerivedCategoryFactors_hom_naturality
    ((AB.ordinaryAdj.mapHomologicalComplex (.up ℤ)).unit.app P)
  apply (cancel_mono
    ((integralComparisonSequencePullback l L j).mapDerivedCategory.map (AB.model.ε.app P) ≫
    (integralComparisonSequencePullback l L j).mapDerivedCategoryFactors.hom.app K)).1
  rw [← hS']
  apply (AX.adjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  refine (congrArg (_ ≫ ·) (AX.transpose _ _ _)).trans ?_
  rw [Adjunction.homEquiv_unit AX.adjunction]
  have hm := (unit_mateEquiv_symm AB.adjunction AX.adjunction
    (TwoSquare.mk _ _ _ _ Qd) (DerivedCategory.Q.obj P)).symm
  dsimp only [Functor.id_obj] at hm
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, ← Category.assoc,
    ← Category.assoc]
  erw [hm]
  rw [Category.assoc, Category.assoc, ← reassoc_of% h2,
    ← CategoryTheory.Functor.map_comp_assoc, ← Adjunction.homEquiv_unit, h1]
  rw [← cancel_mono ((sequenceRestriction l E L ι X).mapDerivedCategoryFactors.hom.app
    (((integralComparisonSequencePullback l L j).mapHomologicalComplex (.up ℤ)).obj K))]
  simp only [Category.assoc]
  erw [h3]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    ← CategoryTheory.Functor.map_comp_assoc _
      ((sequenceRestriction l E L ι B).mapDerivedCategoryFactors.inv.app K)]
  erw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% h5, ← DerivedCategory.Q.map_comp]
  congr 2
  rw [Adjunction.homEquiv_unit]
  apply HomologicalComplex.hom_ext
  intro n
  have hu := unit_mateEquiv_symm oB oX (TwoSquare.mk _ _ _ _ q) (P.X n)
  rw [hoB, hoX] at hu
  simpa [kP, K, ha] using hu.symm


/-- A cast by `Eq.mpr` is heterogeneously equal to its argument. -/
private theorem mpr_heq_self.{w} {α β : Sort w} (h : α = β) (b : β) : HEq (Eq.mpr h b) b := by
  subst h
  rfl

/-- The fixed finite-evaluation scalar adjunction is the adjunction of the chosen model. -/
theorem finiteEvaluationSystemScalarAdjunction_heq_model (W : Scheme.{u}) :
    HEq (finiteEvaluationSystemScalarAdjunction l E L ι W)
      (finiteEvaluationSystemScalarModel_exists l E L ι W).choose.adjunction := by
  unfold finiteEvaluationSystemScalarAdjunction
  exact mpr_heq_self _ _

set_option profiler true in
set_option maxHeartbeats 1000000 in
-- the scalar/pullback comparison unfolds several large adjunction composites
/-- The derived scalar/pullback comparison is the inverse mate, along the fixed
finite-evaluation scalar adjunctions, of any localization of the ordinary
restriction/pullback comparison. -/
private theorem systemScalarPullback_hom_eq_finiteMate_general {X B : Scheme.{u}} (j : X ⟶ B)
    (Qd : (sequenceRestriction l E L ι B).mapDerivedCategory ⋙
        (integralComparisonSequencePullback l E j).mapDerivedCategory ⟶
      (integralComparisonSequencePullback l L j).mapDerivedCategory ⋙
        (sequenceRestriction l E L ι X).mapDerivedCategory)
    (hQd : Functor.IsDerivedSquareOf (sequenceRestrictionPullbackInv l E L ι j) Qd) :
    (integralComparisonSystemScalarPullback l E L ι j).hom =
      ((mateEquiv (finiteEvaluationSystemScalarAdjunction l E L ι B)
        (finiteEvaluationSystemScalarAdjunction l E L ι X)).symm
          (TwoSquare.mk _ _ _ _ Qd)) :=
  systemScalarPullback_eq_mate_general l E L ι j
    (finiteEvaluationSystemScalarModel_exists l E L ι B).choose
    (finiteEvaluationSystemScalarModel_exists l E L ι X).choose _ _
    (finiteEvaluationSystemScalarModel_exists l E L ι B).choose_spec
    (finiteEvaluationSystemScalarModel_exists l E L ι X).choose_spec _ _
    (finiteEvaluationSystemScalarAdjunction_heq_model l E L ι B)
    (finiteEvaluationSystemScalarAdjunction_heq_model l E L ι X)
    (sequenceScalarAdjunction l E L ι B).choose (sequenceScalarAdjunction l E L ι X).choose
    (fun P U x ↦ (sequenceScalarAdjunction_unit l E L ι B P U x).trans
      (sequenceTensorSection_eq l E L ι B P U 1 x))
    (fun P U x ↦ (sequenceScalarAdjunction_unit l E L ι X P U x).trans
      (sequenceTensorSection_eq l E L ι X P U 1 x))
    (sequenceRestrictionPullbackInv l E L ι j) Qd hQd
    (integralComparisonSequenceScalarPullback l E L ι j)
    (sequenceScalarPullback_hom_eq l E L ι j)
    (integralComparisonSystemScalarPullback l E L ι j)
    (integralComparisonSystemScalarPullback_existsUnique l E L ι j).exists.choose_spec

end General

section RestrictionEvaluation

open SemilinearSections

universe c v r

/-- A scalar evaluation square heterogeneously equal to the restriction-evaluation
comparison is the localization of an identity-on-sections ordinary square. -/
theorem restrictionEvaluation_isDerivedSquareOf {C : Type c} [Category.{v} C]
    [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
    (B : ℕ → Sheaf J CommRingCat.{r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
    (F : ℕ → Sheaf J CommRingCat.{r}) (σ : ∀ n : ℕ, F (n + 1) ⟶ F n)
    (α : ∀ n : ℕ, B n ⟶ F n) (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n) (n : ℕ)
    (φ : systemRing.{c, v, r} J B τ ⟶ systemRing.{c, v, r} J F σ)
    (hφ : systemMap.{c, v, r} J B τ F σ α hα = φ)
    (ρ : resD.{c, v, r} φ ⋙ e.{c, v, r} J B τ n ⟶ e.{c, v, r} J F σ n ⋙ resD.{c, v, r} (α n))
    (hρ : HEq ρ (restrictionEvaluation.{c, v, r} J B τ F σ α hα n).hom) :
    ∃ ρ₀ : res.{c, v, r} φ ⋙ SemilinearSections.evaluation.{c, v, r} J B τ n ⟶
        SemilinearSections.evaluation.{c, v, r} J F σ n ⋙ res.{c, v, r} (α n),
      (∀ (M : Systems.{c, v, r} J F σ) (U : Cᵒᵖ),
        HEq (fun x ↦ ((ρ₀.app M).val.app U) x)
          (fun x : M.val.obj (op (n, U.unop)) ↦ x)) ∧
      Functor.IsDerivedSquareOf ρ₀ ρ := by
  subst hφ
  obtain rfl := eq_of_heq hρ
  exact ⟨_, (restrictionEvaluation_existsUnique.{c, v, r} J B τ F σ α hα n).exists.choose_spec,
    Functor.isDerivedSquareOf_mapDerivedCategorySquareIso _⟩

end RestrictionEvaluation

section SystemRestrictionEvaluation

variable (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Finite-level scalar restriction is additive on normalized coefficient modules. -/
instance normalizedRestrictScalars_additive (W : Scheme.{u}) (n : ℕ) :
    @Functor.Additive (normalizedDVRModules l L W n) (normalizedDVRModules l E W n) _ _ _ _
      (proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n)) :=
  inferInstanceAs
    (proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n)).Additive

/-- Finite-level scalar restriction is left exact on normalized coefficient modules. -/
instance normalizedRestrictScalars_preservesFiniteLimits (W : Scheme.{u}) (n : ℕ) :
    @PreservesFiniteLimits (normalizedDVRModules l L W n) _ (normalizedDVRModules l E W n) _
      (proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n)) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteLimits _ _

/-- Finite-level scalar restriction is right exact on normalized coefficient modules. -/
instance normalizedRestrictScalars_preservesFiniteColimits (W : Scheme.{u}) (n : ℕ) :
    @PreservesFiniteColimits (normalizedDVRModules l L W n) _ (normalizedDVRModules l E W n) _
      (proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n)) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteColimits _ _

set_option profiler true in
set_option maxHeartbeats 2000000 in
-- comparing the semilinear-system presentation with the sequence-site presentation
/-- The scalar evaluation square of the normalized finite evaluation is the localization of
an identity-on-sections ordinary restriction-evaluation square. -/
theorem systemRestrictionEvaluation_isDerivedSquareOf (W : Scheme.{u}) (n : ℕ)
    (ρ : TwoSquare (SemilinearSections.resD (integralComparisonSequenceScalarMap l E L ι W))
        (coefficientSequenceDerivedEvaluation l L W n)
        (coefficientSequenceDerivedEvaluation l E W n)
        (pbcDerivedRestrict (FiniteCompactScalar.scalarRingMap
          (integralScalarQuotientMap l E L ι n) W)))
    (hρ : HEq ρ (SemilinearSections.restrictionEvaluation (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
        (integralScalarQuotientSheafMap l E L ι W)
        (scalarQuotient_compatible l E L ι W) n).hom) :
    ∃ ρ₀ : sequenceRestriction l E L ι W ⋙ coefficientSequenceEvaluation l E W n ⟶
        coefficientSequenceEvaluation l L W n ⋙
          proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n),
      (∀ (M : coefficientSequenceModules l L W) (U : W.ProEtᵒᵖ),
        HEq (fun x ↦ ((ρ₀.app M).val.app U) x) (fun x : M.val.obj (op (n, U.unop)) ↦ x)) ∧
      Functor.IsDerivedSquareOf ρ₀ ρ := by
  obtain ⟨ρ₀, h₁, h₂⟩ := restrictionEvaluation_isDerivedSquareOf (ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
    (integralScalarQuotientSheafMap l E L ι W) (scalarQuotient_compatible l E L ι W) n
    (integralComparisonSequenceScalarMap l E L ι W) (scalarSystemMap_eq l E L ι W)
    ρ hρ
  exact ⟨ρ₀, h₁, h₂⟩

end SystemRestrictionEvaluation

/-- The finite inverse geometric mate of the derived direct-image restriction comparison
is the localization of the ordinary inverse mate of the identity-on-sections comparison. -/
theorem sfDerivedImageRestriction_inverseMate_isDerivedSquareOf
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.IsDerivedSquareOf
      ((mateEquiv (sfIntrinsicConstantModuleAdjunction f B)
        (sfIntrinsicConstantModuleAdjunction f A)).symm
        (TwoSquare.mk _ _ _ _ (proEtaleCoefficientDirectImageComparison f φ).hom))
      ((mateEquiv
        (sfIntrinsicConstantModuleAdjunction f B).mapDerivedCategoryRightDerivedAdjunction
        (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction).symm
        (TwoSquare.mk _ _ _ _ (sfDerivedImageRestriction f φ).inv)) := by
  intro P
  have h := compactSupportScalarDirectNormalization f φ
  unfold CategoryTheory.ExactDerivedSquare.unitNormalized at h
  exact WeilConjectures.IntegralSystemRealization.inverse_mate_model _ _ _ _ h P

/-- A function heterogeneously equal to an identity sends each element to a heterogeneously
equal element. -/
theorem heq_apply_of_heq_id.{w} {A B T : Type w} (g : A → B) (hg : HEq g (fun x : T ↦ x))
    (hA : A = T) (hB : B = T) (y : A) : HEq (g y) y := by
  subst hA hB
  obtain rfl := eq_of_heq hg
  rfl

/-- The sections of an `eqToHom` between equal functors into module sheaves are
heterogeneously the identity. -/
theorem eqToHom_app_val_app_heq {C : Type*} [Category C] {D : Type*} [Category D]
    {J : GrothendieckTopology D} {R : Sheaf J RingCat.{u + 1}}
    {F G : C ⥤ SheafOfModules.{u + 1} R} (h : F = G) (N : C) (W : Dᵒᵖ)
    (x : (F.obj N).val.obj W) :
    HEq ((((eqToHom h).app N).val.app W) x) x := by
  subst h
  rfl

section OrdinaryCube

variable (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Sections of a finite direct-image map are the sections over the base change. -/
theorem directImage_map_val_app {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    {M M' : proEtaleRingModules X (proEtaleConstantRing X A)} (g : M ⟶ M') (W : Y.ProEtᵒᵖ)
    (y : M.val.obj ((proEtaleBaseChange f).op.obj W)) :
    (((proEtaleConstantModuleDirectImage f A).map g).val.app W).hom y =
      (g.val.app ((proEtaleBaseChange f).op.obj W)).hom y := rfl

/-- Restriction of scalars does not change the section maps of a morphism. -/
theorem coefficientRestrictScalars_map_val_app (X : Scheme.{u}) {A B : Type u} [CommRing A]
    [CommRing B] (φ : A →+* B) {M M' : proEtaleRingModules X (proEtaleConstantRing X B)}
    (g : M ⟶ M') (W : X.ProEtᵒᵖ) (y : M.val.obj W) :
    (((proEtaleCoefficientRestrictScalars X φ).map g).val.app W).hom y = (g.val.app W).hom y :=
  rfl

/-- Sections of an evaluated system map are its sections at the evaluated level. -/
theorem sequenceEvaluation_map_val_app (W : Scheme.{u}) (n : ℕ)
    {M M' : coefficientSequenceModules l E W} (g : M ⟶ M') (U : W.ProEtᵒᵖ)
    (y : M.val.obj (op (n, U.unop))) :
    (((coefficientSequenceEvaluation l E W n).map g).val.app U).hom y =
      (g.val.app (op (n, U.unop))).hom y := rfl


/-- Finite scalar restriction does not change the section maps of a normalized morphism. -/
theorem normalizedRestrictScalars_map_val_app {W : Scheme.{u}} {n : ℕ}
    {M M' : normalizedDVRModules l L W n} (g : M ⟶ M') (U : W.ProEtᵒᵖ) (y : M.val.obj U) :
    (((proEtaleCoefficientRestrictScalars W (integralScalarQuotientMap l E L ι n)).map
      g).val.app U).hom y = (g.val.app U).hom y := rfl

/-- The sections of an `eqToIso` between equal functors into normalized coefficient modules
are heterogeneously the identity. -/
theorem eqToIso_hom_app_val_app_heq {C : Type*} [Category C] (K : Type u) [Field K]
    [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K] {W : Scheme.{u}} {n : ℕ}
    {F G : C ⥤ normalizedDVRModules l K W n} (h : F = G) (M : C) (U : W.ProEtᵒᵖ)
    (y : (F.obj M).val.obj U) :
    HEq ((((eqToIso h).hom.app M).val.app U).hom y) y := by
  subst h
  rfl

set_option profiler true in
set_option maxHeartbeats 1000000 in
-- sectionwise comparison of identity-on-sections squares
/-- The ordinary cube of right-adjoint squares: direct image, restriction of scalars and
finite evaluation commute compatibly, since every comparison is the identity on sections. -/
private theorem ordinaryDirectRestrictionEvaluation_cube {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (dE : integralComparisonSequenceDirectImage l E f ⋙ coefficientSequenceEvaluation l E Y n ⟶
      coefficientSequenceEvaluation l E X n ⋙
        proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)))
    (pdE : ∀ (M : coefficientSequenceModules l E X) (U : Y.ProEtᵒᵖ)
      (y : ((integralComparisonSequenceDirectImage l E f ⋙
        coefficientSequenceEvaluation l E Y n).obj M).val.obj U),
      HEq (((dE.app M).val.app U).hom y) y)
    (dL : integralComparisonSequenceDirectImage l L f ⋙ coefficientSequenceEvaluation l L Y n ⟶
      coefficientSequenceEvaluation l L X n ⋙
        proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l L (n + 1)))
    (pdL : ∀ (M : coefficientSequenceModules l L X) (U : Y.ProEtᵒᵖ)
      (y : ((integralComparisonSequenceDirectImage l L f ⋙
        coefficientSequenceEvaluation l L Y n).obj M).val.obj U),
      HEq (((dL.app M).val.app U).hom y) y)
    (ρY : sequenceRestriction l E L ι Y ⋙ coefficientSequenceEvaluation l E Y n ⟶
      coefficientSequenceEvaluation l L Y n ⋙
        proEtaleCoefficientRestrictScalars Y (integralScalarQuotientMap l E L ι n))
    (hρY : ∀ (M : coefficientSequenceModules l L Y) (U : Y.ProEtᵒᵖ),
      HEq (fun x ↦ ((ρY.app M).val.app U) x) (fun x : M.val.obj (op (n, U.unop)) ↦ x))
    (ρX : sequenceRestriction l E L ι X ⋙ coefficientSequenceEvaluation l E X n ⟶
      coefficientSequenceEvaluation l L X n ⋙
        proEtaleCoefficientRestrictScalars X (integralScalarQuotientMap l E L ι n))
    (hρX : ∀ (M : coefficientSequenceModules l L X) (U : X.ProEtᵒᵖ),
      HEq (fun x ↦ ((ρX.app M).val.app U) x) (fun x : M.val.obj (op (n, U.unop)) ↦ x))
    (N : coefficientSequenceModules l L X) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
    (coefficientSequenceEvaluation l E Y n).map
        ((sequenceScalarPullbackRight l E L ι f).inv.app N) ≫
      dE.app ((sequenceRestriction l E L ι X).obj N) ≫
      (proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1))).map
        (ρX.app N) =
    ρY.app ((integralComparisonSequenceDirectImage l L f).obj N) ≫
      (proEtaleCoefficientRestrictScalars Y (integralScalarQuotientMap l E L ι n)).map
        (dL.app N) ≫
      (proEtaleCoefficientDirectImageComparison f (integralScalarQuotientMap l E L ι n)).hom.app
        ((coefficientSequenceEvaluation l L X n).obj N) := by
  have pX (M : coefficientSequenceModules l L X) (U : X.ProEtᵒᵖ)
      (y : M.val.obj (op (n, U.unop))) : HEq (((ρX.app M).val.app U).hom y) y :=
    heq_apply_of_heq_id _ (hρX M U) rfl rfl y
  have pY (M : coefficientSequenceModules l L Y) (U : Y.ProEtᵒᵖ)
      (y : M.val.obj (op (n, U.unop))) : HEq (((ρY.app M).val.app U).hom y) y :=
    heq_apply_of_heq_id _ (hρY M U) rfl rfl y
  ext W x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  apply eq_of_heq
  refine HEq.trans (b := x) ?_ ?_
  · refine (heq_of_eq (directImage_map_val_app f _ (ρX.app N) W _)).trans ?_
    refine (pX N _ _).trans ?_
    refine (pdE _ W _).trans ?_
    refine (heq_of_eq (sequenceEvaluation_map_val_app l E Y n _ W x)).trans ?_
    exact heq_of_eq (sequenceScalarPullbackRight_inv_app l E L ι f N _ x)
  · refine HEq.symm ((heq_of_eq ((Classical.choose_spec
      (proEtaleCoefficientDirectImageComparison_existsUnique f
        (integralScalarQuotientMap l E L ι n))).1 _ W _)).trans ?_)
    refine (heq_of_eq (normalizedRestrictScalars_map_val_app l E L ι (dL.app N) W _)).trans ?_
    refine (pdL N W _).trans ?_
    exact pY _ W x

end OrdinaryCube

end WeilConjectures.FrobeniusExchange
