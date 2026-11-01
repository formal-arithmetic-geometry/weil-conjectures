/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius

/-! # Exact finite-dimensional fibres of constructible condensed Weil modules

Source: literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-lem-wrp-l2-growth/
lem-wf-l2-upper.proof.md,
opening sentence: pass the punctual mixed filtration to finite-dimensional Frobenius-stable stalks
(blueprint: lem-wf-condensed-fibres-exact).

The scalar field is the standard size lift `ULift (PadicAlgCl l)`, identified with the
specified algebraic closure by `ULift.ringEquiv`. The condensed coefficient ring is unchanged.
-/

@[expose] public section
set_option autoImplicit false
universe u v w v'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Endofunctor
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Exactness, additivity, finite-dimensional values and the coefficient-unit fibre.
Source: literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-lem-wrp-l2-growth/
lem-wf-l2-upper.proof.md, opening sentence
(blueprint: lem-wf-condensed-fibres-exact). -/
def fibreFunctorAssertions
    {C : Type u} [Category.{v} C] [Preadditive C]
    {K : Type w} [Field K] (P : ObjectProperty C)
    (V : C ⥤ ModuleCat.{v'} K) (A : C) : Prop :=
  PreservesFiniteLimits (P.ι ⋙ V) ∧ PreservesFiniteColimits (P.ι ⋙ V) ∧
    (P.ι ⋙ V).Additive ∧
    (∀ M : P.FullSubcategory, FiniteDimensional K (V.obj M.obj)) ∧
    Nonempty (V.obj A ≃ₗ[K] K)

/-- A lisse module of constant local rank r has fibre dimension r.
Source: literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-lem-wrp-l2-growth/
lem-wf-l2-upper.proof.md, opening sentence
(blueprint: lem-wf-condensed-fibres-exact). -/
def fibreRankAssertions (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (V : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) Y) ⥤
        ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))) : Prop :=
  ∀ (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) Y)) (r : ℕ),
    (∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i : U.I₀,
      Nonempty ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (U.f i)).obj M ≅
        Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l) (U.X i)) r)) →
    Module.finrank (ULift.{u + 1} (PadicAlgCl l)) (V.obj M) = r

/-- Short exact sequences of constructible Weil modules give finite-dimensional short
exact sequences intertwining the specified local automorphisms on both arrows.
Source: literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-lem-wrp-l2-growth/
lem-wf-l2-upper.proof.md, opening sentence
(blueprint: lem-wf-condensed-fibres-exact). -/
def fibreWeilSequenceAssertions
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {K : Type w} [Field K] (P : ObjectProperty C) (G : C ⥤ C)
    (V : C ⥤ ModuleCat.{v'} K)
    (τ : ∀ M : IsoAlgebra G, End (V.obj M.carrier)) : Prop :=
  ∀ (F₁ F₂ F₃ : IsoAlgebra G) (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃),
    P F₁.carrier → P F₂.carrier → P F₃.carrier →
    Mono f.hom.f → Epi g.hom.f → (ComposableArrows.mk₂ f.hom.f g.hom.f).Exact →
    IsIso (τ F₁) ∧ IsIso (τ F₂) ∧ IsIso (τ F₃) ∧
    FiniteDimensional K (V.obj F₁.carrier) ∧
    FiniteDimensional K (V.obj F₂.carrier) ∧
    FiniteDimensional K (V.obj F₃.carrier) ∧
    Function.Injective (V.map f.hom.f).hom ∧
    Function.Exact (V.map f.hom.f).hom (V.map g.hom.f).hom ∧
    Function.Surjective (V.map g.hom.f).hom ∧
    (V.map f.hom.f ≫ τ F₂ = τ F₁ ≫ V.map f.hom.f) ∧
    (V.map g.hom.f ≫ τ F₃ = τ F₂ ≫ V.map g.hom.f)

end WeilConjectures
