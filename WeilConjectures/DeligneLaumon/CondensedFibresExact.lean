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
public import WeilConjectures.DeligneLaumon.CondensedFibresExactFinite
public import WeilConjectures.DeligneLaumon.CondensedFibresExactRank
public import WeilConjectures.DeligneLaumon.CondensedFibresExactSequence

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

/-- Exact finite-dimensional fibres and their canonical local Frobenius actions.
Source: literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-lem-wrp-l2-growth/
lem-wf-l2-upper.proof.md, opening sentence
(blueprint: lem-wf-condensed-fibres-exact).

Proof: (1) Cartesian coefficients make module inverse image exact, as its underlying
abelian inverse image is exact. Field-point sections are exact because covers on the
pro-etale site of the algebraically closed field split. Apply the exact heart inclusion.
(2) Factor the geometric point through a constructible stratum and pull a local finite
basis back to the field point. A section of a nonempty covering member splits its local
trivialization, so this point module is finite free.
(3) The coefficient sections identify with PadicAlgCl l by constant functions and
singleton evaluation. A rank-r basis gives the r coordinate vectors and dimension r,
including r=0. This gives all finite-dimensionality and coefficient-unit assertions.
(4) At a closed point of degree d, geometric Frobenius to the d-th power fixes the
embedded finite residue field. The two geometric-fibre projections give the semilinear
return localClosedPoint_return. The inverse canonical point comparison reparametrizes
sections and is linear over the constant coefficients.
(5) Compose the reparametrization, return comparisons and d-fold Weil isomorphism,
as in the recorded CondensedModule.operator. Each factor is invertible.
(6) Naturality and the Weil-morphism square give the two intertwining equations.
Exactness from (1) and finiteness from (3) give the claimed short exact sequence. -/
def condensedFibresExactAssertions
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (_hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) : Prop :=
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    fibreFunctorAssertions
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber Y₀).left)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        CondensedRing.pointSections l D.k)
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l)
        (D.geometricFiber Y₀).left)) ∧
    fibreRankAssertions l (D.geometricFiber Y₀).left
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        CondensedRing.pointSections l D.k) ∧
    (∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
        (ι : Y₀.left.residueField y.val →+* D.k)
        (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k),
      fibreWeilSequenceAssertions
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
          (D.geometricFiber Y₀).left)
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (D.geometricFrobenius Y₀).hom)
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
            (localClosedPoint D Y₀ y ι hι) ⋙ CondensedRing.pointSections l D.k)
        (fun M ↦ CondensedModule.operator l D (D.geometricFrobenius Y₀).hom M.carrier M.str
            (localClosedPoint D Y₀ y ι hι) (localClosedPointDegree D Y₀ y - 1)
            (localClosedPoint_return D Y₀ y ι hι)))

end WeilConjectures

namespace WeilConjectures

/-- Exact finite-dimensional constructible fibres, rank, and the equivariance of short
exact sequences for the canonical local Frobenius.
Source: literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-lem-wrp-l2-growth/
lem-wf-l2-upper.proof.md, opening sentence
(blueprint: lem-wf-condensed-fibres-exact).

Proof: the assertion is a conjunction of three clauses. Exactness, additivity,
finite-dimensionality and the unit fibre are `condensed_fibres_point_finiteness`; the rank
clause is `condensed_fibres_point_rank`; for every closed point and residue embedding, the
Frobenius-equivariant exact sequences are `condensed_fibres_point_sequence`. -/
theorem condensed_fibres_exact
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    condensedFibresExactAssertions D l hl Y₀ z hz := by
  unfold condensedFibresExactAssertions
  refine ⟨condensed_fibres_point_finiteness D l hl Y₀ z hz,
    condensed_fibres_point_rank D l hl Y₀ z hz, ?_⟩
  intro y ι hι
  exact condensed_fibres_point_sequence D l hl Y₀ y ι hι

end WeilConjectures
