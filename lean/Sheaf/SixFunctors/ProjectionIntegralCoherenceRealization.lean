/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups N6 and D2
-/
module

public import Sheaf.SixFunctors.ProjectionSystemCoherence
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Exact.Basic
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison

/-! # Integral realization of projection coherence

Source: blueprint main-20261015, fix-prop-projection-formula, integral coherence
(blueprint: lem-sf-projection-integral-coherence-realization).

The two variables are K on X and L on Z. Expressions retain the intermediate schemes,
morphisms, compactifications and parenthesizations. `CanonicalPair` includes the actual
projection composite, inverses of structural isomorphisms, finite composition, and
whiskering inside expressions. The imported route constructors
fix the composition, proper/open, refinement, identity and pentagon routes by formulas.
Their realized equalities are asserted without assuming equality of the system routes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The concrete route equations hold as morphism equalities in the derived category
of strict semilinear systems, including every displayed outer functor context.

Source: blueprint fix-prop-projection-formula, integral coherence, step 4;
Stacks 0F7B--0F7K; the system clauses of projection-compatible-triangle-assembly,
proper-open-projection-mate, projection-refinement-descent and ambient-proper-open-pasting
(blueprint: lem-sf-projection-integral-coherence-realization).

Proof: induct on the route. The four generating cases are the four clauses of
projectionSystemGeneratingEquations. Vertical and horizontal pasting are the fields
of rho.properOpen. For threeCell use naturality of Gamma_C at Gamma_A, postcomposed
with the image of Gamma_B. The remaining cases preserve equality by functoriality. -/
private theorem projectionSystemCoherenceRoutes_eq
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (ρ : Realizations l E D o)
    {W : Scheme.{u}} {A B : System l E W} {s t : A ⟶ B}
    (h : ProjectionCoherenceRoutes l E D o ρ s t) : s = t := by
  have hg := projectionSystemGeneratingEquations l E D o ρ
  induction h with
  | composition f g cf cg d sq M N => exact hg.1 f g cf cg d sq M N
  | properOpen k r p i h M N => exact hg.2.1 k r p i h M N
  | refinement f c₁ c₂ v w M N hM hT => exact hg.2.2.1 f c₁ c₂ v w M N hM hT
  | identity W M N => exact hg.2.2.2 W M N
  | vertical => apply ρ.properOpen.vertical
  | horizontal => apply ρ.properOpen.horizontal
  | threeCell a b d k i m r p q v ha hb hc sa sb sc M =>
    simpa only [Category.assoc, Functor.comp_map, Functor.comp_obj] using
      congrArg (fun z ↦ z ≫ (Operations.push l E o v.left).map
        ((ρ.properOpen.gamma b.left r.left p.left k.left hb).app
          ((Operations.shriek l E o a.left).obj M)))
        ((ρ.properOpen.gamma k.left q.left v.left i.left hc).naturality
          ((ρ.properOpen.gamma a.left m.left r.left d.left ha).app M))
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | comp _ _ ih₁ ih₂ => rw [ih₁, ih₂]
  | pull f _ ih => exact congrArg (fun z ↦ (pull l E f).map z) ih
  | push f _ ih => exact congrArg (fun z ↦ (Operations.push l E o f).map z) ih
  | shriek f _ ih => exact congrArg (fun z ↦ (Operations.shriek l E o f).map z) ih
  | compactSupport cf _ ih =>
    exact congrArg (fun z ↦
      (Operations.shriek l E o cf.i ⋙ Operations.push l E o cf.g).map z) ih
  | tensor _ _ ih₁ ih₂ => rw [ih₁, ih₂]


/-- The principal uniformizer quotient has its two-term free resolution.
Source: the DVR assertions of def-weil-l-adic-coefficient-extension and the elementary
principal-ideal quotient calculation. -/
private theorem projectionCoefficientResolution (n : ℕ) :
    Function.Injective (fun x : Padic.coefficientExtensionIntegers l E ↦
      Padic.coefficientExtensionUniformizer l E ^ n * x) ∧
    Function.Exact (fun x : Padic.coefficientExtensionIntegers l E ↦
      Padic.coefficientExtensionUniformizer l E ^ n * x)
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)) ∧
    Function.Surjective (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)) := by
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hm0 : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
    h.2.2.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hpi : Padic.coefficientExtensionUniformizer l E ≠ 0 := by
    intro hz
    apply hm0
    rw [← hgen, hz, Ideal.span_singleton_zero]
  refine ⟨mul_right_injective₀ (pow_ne_zero n hpi), ?_, Ideal.Quotient.mk_surjective⟩
  intro x
  rw [Ideal.Quotient.eq_zero_iff_mem]
  simp only [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, dvd_def]
  constructor <;> rintro ⟨c, hc⟩ <;> exact ⟨c, hc.symm⟩

/-- Canonical generators and their finite paths intertwine with the specified integral
maps. The concrete projection composition, proper/open, refinement,
identity and pasting routes are equal after realization, with their outer contexts.
The quotient clause records the exact two-term finite-free resolution in degrees -1,0.

Source: blueprint main-20261015, fix-prop-projection-formula, integral coherence
(blueprint: lem-sf-projection-integral-coherence-realization).

Proof:
1. The coherence field of the recorded realization intertwines every CanonicalPair,
including finite composition and all outer expression contexts. Apply it directly.
2. Soundness of the concrete system routes gives equality before total limit. Apply
the limit functor and conjugate by the fixed endpoint comparison isomorphisms.
For two canonical integral realizations, their intertwining equations now have equal
left sides. Cancel the invertible source comparison to obtain equality of integral maps.
3. The coefficient uniformizer generates the nonzero maximal ideal, so it is nonzero.
The coefficient ring is a subring of the field E, hence multiplication by every power
of the uniformizer is injective. The kernel of the surjective quotient map is the
principal ideal generated by that power. This proves the two-term resolution,
including n=1; the argument also proves the algebraic assertion at n=0.
No step uses faithfulness of derived finite evaluation on morphisms. -/
theorem projectionIntegralCoherenceRealization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (ρ : Realizations l E D o) :
    (∀ {I : Type u} [Finite I] (_hcard : Nat.card I = 2)
      {X : I → Over (Spec (CommRingCat.of D.k))} (iL : I)
      {W : Over (Spec (CommRingCat.of D.k))}
      (e t : Expression _ I X W) (ge : e.geometric) (gt : t.geometric)
      (K : (e.domain l E o).FullSubcategory) (ht : t.domain l E o K.obj)
      (_hL : finiteTorConstructibleIntegral l E (X iL).left (K.obj iL))
      (s₁ s₂ : @Quiver.Hom (System l E W.left) inferInstance
        (e.systemObj l E o ((inputReduction l E X).obj K.obj))
        (t.systemObj l E o ((inputReduction l E X).obj K.obj)))
      (r₁ r₂ : @Quiver.Hom (Integral l E W.left) inferInstance
        ((e.evaluate (integralInterpretation l E)).obj K.obj)
        ((t.evaluate (integralInterpretation l E)).obj K.obj)),
      (CanonicalPair l E o ρ.compositors ρ.openComparisons ρ.canonicalBridge ρ.properOpen
        ρ.ringedModels ρ.ringedOpenComparisons ρ.ringedProperOpen
        ((inputReduction l E X).obj K.obj) K.obj e t s₁ r₁ →
        ((coefficientSequenceLimit l E W.left).map s₁ ≫
            (ρ.comparison t gt).hom.app ⟨K.obj, ht⟩ =
          (ρ.comparison e ge).hom.app K ≫ r₁)) ∧
      (ProjectionCoherenceRoutes l E D o ρ s₁ s₂ →
        ((ρ.comparison e ge).inv.app K ≫
          (coefficientSequenceLimit l E W.left).map s₁ ≫
            (ρ.comparison t gt).hom.app ⟨K.obj, ht⟩ =
          (ρ.comparison e ge).inv.app K ≫
            (coefficientSequenceLimit l E W.left).map s₂ ≫
              (ρ.comparison t gt).hom.app ⟨K.obj, ht⟩) ∧
        (CanonicalPair l E o ρ.compositors ρ.openComparisons ρ.canonicalBridge ρ.properOpen
          ρ.ringedModels ρ.ringedOpenComparisons ρ.ringedProperOpen
          ((inputReduction l E X).obj K.obj) K.obj e t s₁ r₁ →
          CanonicalPair l E o ρ.compositors ρ.openComparisons ρ.canonicalBridge ρ.properOpen
          ρ.ringedModels ρ.ringedOpenComparisons ρ.ringedProperOpen
          ((inputReduction l E X).obj K.obj) K.obj e t s₂ r₂ → r₁ = r₂))) ∧
    (∀ (n : ℕ) (_hn : 1 ≤ n),
      Function.Injective (fun x : Padic.coefficientExtensionIntegers l E ↦
        Padic.coefficientExtensionUniformizer l E ^ n * x) ∧
      Function.Exact (fun x : Padic.coefficientExtensionIntegers l E ↦
        Padic.coefficientExtensionUniformizer l E ^ n * x)
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)) ∧
      Function.Surjective (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n))) := by
  constructor
  · intro I _ _ X iL W e t ge gt K ht _ s₁ s₂ r₁ r₂
    refine ⟨ρ.coherence e t ge gt K ht s₁ r₁, ?_⟩
    intro hroute
    have hs := projectionSystemCoherenceRoutes_eq l E D _hl o ρ hroute
    refine ⟨by rw [hs], ?_⟩
    intro h₁ h₂
    have h₁' := ρ.coherence e t ge gt K ht s₁ r₁ h₁
    have h₂' := ρ.coherence e t ge gt K ht s₂ r₂ h₂
    apply (cancel_epi ((ρ.comparison e ge).hom.app K)).1
    rw [← h₁', ← h₂', hs]
  · intro n _
    exact projectionCoefficientResolution l E n

/-- The three-edge and two-edge integral routes of the compact-support associativity
pentagon agree. The route index is generated by the displayed three-cell and pasting
formulas, including their compact-support contexts; it does not assume system equality.
Source: integral coherence, proof step 4; lem-sf-three-cell-compositor
(blueprint: lem-sf-projection-integral-coherence-realization).
Proof: expand all five edges into the specified proper/open and compositor factors.
The three-cell equation and the horizontal/vertical pasting equations relate the
expanded routes in their outer contexts. Apply projectionIntegralCoherenceRealization
to this concrete pair of routes; CanonicalPair.comp identifies their integral maps.
The intermediate realization comparisons cancel, giving the displayed equality. -/
theorem projectionIntegralAssociativityPentagon
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (ρ : Realizations l E D o)
    {I : Type u} [Finite I] (_hcard : Nat.card I = 2)
    {X : I → Over (Spec (CommRingCat.of D.k))} (iL : I)
    {W : Over (Spec (CommRingCat.of D.k))}
    (e₀ e₁ e₂ e₃ e₄ : Expression _ I X W)
    (_g₀ : e₀.geometric) (_g₁ : e₁.geometric) (_g₂ : e₂.geometric)
    (_g₃ : e₃.geometric) (_g₄ : e₄.geometric)
    (K : (e₀.domain l E o).FullSubcategory)
    (_h₁ : e₁.domain l E o K.obj) (_h₂ : e₂.domain l E o K.obj)
    (_h₃ : e₃.domain l E o K.obj) (_h₄ : e₄.domain l E o K.obj)
    (_hL : finiteTorConstructibleIntegral l E (X iL).left (K.obj iL))
    (s01 : e₀.systemObj l E o ((inputReduction l E X).obj K.obj) ⟶
      e₁.systemObj l E o ((inputReduction l E X).obj K.obj))
    (r01 : (e₀.evaluate (integralInterpretation l E)).obj K.obj ⟶
      (e₁.evaluate (integralInterpretation l E)).obj K.obj)
    (s12 : e₁.systemObj l E o ((inputReduction l E X).obj K.obj) ⟶
      e₂.systemObj l E o ((inputReduction l E X).obj K.obj))
    (r12 : (e₁.evaluate (integralInterpretation l E)).obj K.obj ⟶
      (e₂.evaluate (integralInterpretation l E)).obj K.obj)
    (s24 : e₂.systemObj l E o ((inputReduction l E X).obj K.obj) ⟶
      e₄.systemObj l E o ((inputReduction l E X).obj K.obj))
    (r24 : (e₂.evaluate (integralInterpretation l E)).obj K.obj ⟶
      (e₄.evaluate (integralInterpretation l E)).obj K.obj)
    (s03 : e₀.systemObj l E o ((inputReduction l E X).obj K.obj) ⟶
      e₃.systemObj l E o ((inputReduction l E X).obj K.obj))
    (r03 : (e₀.evaluate (integralInterpretation l E)).obj K.obj ⟶
      (e₃.evaluate (integralInterpretation l E)).obj K.obj)
    (s34 : e₃.systemObj l E o ((inputReduction l E X).obj K.obj) ⟶
      e₄.systemObj l E o ((inputReduction l E X).obj K.obj))
    (r34 : (e₃.evaluate (integralInterpretation l E)).obj K.obj ⟶
      (e₄.evaluate (integralInterpretation l E)).obj K.obj)
    (_c01 : CanonicalPair l E o ρ.compositors ρ.openComparisons
      ρ.canonicalBridge ρ.properOpen ρ.ringedModels ρ.ringedOpenComparisons
      ρ.ringedProperOpen ((inputReduction l E X).obj K.obj) K.obj e₀ e₁ s01 r01)
    (_c12 : CanonicalPair l E o ρ.compositors ρ.openComparisons
      ρ.canonicalBridge ρ.properOpen ρ.ringedModels ρ.ringedOpenComparisons
      ρ.ringedProperOpen ((inputReduction l E X).obj K.obj) K.obj e₁ e₂ s12 r12)
    (_c24 : CanonicalPair l E o ρ.compositors ρ.openComparisons
      ρ.canonicalBridge ρ.properOpen ρ.ringedModels ρ.ringedOpenComparisons
      ρ.ringedProperOpen ((inputReduction l E X).obj K.obj) K.obj e₂ e₄ s24 r24)
    (_c03 : CanonicalPair l E o ρ.compositors ρ.openComparisons
      ρ.canonicalBridge ρ.properOpen ρ.ringedModels ρ.ringedOpenComparisons
      ρ.ringedProperOpen ((inputReduction l E X).obj K.obj) K.obj e₀ e₃ s03 r03)
    (_c34 : CanonicalPair l E o ρ.compositors ρ.openComparisons
      ρ.canonicalBridge ρ.properOpen ρ.ringedModels ρ.ringedOpenComparisons
      ρ.ringedProperOpen ((inputReduction l E X).obj K.obj) K.obj e₃ e₄ s34 r34)
    (_route : ProjectionCoherenceRoutes l E D o ρ
      (s01 ≫ s12 ≫ s24) (s03 ≫ s34)) :
    r01 ≫ r12 ≫ r24 = r03 ≫ r34 := by
  have c014 := CanonicalPair.comp _g₁ _h₁.2 _c01
    (CanonicalPair.comp _g₂ _h₂.2 _c12 _c24)
  have c034 := CanonicalPair.comp _g₃ _h₃.2 _c03 _c34
  exact (((projectionIntegralCoherenceRealization l E D _hl o ρ).1
    _hcard iL e₀ e₄ _g₀ _g₄ K _h₄ _hL
    (s01 ≫ s12 ≫ s24) (s03 ≫ s34)
    (r01 ≫ r12 ≫ r24) (r03 ≫ r34)).2 _route).2 c014 c034

end WeilConjectures.IntegralSystemRealization
