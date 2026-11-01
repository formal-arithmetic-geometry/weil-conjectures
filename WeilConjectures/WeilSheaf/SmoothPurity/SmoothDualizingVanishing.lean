/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.SmoothCoefficientVanishing

/-! # Vanishing outside the native smooth dualizing degree

This is the geometric vanishing input used to obtain the two canonical t-structure bounds.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits
open WeilConjectures WeilConjectures.ConstantPurityFrobenius

attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The native exceptional constant object has no cohomology outside degree `-2d`.

Source: current blueprint, `cor-pur-adic-and-rational-smooth-dualizing-complexes`,
smooth specialization, and `cor-coef-verdier-weil-equivariance`.
(blueprint: lem-sf-weil-smooth-dualizing-concentration)

Proof: base change the structure morphism to the algebraic closure and apply the
counit-normalized native exceptional-forgetting comparison.  The coefficient-stage
smooth purity theorem identifies the resulting ordinary exceptional object with the
constant Tate line shifted by `2d`; exact conservative forgetting transports its
vanishing in every other degree back to the native Weil category.  Frobenius
compatibility is only used to transport the comparison, so no identification of the
surviving Weil sheaf is needed here.
-/
theorem smooth_dualizing_homology_vanishing
    (J : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X)
    (adj : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ⊣ J)
    (d : ℕ) [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] :
    ∀ i : ℤ, i ≠ -2 * (d : ℤ) →
      IsZero ((homologySheaf i).obj
        (J.obj (WeilSheaf.toComplex.obj
          (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))))) := by
  classical
  let : Fintype k₀ := Fintype.ofFinite k₀
  obtain ⟨n, hp, hn⟩ := FiniteField.card k₀ (ringChar k₀)
  let D : FiniteFieldDatum.{u} :=
    { p := ringChar k₀, a := n, q := Nat.card k₀, prime := hp
      exponent_pos := n.pos
      cardinality_eq := by simpa only [Nat.card_eq_fintype_card] using hn
      k₀ := k₀, card_base := rfl, k := AlgebraicClosure k₀ }
  let : IsAlgClosure (Padic l) (ULift.{u} (PadicAlgCl l)) :=
    { isAlgClosed := ⟨fun p ↦ by
        let e : ULift.{u} (PadicAlgCl l) ≃+* PadicAlgCl l := ULift.ringEquiv
        have h := (IsAlgClosed.splits (p.map e.toRingHom)).map e.symm.toRingHom
        have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := by ext; rfl
        simpa only [Polynomial.map_map, he, Polynomial.map_id] using h⟩
      isAlgebraic := (ULift.algEquiv (R := Padic l) (A := PadicAlgCl l)).symm.isAlgebraic }
  let P : PurityFiniteSetting.{u} :=
    { field := D
      coefficients :=
        { l := l, different := Ne.symm (Fact.out : ringChar k₀ ≠ l)
          Qbar := ULift.{u} (PadicAlgCl l) }
      extension := ⊥
      level := 1
      level_pos := le_refl 1 }
  let X₀ : Over (Spec (.of D.k₀)) := Over.mk (X ↘ Spec (.of k₀))
  let : X₀.hom.IsOver (Spec (.of D.k₀)) := by
    constructor
    dsimp only [autoParam]
    change X₀.hom ≫ 𝟙 _ = X₀.hom
    rw [Category.comp_id]
  let : LocallyOfFiniteType X₀.hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k₀)))
  let : QuasiCompact X₀.hom := inferInstanceAs (QuasiCompact (X ↘ Spec (.of k₀)))
  let : IsSeparated X₀.hom := inferInstanceAs (IsSeparated (X ↘ Spec (.of k₀)))
  let : SmoothOfRelativeDimension d X₀.hom :=
    inferInstanceAs (SmoothOfRelativeDimension d (X ↘ Spec (.of k₀)))
  let c₀ : Compactification X₀.hom :=
    HasCompactification.compactification X₀.hom
      (hf := hasCompactification_of_over (k₀ := k₀) X₀.hom)
  have hs : Nonempty (systems D l P.coefficients.different P.coefficients.Qbar X₀) := by
    let Y₀ := point D
    let f₀ := pointMap D X₀
    let : LocallyOfFiniteType Y₀.hom :=
      inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k₀))))
    let : QuasiCompact Y₀.hom := inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))
    let : IsSeparated f₀.left := inferInstanceAs (IsSeparated X₀.hom)
    let : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType X₀.hom)
    let : QuasiCompact f₀.left := inferInstanceAs (QuasiCompact X₀.hom)
    let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
      (FrobeniusExchange.fiber_finiteType D X₀).1
    let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
      (FrobeniusExchange.fiber_finiteType D X₀).2
    let : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
      (FrobeniusExchange.fiber_finiteType D Y₀).1
    let : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
      (FrobeniusExchange.fiber_finiteType D Y₀).2
    let : (FrobeniusExchange.fiberMap D f₀).IsOver (Spec (.of D.k)) :=
      zlFiberMap_isOver D f₀
    let : IsSeparated (FrobeniusExchange.fiberMap D f₀) :=
      (FrobeniusExchange.fiberMap_properties D f₀).1
    let : LocallyOfFiniteType (FrobeniusExchange.fiberMap D f₀) :=
      (FrobeniusExchange.fiberMap_properties D f₀).2.1
    let : QuasiCompact (FrobeniusExchange.fiberMap D f₀) :=
      (FrobeniusExchange.fiberMap_properties D f₀).2.2
    exact @ConstructibleExceptionalCoefficients.exists_system.{u, u}
      l inferInstance P.coefficients.Qbar inferInstance inferInstance inferInstance
      D P.coefficients.different (D.geometricFiber X₀).left (D.geometricFiber Y₀).left
      (FrobeniusExchange.fiberMap D f₀) inferInstance inferInstance
      (FrobeniusExchange.fiber_finiteType D X₀).1
      (FrobeniusExchange.fiber_finiteType D X₀).2
      (FrobeniusExchange.fiber_finiteType D Y₀).1
      (FrobeniusExchange.fiber_finiteType D Y₀).2
      (zlFiberMap_isOver D f₀)
      (FrobeniusExchange.fiberMap_properties D f₀).1
      (FrobeniusExchange.fiberMap_properties D f₀).2.1
      (FrobeniusExchange.fiberMap_properties D f₀).2.2
  obtain ⟨S⟩ := hs
  obtain ⟨C, hcomp, hzero⟩ :=
    NativeCoefficientCohomology.smooth_coefficient_exceptional_vanishing P X₀ c₀ S d
  intro i hi
  obtain ⟨e⟩ := hcomp J adj i
  exact (hzero i hi).of_iso e

end AlgebraicGeometry.WeilComplex
