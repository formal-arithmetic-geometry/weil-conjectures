/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientCohomologyComparison
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist

/-! # Cohomology identification of native smooth dualizing purity

The native derived category of Weil sheaves retains derived morphisms.  This statement
isolates the cohomology identification. It does not identify that category with fixed pairs
of derived objects.
-/

@[expose] public section
set_option autoImplicit false

universe u

attribute [local instance 1100] CategoryTheory.instOverClass

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

open WeilConjectures WeilConjectures.ConstantPurityFrobenius
open CategoryTheory.Limits

private theorem coefficient_smooth_purity_iso (P : PurityFiniteSetting.{u})
    (X₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (c₀ : Compactification X₀.hom)
    (S : systems P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar X₀)
    (d : ℕ) [SmoothOfRelativeDimension d X₀.hom] :
    Nonempty (NativeCoefficientCohomology.twistedConstant P X₀ d ≅
      NativeCoefficientCohomology.exceptionalConstant P X₀ c₀ S) := by
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  let Y₀ := point D
  let f₀ := pointMap D X₀
  let : LocallyOfFiniteType Y₀.hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k₀))))
  let : QuasiCompact Y₀.hom := inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))
  let : IsSeparated Y₀.hom := inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k₀))))
  let : SmoothOfRelativeDimension d f₀.left :=
    inferInstanceAs (SmoothOfRelativeDimension d X₀.hom)
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
  let : IsSeparated ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    MorphismProperty.baseChange_obj (P := @IsSeparated) _ X₀ inferInstance
  let : IsSeparated ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    MorphismProperty.baseChange_obj (P := @IsSeparated) _ Y₀ inferInstance
  let : (FrobeniusExchange.fiberMap D f₀).IsOver (Spec (.of D.k)) :=
    zlFiberMap_isOver D f₀
  let : IsSeparated (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).1
  let : LocallyOfFiniteType (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).2.1
  let : QuasiCompact (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).2.2
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension d) :=
    smoothOfRelativeDimension_isStableUnderBaseChange d
  let : SmoothOfRelativeDimension d (FrobeniusExchange.fiberMap D f₀) :=
    MorphismProperty.overPullbackMap (P := @SmoothOfRelativeDimension d)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  let K := unit D l hl Ω (D.geometricFiber Y₀).left
  let γ := @RationalSmoothPurityCanonical.commonIso P
    (D.geometricFiber X₀).left (D.geometricFiber Y₀).left inferInstance inferInstance
    (FrobeniusExchange.fiber_finiteType D X₀).1
    (FrobeniusExchange.fiber_finiteType D X₀).2
    (MorphismProperty.baseChange_obj (P := @IsSeparated) _ X₀ inferInstance)
    (FrobeniusExchange.fiber_finiteType D Y₀).1
    (FrobeniusExchange.fiber_finiteType D Y₀).2
    (MorphismProperty.baseChange_obj (P := @IsSeparated) _ Y₀ inferInstance)
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
    (fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y)
    (FrobeniusExchange.fiberMap D f₀) (zlFiberMap_isOver D f₀)
    (FrobeniusExchange.fiberMap_properties D f₀).1
    (FrobeniusExchange.fiberMap_properties D f₀).2.1
    (FrobeniusExchange.fiberMap_properties D f₀).2.2
    (FrobeniusExchange.geometricCompactification D f₀ c₀) S d inferInstance K
  refine ⟨Endofunctor.IsoAlgebra.isoMk γ ?_⟩
  simpa only [NativeCoefficientCohomology.twistedConstant,
    NativeCoefficientCohomology.exceptionalConstant, Endofunctor.IsoAlgebra.mk,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, γ, D, l, hl, Ω, Y₀, f₀, K,
    Category.assoc] using
    (constant_purity_frobenius_square P X₀ c₀ S d).2.2

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The degree `-2d` cohomology of the exceptional constant object is the Tate line.

Source: current blueprint, `cor-pur-adic-and-rational-smooth-dualizing-complexes`,
smooth specialization, and `lem-pur-constant-purity-frobenius-square`.
(blueprint: lem-sf-weil-smooth-dualizing-cohomology)

Proof: form the arithmetic model of the given structure morphism, choose its
compactification and a coefficient-normalized exceptional adjunction system, and pass to
the geometric fibre. Smoothness of relative dimension d persists under this base change.
The canonical common-stage smooth purity map at the coefficient unit identifies the
shifted Tate constant with the exceptional constant. Clause three of the constant-purity
Frobenius square says exactly that this map intertwines their actual structure maps.
Thus it is an isomorphism of coefficient Frobenius pairs.

Use coefficient_cohomology_comparison in degree -2d. Its exceptional endpoint identifies
the native cohomology of the given J with the image of the exceptional pair. Apply its
cohomology functor to the inverse purity-pair isomorphism, and then compose with its
canonical Tate endpoint. This gives the displayed native Weil-sheaf isomorphism.
The comparison theorem isolates exact coefficient realization and its counit, root-line,
tensor-unit and shift normalizations, without a smoothness hypothesis or a purity
isomorphism. No assertion about other cohomology degrees is needed here, and no native
derived category is identified with fixed pairs of ordinary derived objects.
-/
theorem nonempty_smooth_dualizing_cohomology_iso
    (J : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X)
    (adj : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ⊣ J)
    (d : ℕ) [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty ((homologySheaf (-2 * (d : ℤ))).obj
        (J.obj (WeilSheaf.toComplex.obj
          (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))) ≅
      (WeilSheaf.tateTwistSheaf k₀ l X d).tensorObj (WeilSheaf.adicConstant k₀ l X)
        (WeilSheaf.isLisse_tateTwistSheaf k₀ l X d)) := by
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
  obtain ⟨C, hJ, hT⟩ :=
    NativeCoefficientCohomology.coefficient_cohomology_comparison P X₀ c₀ S
  obtain ⟨e⟩ := coefficient_smooth_purity_iso P X₀ c₀ S d
  obtain ⟨eJ⟩ := hJ J adj (-2 * (d : ℤ))
  obtain ⟨eT⟩ := hT d
  exact ⟨eJ ≪≫ (C (-2 * (d : ℤ))).mapIso e.symm ≪≫ eT⟩

end AlgebraicGeometry.WeilComplex
