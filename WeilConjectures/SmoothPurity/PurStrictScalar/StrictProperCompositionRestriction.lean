/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarMateEvaluationData

/-! # Restriction and normalized proper composition

Source: Stacks 0D6E, 03DA and 0940; whole-tower derived-composite normalization.
(blueprint: lem-pur-strict-proper-composition-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective WeilConjectures.SemilinearSections.hasDerived
attribute [local instance 5000] AlgebraicGeometry.ProEtale.StrictTower.towers_hasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.ProEtale.StrictTower.towers_hasDerivedCategory
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
attribute [local irreducible] U J R G

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Restriction preserves the proper compositor, including transport of the composite map.
Source: Stacks 0D6E (lemma-derived-pushforward-composition), 03DA and 0940;
restriction-square proof, proper-composition step.
(blueprint: lem-pur-strict-proper-composition-restriction).
Proof: ordinary direct-image composition is induced by the canonical isomorphism
between iterated fibre products. Restriction of coefficients is identity on the
sections over those objects, and arithmetic selection just retains their indices.
Thus both commute with that ordinary compositor and with transport along h.
Restriction of coefficients preserves K-injectives because its left adjoint is
exact finite-free tensor. Positive arithmetic selection preserves K-injectives by
its exact left adjoint. Evaluate the derived composites on simultaneous
K-injective resolutions. The canonical composite resolution units identify their
ordinary compositor with rComp, and the ordinary restriction squares with
properRestriction and reindexProper respectively. The equality of the ordinary
composites therefore descends to the two displayed equations on the whole derived
diagram category. Naturality in the input complex extends the equations from the
resolution representatives to all derived objects. No evaluation-faithfulness
assumption is used. -/
theorem strictProperCompositionRestriction
    {W T Y : Scheme.{u}} (p : W ⟶ T) (g : T ⟶ Y) (q : W ⟶ Y)
    (h : p ≫ g = q) :
    let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
    let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)
    let tA := (rComp A p g).hom ≫ (eqToIso (congrArg (R A) h)).hom
    let tB := (rComp B p g).hom ≫ (eqToIso (congrArg (R B) h)).hom
    (∀ M : Derived B W,
      (R A g).map ((properRestriction l E F i p).inv.app M) ≫
          (properRestriction l E F i g).inv.app ((R B p).obj M) ≫
          (U l E F i Y).map (tB.app M) =
        tA.app ((U l E F i W).obj M) ≫ (properRestriction l E F i q).inv.app M) ∧
    ∀ (e : ℕ) (he : 1 ≤ e) (M : Derived B W),
      (subsequence l F Y e).map (tB.app M) ≫
          (reindexProper l F q e he).hom.app M =
        (reindexProper l F g e he).hom.app ((R B p).obj M) ≫
          (R B g).map ((reindexProper l F p e he).hom.app M) ≫
          tB.app ((subsequence l F W e).obj M) := by
  sorry

end WeilConjectures.PurStrictScalar
