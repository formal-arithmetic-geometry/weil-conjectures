/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisPushforward

/-! The scalar-basis unit decomposition used for condensed algebraic closures.

The construction follows the finite-support coefficient model: choose an algebraic basis of the
algebraic closure over the finite intermediate field, express each section through its finite
subextension, and transport the resulting coproduct decomposition through pullback, tensor, and
the derived category. The complete coordinate construction is left as this named stage-3 item.
(blueprint: lem-weil-pbc-condensed-qbar-derived-scalar-basis-unit)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

-- Keep the chosen derived adjunction folded while checking the scalar unit maps.
attribute [local irreducible] Mod.derivedExtendMapDerivedCategoryAdjunction
  AlgebraicGeometry.ProEtale.upperStarFromPoint AlgebraicGeometry.ProEtale.upperStar

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- Coherent coefficient sections whose scalar actions decompose the derived extension unit.
Source: Compatibility.lean, scalar-action calculation, and FiniteSubextension.lean, the
finite-field-valued section model.
(blueprint: lem-weil-pbc-condensed-qbar-derived-scalar-basis-unit)

Proof: choose an algebraic E-basis of Omega. Every finite-field-valued continuous function
has finite coordinate support: its values span a finite-dimensional E-space after taking the
compositum of its finite field with E. Coordinates are continuous by finite-dimensional
linear topology over Q_ell. Thus the restricted regular condensed Omega-module is a coproduct
of regular E-modules, with basis-vector summand maps. Pull the basis vectors to each scheme
by the monoidal point inverse image. The monoidal composition comparison proves the displayed
coherence equation. Tensor the coproduct decomposition with each module: the legs are the
extension unit followed by scalar multiplication by these sections. Exactness of coproducts
and scalar extension descends this natural decomposition termwise through the homotopy and
unbounded derived localizations. Naturality transports it to arbitrary derived objects, and
uniqueness of coproducts handles any chosen copower. No direct image enters this argument. -/
theorem exists_condensedQbar_scalar_basis_unit :
    ∃ (I : Type (u + 1))
      (b : ∀ Z : Scheme.{u}, I →
        (𝟙_ (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) ⟶
          condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)),
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (i : I), b X i =
        Functor.LaxMonoidal.ε (f)^*[Ab.{u + 1}] ≫
          (f)^*[Ab.{u + 1}].map (b Y i) ≫
            condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f) ∧
      (∀ (Z : Scheme.{u}) (M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E) Z)))
        [HasCoproduct (fun _ : I ↦ M)],
        IsIso (Sigma.desc (f := fun _ : I ↦ M) fun i ↦
          Mod.qbar_scalarUnitLeg (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z) (b Z i) M)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
