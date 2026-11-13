/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasisPushforward
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasisSections
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasisUnitOfSections

/-! The scalar-basis unit decomposition used for condensed algebraic closures.

The construction follows the finite-support coefficient model: choose an algebraic basis of the
algebraic closure over the finite intermediate field, express each section through its finite
subextension, and transport the resulting coproduct decomposition through pullback, tensor, and
the derived category. The complete coordinate construction is left as this named stage-3 item.
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
finite-field-valued section model. -/
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
  let h := exists_condensedQbar_scalar_basis_sections ℓ E
  rcases h with ⟨I, b, hcoh, hexact, hN⟩
  refine ⟨I, b, hcoh, ?_⟩
  exact condensedQbar_scalar_basis_unit_of_sections ℓ E I b hexact hN

end AlgebraicGeometry.ProEtale.CondensedRing
