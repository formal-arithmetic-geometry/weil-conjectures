/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasisUnit

/-! # Scalar-basis decompositions for the finite-subextension-valued algebraic closure
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

-- Keep the chosen derived adjunction folded while checking the scalar unit maps.
attribute [local irreducible] Mod.derivedExtendMapDerivedCategoryAdjunction
  AlgebraicGeometry.ProEtale.upperStarFromPoint AlgebraicGeometry.ProEtale.upperStar

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The scalar-basis proposition, with the complete coefficient and derived-unit formula. -/
def CondensedQbarDerivedScalarBasis : Prop :=
    ∃ (I : Type (u + 1))
      (τ : ∀ Z : Scheme.{u}, I → CatCenter (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)))),
      (∀ (Z : Scheme.{u}) (M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E) Z)))
        [HasCoproduct (fun _ : I ↦ M)],
        IsIso (Sigma.desc (f := fun _ : I ↦ M) fun i ↦
          (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).unit.app M ≫
          (Mod.comap (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).mapDerivedCategory.map
              ((τ Z i).app ((Mod.extendScalars (coefficientMap
                (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).leftDerivedFunctor.obj M)))) ∧
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (i : I)
        (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))),
        R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map ((τ X i).app M) =
          (τ Y i).app (R((f)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj M))

/-- A single algebraic basis gives compatible scalar endomorphisms on every scheme. -/
theorem condensedQbar_derived_scalar_basis :
    CondensedQbarDerivedScalarBasis ℓ E := by
  let h := exists_condensedQbar_scalar_basis_unit ℓ E
  rcases h with ⟨I, b, hb, hunit⟩
  refine ⟨I, fun Z i ↦ qbar_derivedCenter (Mod.qbar_scalarNatEndo (b Z i)), ?_, ?_⟩
  · intro Z M hM
    simpa only [Mod.qbar_scalarUnitLeg_eq] using hunit Z M
  · intro X Y f i M
    exact qbar_lowerStar_derivedScalarEndo_of_eq f (b X i) (b Y i) (hb f i) M

end AlgebraicGeometry.ProEtale.CondensedRing
