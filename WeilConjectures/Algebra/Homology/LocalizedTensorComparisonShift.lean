/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonShiftSquare

/-!
# Shift stability of localized tensor comparison

## References

* Stacks Project, Tag 0DJA(1), using Tag 0BYJ
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- Core component transport for shift stability. -/
theorem localizedTensorComparisonProperty_shift_component
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : localizedTensorComparisonProperty R A B C Q N t X) (n : ℤ)
    (U : CochainComplex (ModuleCat.{u} A) ℤ)
    (hU : Nonempty (DerivedCategory.Q.obj U ≅ X⟦n⟧))
    (hK : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic)
    (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) := by
  obtain ⟨eU⟩ := hU
  have hV : Nonempty (DerivedCategory.Q.obj (U⟦-n⟧) ≅ X) := ⟨
    (DerivedCategory.Q.commShiftIso (-n)).app U ≪≫
      (shiftFunctor _ (-n)).mapIso eU ≪≫
      (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).app X⟩
  have hVK : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V (U⟦-n⟧) (curriedTensor _)).Acyclic := by
    intro V hV j
    apply HomologicalComplex.ExactAt.of_iso _
      (CochainComplex.mapBifunctorShift₂Iso V U (curriedTensor _) (-n)).symm
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hK V hV (-n + j)).isZero_homology.of_iso
      ((CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} A)
        (-n) j (-n + j) rfl).app
          (CochainComplex.mapBifunctor V U (curriedTensor _)))
  obtain ⟨mV, eS, eT, heq⟩ :=
    exists_localizedTensorComparison_shift_square R A B C Q N t U n mU i
  have hi := hX (U⟦-n⟧) hV hVK mV (i + n)
  change IsIso (_ ≫ _) at hi ⊢
  rw [heq]
  infer_instance


/-- Localized tensor comparison in all degrees is preserved by integer shifts. -/
theorem localizedTensorComparisonProperty_shift
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : localizedTensorComparisonProperty R A B C Q N t X) (n : ℤ) :
    localizedTensorComparisonProperty R A B C Q N t (X⟦n⟧) := by
  rw [localizedTensorComparisonProperty]
  intro U hU hK mU i
  exact localizedTensorComparisonProperty_shift_component R A B C Q N t X hX n U hU hK mU i

end ModuleCat
