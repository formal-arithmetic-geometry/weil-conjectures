module

public import Sheaf.Algebra.Homology.HomologyEvaluationDefinitions
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.Algebra.Homology.HomComplexRestrictOpen
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap

/-! Core finite-free roof calculation for local homology evaluation. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

/-- The finite-free roof calculation proves local invertibility once its roof is exposed.
Source: Stacks Project, Tag 0BQY, zero-differential Hom calculation.
(blueprint: new-b2-homology-evaluation-local-iso-core).

The proof is the explicit finite-free zero-differential calculation together with the
quasi-isomorphism comparison square. -/
theorem homologyEvaluation_local_iso_of_roof (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k))
    (e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0))
    (he : IsHomologyEvaluation X T J n e) (V : X.Opens) (W : V.toScheme.Opens)
    (hI : CochainComplex.IsKInjective ((moduleOpenOverComplexFunctor X V W).obj J))
    (E L : CochainComplex
      (SheafOfModules (V.toScheme.ringCatSheaf.over W)) ℤ)
    (q : L ⟶ (moduleOpenOverComplexFunctor X V W).obj T)
    (p : L ⟶ E) (hq : QuasiIso q) (hp : QuasiIso p)
    (hzero : ∀ a b : ℤ, E.d a b = 0)
    (hsupp : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (E.X k))
    (hfree : ∀ k : ℤ, ∃ r : ℕ, Nonempty (E.X k ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf.over W) (ULift.{u} (Fin r)))) :
    IsIso (((Scheme.Modules.restrictFunctor V.ι).map e).over W) := by
  sorry

end CategoryTheory
