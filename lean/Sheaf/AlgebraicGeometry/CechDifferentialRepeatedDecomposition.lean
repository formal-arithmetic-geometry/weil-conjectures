module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.CategoryTheory.SiteCechComplex
public import Mathlib.GroupTheory.Perm.Sign

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The finite-sum reduction used in the repeated-tuple cancellation argument.
Proof: expand the alternating differential; every face outside the repeated positions
is zero by the repeated-tuple hypothesis, leaving exactly the displayed two-face sum.
(blueprint: lem-pc-cech-differential-repeated-decomposition) -/
theorem cechDifferential_repeated_decomposition (X : Scheme.{u}) {I : Type v}
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (c : S.cochains F p) (t : Fin (p + 2) → I)
    (a b : Fin (p + 2)) (hab : a ≠ b) (htab : t a = t b)
    (hz : ∀ s : Fin (p + 1) → I, ¬ Function.Injective s → c s = 0) :
    S.differentialValue F p c t =
      ∑ j : ({a, b} : Finset (Fin (p + 2))),
        (-1 : ℤ) ^ (j : Fin (p + 2)).val •
          (F.map (S.indexMap t (j : Fin (p + 2)).succAbove).op)
            (c (t ∘ (j : Fin (p + 2)).succAbove)) := by
  sorry

end AlgebraicGeometry.Scheme
