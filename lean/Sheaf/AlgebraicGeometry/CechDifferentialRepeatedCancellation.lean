module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.CategoryTheory.SiteCechComplex
public import Mathlib.GroupTheory.Perm.Sign

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The two duplicate faces cancel by the alternating permutation law.
Proof: construct the permutation exchanging the equal entries, apply the alternating
cochain law, compare restriction composites by the fibre-product universal property,
and use the opposite face signs to cancel.
(blueprint: lem-pc-cech-differential-repeated-cancellation) -/
theorem cechDifferential_repeated_cancellation (X : Scheme.{u}) {I : Type v}
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (c : S.cochains F p) (t : Fin (p + 2) → I)
    (a b : Fin (p + 2)) (hab : a ≠ b) (htab : t a = t b)
    (hc : ∀ (s : Fin (p + 1) → I) (σ : Equiv.Perm (Fin (p + 1))),
      c s = (Equiv.Perm.sign σ : ℤ) • F.map (S.indexMap s σ).op (c (s ∘ σ))) :
    (∑ j : ({a, b} : Finset (Fin (p + 2))),
      (-1 : ℤ) ^ (j : Fin (p + 2)).val •
        (F.map (S.indexMap t (j : Fin (p + 2)).succAbove).op)
          (c (t ∘ (j : Fin (p + 2)).succAbove))) = 0 := by
  sorry

end AlgebraicGeometry.Scheme
