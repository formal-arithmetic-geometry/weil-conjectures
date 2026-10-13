module

public import Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Rename

@[expose] public section
universe u
namespace Algebra

/-- Adjoining an inverse preserves the relative global complete intersection condition.
After tensoring with every residue field of the base, the original presentation has
equidimensional fibres of dimension `n - c` by `hrel`. The enlarged fibre is the
principal open where the image of `h` is invertible, presented with one extra
variable and one extra equation. Principal opens preserve the local dimensions on
this equidimensional fibre, so its dimension is still `n - c`, equal to
`(n + 1) - (c + 1)`. This is exactly the defining fibre condition. Source: Stacks
Project, Algebra, Lemma Tag 00SS, part (2).
(blueprint: new-principal-localization-ci) -/
theorem principalLocalization_ci
    (R : Type u) [CommRing R] (n c : ℕ)
    (f : Fin c → MvPolynomial (Fin n) R)
    (hrel : IsRelativeGlobalCompleteIntersectionPresentation f)
    (h : MvPolynomial (Fin n) R) :
    IsRelativeGlobalCompleteIntersectionPresentation
        (Fin.snoc (α := fun _ ↦ MvPolynomial (Fin (n + 1)) R)
          (fun i ↦ MvPolynomial.rename Fin.castSucc (f i))
          (MvPolynomial.rename Fin.castSucc h * MvPolynomial.X (Fin.last n) - 1)) := by
  sorry

end Algebra
