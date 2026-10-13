module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

noncomputable def principalThickeningCanonical
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens)
    (n k : ℕ) : Γ(FiniteEtale.Adic.openThickening
      (Ideal.Quotient.mk (Ideal.span {g})) W (n + k), ⊤) →
      Γ(FiniteEtale.Adic.openThickening
        (Ideal.Quotient.mk (Ideal.span {g})) W n, ⊤) :=
  match k with
  | 0 => id
  | k + 1 => principalThickeningCanonical R g W n k ∘
      (FiniteEtale.Adic.openThickeningTransition
        (Ideal.Quotient.mk (Ideal.span {g})) W (n + k)).appTop

/-- The canonical quotient restriction across a bounded principal thickening gap.

Source: Stacks Project, Tags 0H3D and 0H3E. This is the geometric lifting step:
vanishing of `H^1(W,O_W)` together with the uniform annihilation hypothesis implies
that every section on the `(n+c)`-th principal thickening is the restriction of an
ambient section at level `n`. The proof is the derived two-term complex argument
of Tag 0H3D; it is recorded as a separate node so the elementary recursion argument
in the parent theorem can be checked independently.
(blueprint: new-principal-thickening-single-lift) -/
theorem principal_thickening_single_lift
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens)
    (hH : Subsingleton (Modules.H (X := W.toScheme)
      (SheafOfModules.unit W.toScheme.ringCatSheaf) 1))
    (c : ℕ)
    (hkill : ∀ (j : ℕ) (s : R), g ^ j * s = 0 → g ^ c * s = 0) :
    ∀ n (t : Γ(FiniteEtale.Adic.openThickening
      (Ideal.Quotient.mk (Ideal.span {g})) W (n + c), ⊤)),
      ∃ a : Γ(W.toScheme, ⊤),
        (FiniteEtale.Adic.openThickeningMap
          (Ideal.Quotient.mk (Ideal.span {g})) W n).appTop a =
          principalThickeningCanonical R g W n c t := by sorry

end AlgebraicGeometry.Scheme
