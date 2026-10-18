import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Finite surjective refinements of fppf coverings

Source: Stacks Project, More on Morphisms, Tag 0CP0, lemma-dominate-fppf-finite
(blueprint: lem-trf-fppf-finite-surjective-refinement)
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every small fppf covering of a quasi-compact, quasi-separated scheme is
refined by a finite surjective morphism of finite presentation and an open cover
whose members map to members of the original covering.

Source: Stacks Project, More on Morphisms, Tag 0CP0, lemma-dominate-fppf-finite
(blueprint: lem-trf-fppf-finite-surjective-refinement)

The proof uses the integral-surjective refinement, approximation of integral
morphisms by finite morphisms, descent of quasi-compact opens along affine
transition maps, eventual equality of opens in an inverse limit, and
factorization of maps into locally finitely presented targets. The empty scheme
and empty covering are handled directly.
-/
theorem exists_finite_surjective_fppf_refinement
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {I : Type u} (Xi : I → Scheme.{u})
    (f : (i : I) → Xi i ⟶ X)
    [hflat : ∀ i, Flat (f i)]
    [hlfp : ∀ i, LocallyOfFinitePresentation (f i)]
    (hjoint : ∀ x : X, ∃ i y, f i y = x) :
    ∃ (X' : Scheme.{u}) (p : X' ⟶ X),
      IsFinite p ∧ LocallyOfFinitePresentation p ∧ QuasiCompact p ∧
        QuasiSeparated p ∧ Surjective p ∧
      ∃ (A : Type u) (U : A → Scheme.{u}) (j : (a : A) → U a ⟶ X'),
        (∀ a, IsOpenImmersion (j a)) ∧
        (∀ a, ∃ (i : I) (g : U a ⟶ Xi i), g ≫ f i = j a ≫ p) ∧
        (∀ x : X', ∃ a y, j a y = x) := by
  sorry

end AlgebraicGeometry
