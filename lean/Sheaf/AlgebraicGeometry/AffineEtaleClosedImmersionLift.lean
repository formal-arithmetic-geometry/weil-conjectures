module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.RingTheory.EtaleAlgebraLift

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Source: Stacks Project, Étale Cohomology, Lemma 59.80.6 (Tag 09ZA),
first sentence of its proof, using Algebra Tag 04D1
(blueprint: lem-weil-pbc-affine-etale-closed-immersion-lift).

Proof: A closed subscheme of `X = Spec R` is affine, and its ring of global
sections is a quotient `R/I`. Write `V = Spec B`; the morphism `p` corresponds
to an étale `R/I`-algebra `B`. Stacks Tag 04D1 lifts this to an étale
`R`-algebra `C` whose reduction `C/IC` is isomorphic to `B` over `R/I`.
Put `U = Spec C` and let `q` be the map induced by `R → C`.
The tensor-quotient isomorphism identifies `C ⊗[R] (R/I)` with `C/IC`.
The affine fiber-product formula therefore gives an isomorphism
`V ≅ U ×[X] Z` over `Z`. Composing it with the projection to `U` defines
`a`; transporting the canonical pullback square gives `IsPullback a p q i`.
The construction also applies to the zero quotient and empty affine `V`;
no normality, reducedness, or nonemptiness is needed. -/
theorem Etale.exists_affine_lift_of_closedImmersion
    {X Z V : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (p : V ⟶ Z) [Etale p] [IsAffine V] :
    ∃ (U : Scheme.{u}) (_ : IsAffine U) (q : U ⟶ X) (_ : Etale q) (a : V ⟶ U),
      IsPullback a p q i := by
  sorry

end AlgebraicGeometry
