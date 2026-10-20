/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Paper.CoefficientDuality
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-! # Bounded coherent duality for a dualizing complex

Source: Stacks Project, dualizing.tex, Lemma 0A7C (lemma-dualizing), bounded clause.
(blueprint: lem-sf-dualizing-complex-bounded-duality).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace DerivedCategory

/-- A dualizing complex induces duality on bounded complexes with finite cohomology.
The bounded injective model is the finite-injective-dimension hypothesis, and the
scalar-action map is the transpose of the right unitor, rather than an arbitrary
isomorphism of the two objects.

Source: Stacks Project, dualizing.tex, Lemma 0A7C, lemma-dualizing, bounded clause;
More on Algebra, Lemma 0A69, lemma-internal-hom-evaluate-isomorphism-technical.
(blueprint: lem-sf-dualizing-complex-bounded-duality).

Proof: Let D = RHom(-, Omega). The bounded injective model computes this functor
by Hom(-, I). If I is supported in [a,b], a representative of K supported above
c gives a dual supported below a-c, and a representative supported below c gives
a dual supported above b-c. Good truncations give these representatives, so D
exchanges the two boundedness conditions. Its cohomology is finite by Stacks
0G4H (lemma-finite-ext-into-bounded-injective): truncate K far enough above the
degree in question, then use a bounded-above finite-free model over the Noetherian
ring. Thus D preserves bounded finite cohomology.

The same finite-free models make each bounded-above truncation pseudo-coherent.
Apply the evaluation theorem 0A69 with both targets Omega. Its fixed first factor
RHom(Omega,Omega) is the unit, by the assumed scalar-action isomorphism, so has
Tor amplitude [0,0]. The resulting canonical map
RHom(Omega,Omega) tensor K -> RHom(RHom(K,Omega),Omega) is invertible. Compose with
scalar action tensor K and the inverse left unitor to obtain K -> D(D(K)).
The transpose of this composite is evaluation after Koszul interchange, since
scalar 1 acts as the identity of Omega. Evaluation and composition are natural
in K, so these maps form a natural transformation from the identity to DD.
Its components are invertible on the bounded finite subcategory. Restrict D to
that full subcategory; the natural bidual isomorphisms give D as its own
contravariant quasi-inverse. The restriction's comparison with ambient RHom is
the identity, which gives the displayed natural isomorphism. The zero ring and
zero complex satisfy the same argument, with zero objects throughout. -/
theorem dualizingComplex_bounded_duality
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (Ω : DerivedCategory (ModuleCat.{u} R))
    (hI : ∃ I : CochainComplex (ModuleCat.{u} R) ℤ,
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (I.X i)) ∧
      (∀ i : ℤ, Injective (I.X i)) ∧ Nonempty (Q.obj I ≅ Ω))
    (hfinite : ∀ i : ℤ,
      Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj Ω))
    (hscalar : IsIso (MonoidalClosed.curry (ρ_ Ω).hom)) :
    ∃ F : (WeilConjectures.boundedFiniteCoefficientComplex R).FullSubcategoryᵒᵖ ⥤
        (WeilConjectures.boundedFiniteCoefficientComplex R).FullSubcategory,
      F.IsEquivalence ∧
        Nonempty (F ⋙ (WeilConjectures.boundedFiniteCoefficientComplex R).ι ≅
          (WeilConjectures.boundedFiniteCoefficientComplex R).ι.op ⋙
            MonoidalClosed.internalHom.flip.obj Ω) := by
  sorry

end DerivedCategory
