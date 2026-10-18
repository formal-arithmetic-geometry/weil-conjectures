/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.LisseRationalScalarFiberMaps

/-!
# Endomorphisms of geometric fibres under coefficient extension

Source: Deligne, Weil II (1.1.1) b)-d), pp. 146-147.
(blueprint: lem-pod-lisse-coefficient-fiber-endomorphisms).
-/

@[expose] public section

universe d
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{d})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  {Ω : Type d} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (K : Type (d + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]

/-- Extension from the least coefficient field detects and uniquely extends natural
endomorphisms of the geometric fibre with algebraically closed coefficients.

Source: Deligne, Weil II (1.1.1) b)-d), pp. 146-147 (restriction and extension of
coefficients); Stacks Project, Algebra, `lemma-separable-algebraic-diagonal`, finite
separable case (the diagonal summand of the scalar tensor product).
(blueprint: lem-pod-lisse-coefficient-fiber-endomorphisms).

Proof: write B for the least coefficient field and fix a finite coefficient field E.
Restrict an integral E-lattice to the integers of B and reindex its adic quotients by
the powers of the B-uniformizer. The finite coefficient quotients make each level
stalk a finite set, hence a finite B-integer module. Local constancy is preserved by
restriction of scalars. Cofinality of the two filtrations gives a lisse B-system:
at level n use the E-level
e(n+1)-1, where e is the ramification index, with restricted coefficients. The
uniformizer ideals agree there up to a unit, so the annihilation and transition
quotient conditions are exactly the required ones. Rationalizing gives restriction
of coefficients on rational sheaves and identifies its K-fibre with the fibre of the
restricted finite-dimensional E-vector space. These identifications respect all maps
by the prescribed pure-tensor formula hmap; different lattice choices give canonically
the same rational object because commensurable lattices are bounded by uniformizer
powers. To restrict a rational morphism, multiply it by a sufficiently large power
of the B-uniformizer so that its coefficient lies in the integers of E, restrict the
resulting integral map, and divide by that power in B. Equality after a further power
shows independence of this choice and compatibility with composition.

The proved rational scalar comparison, transported by obj_eq and map_eq, identifies
the functor P(B-to-E) followed by J_E with J_B. Conjugate the given endomorphism by
this comparison. Given the resulting endomorphism of the B-fibre, apply it to the
restriction of each E-sheaf.
Naturality for multiplication by every element of E says that the resulting K-linear
map commutes with the E-action. Since E/B is finite separable (characteristic zero),
K tensor_B E is a product of copies of K, indexed by embeddings E into K. Concretely,
a primitive element has a separable minimal polynomial; its linear factor for the
specified embedding is coprime to the complementary factor, and the Chinese remainder
projection gives the corresponding idempotent. Its diagonal
idempotent for the specified inclusion E into K selects the prescribed E-to-K fibre.
The endomorphism preserves this summand; restriction to it defines the desired
endomorphism of the E-fibre. Naturality for every E-sheaf morphism follows from that of
the B-endomorphism and the functorial idempotent. On a sheaf extended from B the
construction returns the original map: restriction of its extension is a finite direct
sum of the original B-sheaf; inclusions and projections force the endomorphism on that
sum to be the direct sum of the original endomorphism, and its diagonal summand has the
original map. This proves surjectivity of the displayed whiskering map.

For injectivity, each E-sheaf is a retract of the E-extension of its B-restriction.
The retraction is supplied by the same separability idempotent in E tensor_B E and is
a rational sheaf morphism. Two endomorphisms agreeing after extension from B agree on
that extended restriction and hence on its retract, by naturality for the inclusion
and projection. Finally conjugate these constructions by the recorded category
equalities and map_eq of the coefficient diagram. They identify its bottom transition
with the scalar extension used above. No coherence constraint of the diagram is used.
For E=B the whiskering map is identified with the identity by the unit comparison;
the zero sheaf and zero endomorphism are preserved throughout. -/
theorem lisseCoefficientFiberEndomorphisms_whisker_bijective
    (S : ∀ E₀ : Padic.FiniteCoefficientFields l K,
      LisseRationalSheaf l E₀.val Y ⥤ ModuleCat.{d + 1} E₀.val)
    (hS : ∀ (E₀ : Padic.FiniteCoefficientFields l K)
      (F : LisseRationalSheaf l E₀.val Y), (S E₀).obj F = lisseRationalFiber l E₀.val Y y F)
    (hmap : ∀ E₀ : Padic.FiniteCoefficientFields l K,
      IsLisseRationalFiberFunctor Y y l E₀.val (S E₀) (hS E₀)) :
    let P := (lisseCoefficientDiagramData l Y K).diagram
    let J := fun E₀ : Padic.FiniteCoefficientFields l K ↦
      (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀)).toFunctor ⋙
        S E₀ ⋙ ModuleCat.extendScalars (algebraMap E₀.val K)
    ∀ E₀ : Padic.FiniteCoefficientFields l K,
      Function.Bijective (fun u : J E₀ ⟶ J E₀ ↦
        Functor.whiskerLeft (P.map (homOfLE
          (show Padic.finiteCoefficientBase l K ≤ E₀ from
            show (⊥ : IntermediateField ℚ_[l] K) ≤ E₀.val from bot_le)).toLoc).toFunctor u) := by
  sorry

end AlgebraicGeometry.Scheme
