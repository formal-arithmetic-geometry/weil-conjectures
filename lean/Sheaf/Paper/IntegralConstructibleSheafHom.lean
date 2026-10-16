/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Sheaf.CategoryTheory.HomColimitExtension
public import Mathlib.CategoryTheory.Category.ULift

/-! # Sequential Hom continuity for a constructible integral sheaf -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]

/-- Shifted Hom from a constructible integral sheaf commutes with uniformly bounded-below
sequential colimits. The lifted indexing category is equivalent to the ordinary natural numbers.
Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3),
Lemma 6.8.12 and the proof of Lemma 6.3.14.
(blueprint: lem-weil-pbc-integral-constructible-sheaf-hom)

Proof. Use good truncation at the common cohomological lower bound; filtered colimits
are exact, so this does not change the derived colimit or its canonical comparison.
Bounded-below qcqs cohomology commutes with direct sums and filtered colimits: on an
acyclic hypercover by finite unions of weakly contractible affines, every fixed total
degree has only finitely many contributing columns. Exact section evaluation on each
component commutes with these colimits, as do finite sums and filtered cohomology.
This proves the coefficient unit case. Finite perfect coefficient complexes inherit
this continuity. Here the library uses local finite presentations, so first compare
them with the finite integral models of Definition 6.8.10. On a presentation cover,
evaluate the finite matrix at geometric points. The fiber module type is independent
of the lift to the cover, by descent. Flat going-down lifts generalizations, and
continuous functions to the Hausdorff ring O_E agree at comparable points. Thus the
fiber Smith invariants agree along specialization. A Noetherian stratum has finitely
many irreducible components; their generic points and intersections show that the
module type is constant on each connected component, of which there are finitely many.
Near a point of the presentation cover choose an entry of smallest nonzero valuation.
Shrink so that it keeps that valuation, divide continuously by it, and perform integral
row and column operations. The fixed Smith invariants ensure that no smaller pivot
appears nearby. Repeat on the smaller matrix. A zero remainder is pointwise zero and
hence zero as a matrix of continuous functions. This diagonalization gives locally a
fixed finite O_E-module. The zero matrix needs no pivots. A finite module over the DVR
O_E has a finite free resolution (including its torsion summands); the resulting local
perfect resolution gives continuity on each such stratum by distinguished extensions.
The comparison is local in the pro-etale topology, using the same bounded hypercover
argument on a trivializing cover. Quasi-compact open extension by zero preserves it
by adjunction with exact restriction. For a closed stratum use the localization
triangle expressing its exceptional restriction by the complementary qcqs open
pushforward; the preceding bounded-below cohomology calculation commutes with this
triangle and preserves a common lower bound. Finite stratification and noetherian
open-closed induction now give every constructible source sheaf, for every shift.
Equivalently apply Hom to the sequential telescope: bounded-below coproduct continuity
identifies both adjoining Hom groups with direct sums; identity minus transition shift
is injective by induction on coordinates, and its cokernel is the filtered Hom colimit.
All comparisons are induced by the supplied cocone legs. The unique isomorphism of
colimit cocones transports the result to c. Zero ranks and the empty scheme give
zero groups and satisfy the same formulas. -/
theorem integralConstructible_sheaf_hom_colimit (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))
    (hM : IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X) M)
    (D : AsSmall.{u + 1} ℕ ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) ℤ)
    (c : Cocone D) (hc : Nonempty (IsColimit c))
    (hD : ∃ a : ℤ, ∀ n, (DerivedCategory.Q.obj (D.obj n)).IsGE a) :
    homColimitProperty (D ⋙ DerivedCategory.Q) (DerivedCategory.Q.mapCocone c)
      ((DerivedCategory.singleFunctor _ 0).obj M) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
