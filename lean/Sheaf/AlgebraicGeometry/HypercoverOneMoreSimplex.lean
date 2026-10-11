/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.SimplicialHomObject
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite

/-!
# Adding one simplex to a hypercover Hom object

Source: Stacks Project, Tag 01GM, Lemma `lemma-one-more-simplex`
(blueprint: lem-weil-pbc-hypercover-one-more-simplex).
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.Scheme

/-- Restriction along the addition of one simplex is a covering of semi-representable
objects. Source: Stacks Project, Tag 01GM, Lemma `lemma-one-more-simplex`
(blueprint: lem-weil-pbc-hypercover-one-more-simplex).

Proof:
1. By lem-weil-pbc-simplicial-set-glue-simplex, the hypotheses exhibit `V` as the
pushout of `U` and `Δ[n]` along `∂Δ[n]`. At `n = 0` this is the coproduct with `Δ[0]`.
2. By lem-weil-pbc-simplicial-hom-object-standard-simplex, the simplex Hom object is
`K_n`, and for positive `n` the boundary Hom object is the matching object `M_n(K)`.
The universal families of def-weil-pbc-simplicial-hom-object identify these objects.
3. An isomorphism of formal coproducts has a bijective index map and isomorphisms on
components; it is thus a covering. By lem-weil-pbc-semi-representable-covering-permanence,
composing a covering with isomorphisms preserves coverings.
4. For `n > 0`, lem-weil-pbc-simplicial-hom-object-pushout turns the pushout into a
fibre square of Hom objects, whose top map is the restriction to `U`.
5. Under the identifications of step 2, the bottom map is the matching map `μ_n`:
their composites with each universal boundary component agree, hence they agree by
universality. It is a covering by def-weil-pbc-semi-representable-object and step 3.
6. Base change preserves coverings by lem-weil-pbc-semi-representable-covering-permanence.
The fibre product of lem-weil-pbc-semi-representable-finite-limits is isomorphic to the
Hom object in the square, and step 3 makes its projection to `Hom(U,K)_0` a covering.
7. For `n = 0`, lem-weil-pbc-simplicial-hom-object-pushout instead gives the product
`Hom(U,K)_0 × K_0`. The matching map `K_0 → {id_X}` is a covering by the hypercover
hypothesis. Regard this product as a fibre product over the terminal family, using
lem-weil-pbc-semi-representable-finite-limits; base change and step 3 give the result. -/
theorem isSemiRepresentableCovering_simplicialHomRestriction_one_more_simplex
    {X : Scheme.{u}} (K : SimplicialObject (FormalCoproduct.{w} X.Etale))
    (hK : IsSemiRepresentableHypercover K) (V : SSet.{t}) (U : V.Subcomplex)
    (hV : ∀ i : ℕ, Finite (V.obj (op ⦋i⦌)) ∧ Nonempty (V.obj (op ⦋i⦌)))
    (hU : ∀ i : ℕ, Finite (U.toSSet.obj (op ⦋i⦌)) ∧
      Nonempty (U.toSSet.obj (op ⦋i⦌)))
    [V.Finite] [U.toSSet.Finite]
    (n : ℕ) (x : V.obj (op ⦋n⦌)) (hx : x ∉ U.obj (op ⦋n⦌))
    (hlower : ∀ i : ℕ, i < n → U.obj (op ⦋i⦌) = Set.univ)
    (hdegree : (Set.univ : Set (V.obj (op ⦋n⦌))) = U.obj (op ⦋n⦌) ∪ {x})
    (hhigher : ∀ (j : ℕ) (z : V.obj (op ⦋j⦌)),
      n < j → z ∉ U.obj (op ⦋j⦌) → z ∈ V.degenerate j)
    {HV HU : FormalCoproduct.{w} X.Etale}
    (v : SimplicialHomFamily K V HV) (u : SimplicialHomFamily K U.toSSet HU)
    (hv : (simplicialHomFamilyFunctor K V).IsRepresentedBy v)
    (hu : (simplicialHomFamilyFunctor K U.toSSet).IsRepresentedBy u) :
    IsSemiRepresentableCovering (simplicialHomRestriction U v hu) := by
  sorry

end AlgebraicGeometry.Scheme
