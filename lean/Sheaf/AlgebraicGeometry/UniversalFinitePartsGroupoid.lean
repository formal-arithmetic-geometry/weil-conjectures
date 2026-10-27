/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import Mathlib.CategoryTheory.Yoneda

/-!
# The groupoid on universal finite open source parts

Source: Stacks Project, More on Groupoids in Spaces, Tag 04RU and the preceding
explicit construction in `section-finite-part-groupoid`; Tag 04PH for closedness
(blueprint: lem-sfb-universal-finite-parts-groupoid).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The universal finite open source part containing the identity carries the translation
 groupoid, with finite source and target and its canonical morphism to the original groupoid.

Source: Stacks Project, Tag 04RU, the formulas preceding it, and Tag 04PH
(blueprint: lem-sfb-universal-finite-parts-groupoid).

The bijections `E` identify maps to `M` with precisely the pairs `(a,Z)` of the node.
The two equations for `b` uniquely determine the base-change map; `huniv` identifies
`Z` with the inverse image of `Q`. Thus these bijections are natural, and `Q` is the
universal family. A unit section is expressed by an actual lift into `Z`, with both
projection equations. No reducedness, affineness, or quasi-finiteness is imposed.

In the last clause, `m` and `n` are the source and target objects of the test arrow `q`.
The isomorphism `τ` is right translation by the inverse of its arrow coordinate.
The maps `k` and `l` into the composable-pair scheme are fixed by both projections;
their composites with `c` specify `τ` and its inverse on the arrow coordinate.
The final open-set equality says exactly that the target finite part is the image
of the source finite part under `τ`, as an open subscheme, on arbitrary test schemes.

Proof:
1. A test point of the universal family is a triple `(a,Z,z)`. Use the fibre-product
   universal property (def-pc-fibre-product) to construct right translation
   `r ↦ c(r,i(z))`, whose inverse is `r ↦ c(r,z)` by def-a1-groupoid-scheme.
   Yoneda (lem-galois-yoneda-fully-faithful) identifies these with scheme equalities.
2. Translation takes `z` to the identity at `t(z)` and the source identity to `i(z)`.
   Thus its image open is finite and contains both the new identity and inverse.
   These constructions commute with base change by
   lem-weil-pbc-open-immersion-base-change and lem-weil-pbc-finite-morphism-permanence.
3. For composable triples, `Z₁ = Z₂ z₂⁻¹`; hence `z₁z₂` belongs to `Z₂`.
   The composition formula is therefore well defined and natural. Yoneda produces
   the actual source, target, unit, inverse and composition morphisms.
4. Associativity in the original groupoid gives `τ_(z₁z₂) = τ_z₁ τ_z₂`.
   Together with `τ_e = 1` and `τ_(z⁻¹) τ_z = 1`, this gives the endpoint identities.
5. The two bracketings of three triples have identical source pair and arrow.
   The original unit and inverse laws give both unit laws and both inverse laws
   for the triples. Thus def-a1-groupoid-scheme applies on all test schemes.
6. The arrow coordinates of all operations are respectively `e(a)`, `i(z)` and
   `c(z₁,z₂)`; hence the projection to the original groupoid preserves all operations.
   Applying the inverse twice gives the identity of `Q`.
7. Source is the universal finite family. Target is source after the inverse
   isomorphism, and is finite too (def-weil-finite-integral-morphism).
8. The ambient source fibre is separated over `M` by
   lem-weil-pbc-separated-base-change. The finite family is proper by
   lem-weil-pbc-finite-proper. Apply lemma-nagata-proper-to-separated-target to its
   open inclusion, which is consequently proper and has closed image. -/
theorem universal_finite_parts_groupoid
    {S : Scheme.{u}} (U R M : Over S)
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s.left t.left ⟶ R.left)
    (hG : IsGroupoidScheme s.left t.left e.left i.left c)
    [IsSeparated s.left] [IsSeparated t.left]
    [LocallyOfFiniteType s.left] [LocallyOfFiniteType t.left]
    (g : M ⟶ U) [Etale g.left] (Q : (pullback s.left g.left).Opens)
    (E : ∀ T : Over S, (T ⟶ M) ≃
      (Σ a : T ⟶ U, {Z : (pullback s.left a.left).Opens //
        IsFinite (Z.ι ≫ pullback.snd s.left a.left) ∧
        ∃ v : T.left ⟶ Z.toScheme,
          v ≫ Z.ι ≫ pullback.fst s.left a.left = a.left ≫ e.left ∧
          v ≫ Z.ι ≫ pullback.snd s.left a.left = 𝟙 T.left}))
    (hforget : ∀ (T : Over S) (m : T ⟶ M), (E T m).1 = m ≫ g)
    (huniv : ∀ (T : Over S) (m : T ⟶ M),
      ∃ b : pullback s.left (E T m).1.left ⟶ pullback s.left g.left,
        b ≫ pullback.fst s.left g.left = pullback.fst s.left (E T m).1.left ∧
        b ≫ pullback.snd s.left g.left =
          pullback.snd s.left (E T m).1.left ≫ m.left ∧
        (E T m).2.val = b ⁻¹ᵁ Q) :
    ∃ (sQ tQ : Q.toScheme ⟶ M.left) (eQ : M.left ⟶ Q.toScheme)
      (iQ : Q.toScheme ⟶ Q.toScheme) (cQ : pullback sQ tQ ⟶ Q.toScheme),
      sQ = Q.ι ≫ pullback.snd s.left g.left ∧
      tQ ≫ M.hom = sQ ≫ M.hom ∧
      IsGroupoidScheme sQ tQ eQ iQ cQ ∧
      IsFinite sQ ∧ IsFinite tQ ∧ IsClosed (Q : Set ↥(pullback s.left g.left)) ∧
      (Q.ι ≫ pullback.fst s.left g.left) ≫ s.left = sQ ≫ g.left ∧
      (Q.ι ≫ pullback.fst s.left g.left) ≫ t.left = tQ ≫ g.left ∧
      eQ ≫ Q.ι ≫ pullback.fst s.left g.left = g.left ≫ e.left ∧
      iQ ≫ Q.ι ≫ pullback.fst s.left g.left =
        (Q.ι ≫ pullback.fst s.left g.left) ≫ i.left ∧
      (∀ (H : Scheme.{u}) (p : H ⟶ pullback sQ tQ)
        (d : H ⟶ pullback s.left t.left),
        d ≫ pullback.fst s.left t.left =
          p ≫ pullback.fst sQ tQ ≫ Q.ι ≫ pullback.fst s.left g.left →
        d ≫ pullback.snd s.left t.left =
          p ≫ pullback.snd sQ tQ ≫ Q.ι ≫ pullback.fst s.left g.left →
        p ≫ cQ ≫ Q.ι ≫ pullback.fst s.left g.left = d ≫ c) ∧
      (∀ (T : Over S) (m n : T ⟶ M) (q : T.left ⟶ Q.toScheme),
        q ≫ sQ = m.left → q ≫ tQ = n.left →
        ∃ (τ : pullback s.left (E T m).1.left ≅ pullback s.left (E T n).1.left)
          (k : pullback s.left (E T m).1.left ⟶ pullback s.left t.left)
          (l : pullback s.left (E T n).1.left ⟶ pullback s.left t.left),
          τ.hom ≫ pullback.snd s.left (E T n).1.left =
            pullback.snd s.left (E T m).1.left ∧
          k ≫ pullback.fst s.left t.left = pullback.fst s.left (E T m).1.left ∧
          k ≫ pullback.snd s.left t.left =
            pullback.snd s.left (E T m).1.left ≫
              q ≫ Q.ι ≫ pullback.fst s.left g.left ≫ i.left ∧
          τ.hom ≫ pullback.fst s.left (E T n).1.left = k ≫ c ∧
          l ≫ pullback.fst s.left t.left = pullback.fst s.left (E T n).1.left ∧
          l ≫ pullback.snd s.left t.left =
            pullback.snd s.left (E T n).1.left ≫
              q ≫ Q.ι ≫ pullback.fst s.left g.left ∧
          τ.inv ≫ pullback.fst s.left (E T m).1.left = l ≫ c ∧
          (E T n).2.val = τ.inv ⁻¹ᵁ (E T m).2.val) := by
  sorry

end AlgebraicGeometry
