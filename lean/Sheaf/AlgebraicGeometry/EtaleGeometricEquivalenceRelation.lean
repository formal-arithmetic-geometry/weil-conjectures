/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Geometric-point criterion for an étale equivalence relation

Source: Stacks Project, `groupoids.tex`, Tag 0DT7 (lemma-etale-equivalence-relation),
with the unramified projections specialized to étale projections
(blueprint: lem-sfb-unramified-geometric-equivalence-relation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An étale relation whose geometric-point fibres are equivalence relations is a
monomorphism and an equivalence relation on every test scheme over the base.

Source: Stacks Project, `groupoids.tex`, Tag 0DT7 (lemma-etale-equivalence-relation),
with the unramified projections specialized to étale projections
(blueprint: lem-sfb-unramified-geometric-equivalence-relation).

Proof:
1. The first projection of the relation map is étale and hence unramified; cancellation
   for an unramified composite makes the relation map unramified, so its diagonal is an
   open immersion.
2. Injectivity on algebraically closed field-valued points makes every geometric point of
   the pullback pair lie on that diagonal.  Algebraic closures of residue fields then make
   the diagonal surjective, hence an isomorphism.
3. The resulting diagonal is the categorical monomorphism condition on every test scheme.
4. The maps `e`, `i`, and `c` give reflexivity, symmetry, and transitivity of the image
   relation on arbitrary schemes over `S`. -/
theorem etale_geometric_equivalence_relation
    (S U R : Scheme.{u}) (f : U ⟶ S)
    (j : R ⟶ pullback f f)
    (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback (j ≫ pullback.snd f f) (j ≫ pullback.fst f f) ⟶ R)
    [Etale (j ≫ pullback.fst f f)] [Etale (j ≫ pullback.snd f f)]
    (he₁ : e ≫ j ≫ pullback.fst f f = 𝟙 U)
    (he₂ : e ≫ j ≫ pullback.snd f f = 𝟙 U)
    (hi₁ : i ≫ j ≫ pullback.fst f f = j ≫ pullback.snd f f)
    (hi₂ : i ≫ j ≫ pullback.snd f f = j ≫ pullback.fst f f)
    (hc₁ : c ≫ j ≫ pullback.fst f f =
      pullback.fst (j ≫ pullback.snd f f) (j ≫ pullback.fst f f) ≫
        (j ≫ pullback.fst f f))
    (hc₂ : c ≫ j ≫ pullback.snd f f =
      pullback.snd (j ≫ pullback.snd f f) (j ≫ pullback.fst f f) ≫
        (j ≫ pullback.snd f f))
    (hgeom : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (k : Spec (.of K) ⟶ S),
      (∀ (a b : Spec (.of K) ⟶ R),
        a ≫ j ≫ pullback.fst f f ≫ f = k →
        b ≫ j ≫ pullback.fst f f ≫ f = k →
        a ≫ j ≫ pullback.fst f f = b ≫ j ≫ pullback.fst f f →
        a ≫ j ≫ pullback.snd f f = b ≫ j ≫ pullback.snd f f →
        a = b) ∧
      (∀ (x : Spec (.of K) ⟶ U), x ≫ f = k →
        ∃ (r : Spec (.of K) ⟶ R),
          r ≫ j ≫ pullback.fst f f = x ∧
          r ≫ j ≫ pullback.snd f f = x) ∧
      (∀ (x y : Spec (.of K) ⟶ U),
        x ≫ f = k → y ≫ f = k →
        (∃ (r : Spec (.of K) ⟶ R),
          r ≫ j ≫ pullback.fst f f = x ∧
          r ≫ j ≫ pullback.snd f f = y) →
        ∃ (r : Spec (.of K) ⟶ R),
          r ≫ j ≫ pullback.fst f f = y ∧
          r ≫ j ≫ pullback.snd f f = x) ∧
      (∀ (x y z : Spec (.of K) ⟶ U),
        x ≫ f = k → y ≫ f = k → z ≫ f = k →
        (∃ (r : Spec (.of K) ⟶ R),
          r ≫ j ≫ pullback.fst f f = x ∧
          r ≫ j ≫ pullback.snd f f = y) →
        (∃ (r : Spec (.of K) ⟶ R),
          r ≫ j ≫ pullback.fst f f = y ∧
          r ≫ j ≫ pullback.snd f f = z) →
        ∃ (r : Spec (.of K) ⟶ R),
          r ≫ j ≫ pullback.fst f f = x ∧
          r ≫ j ≫ pullback.snd f f = z)) :
    Mono j ∧
      ∀ (T : Scheme.{u}) (g : T ⟶ S),
        (∀ (x : T ⟶ U), x ≫ f = g →
          ∃ (r : T ⟶ R),
            r ≫ j ≫ pullback.fst f f = x ∧
            r ≫ j ≫ pullback.snd f f = x) ∧
        (∀ (x y : T ⟶ U),
          x ≫ f = g → y ≫ f = g →
          (∃ (r : T ⟶ R),
            r ≫ j ≫ pullback.fst f f = x ∧
            r ≫ j ≫ pullback.snd f f = y) →
          ∃ (r : T ⟶ R),
            r ≫ j ≫ pullback.fst f f = y ∧
            r ≫ j ≫ pullback.snd f f = x) ∧
        (∀ (x y z : T ⟶ U),
          x ≫ f = g → y ≫ f = g → z ≫ f = g →
          (∃ (r : T ⟶ R),
            r ≫ j ≫ pullback.fst f f = x ∧
            r ≫ j ≫ pullback.snd f f = y) →
          (∃ (r : T ⟶ R),
            r ≫ j ≫ pullback.fst f f = y ∧
            r ≫ j ≫ pullback.snd f f = z) →
          ∃ (r : T ⟶ R),
            r ≫ j ≫ pullback.fst f f = x ∧
            r ≫ j ≫ pullback.snd f f = z) := by
  sorry

end AlgebraicGeometry
