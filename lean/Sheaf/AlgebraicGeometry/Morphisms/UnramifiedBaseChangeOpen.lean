module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Sheaf.AlgebraicGeometry.Thickening

/-!
# Base change and restriction of unramified morphisms

Source: Stacks Project, Morphisms, Lemma 02GA and the final clause of Lemma 02G6
(blueprint: lem-weil-pbc-unramified-base-change-open).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Stacks Project, Morphisms, Lemma 02GA and the final clause of Lemma 02G6.
(blueprint: lem-weil-pbc-unramified-base-change-open)

Proof steps from the DAG:
1. Local finite type passes to the base change by lem-weil-pbc-lft-base-change.
2. The original morphism is formally unramified by
   lem-weil-pbc-unramified-formally-unramified; its base change is formally unramified
   by lem-weil-pbc-formally-unramified-base-change.
3. Together these imply unramifiedness by
   lem-weil-pbc-lft-formally-unramified-unramified.
4. The restriction is locally of finite type by lem-weil-pbc-lft-affine-pairs:
   affine opens of the open subschemes give the same section ring maps as in X and S.
5. For a first-order thickening, two lifts into U give two lifts into X. They agree
   by formal unramifiedness of f (def-weil-pbc-formally-unramified-morphism), and hence
   agree in U since its inclusion is monic (lem-weil-pbc-open-immersion-monomorphism).
6. Local finite type and formal unramifiedness again imply unramifiedness by
   lem-weil-pbc-lft-formally-unramified-unramified. -/
theorem unramified_baseChange_restrict_open
    {X S S' : Scheme.{u}} (f : X ⟶ S)
    (hf : LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f))
    (g : S' ⟶ S) :
    LocallyOfFiniteType (pullback.snd f g) ∧
      IsOpenImmersion (pullback.diagonal (pullback.snd f g)) ∧
      (∀ (U : X.Opens) (V : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V),
        LocallyOfFiniteType (f.resLE V U hUV) ∧
          IsOpenImmersion (pullback.diagonal (f.resLE V U hUV))) := by
  sorry

end AlgebraicGeometry
