/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Adjacent maps between second-ideal algebraizations

Source: Stacks Project, Tag 088A, the maps G_(e+1) to G_e.
(blueprint: lem-weil-pbc-formal-second-ideal-algebraization-transitions).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Adjacent quotient transitions lift to maps inducing the smaller K-quotient.
Source: Stacks Project, Tag 088A, construction of the transitions of G_e.
(blueprint: lem-weil-pbc-formal-second-ideal-algebraization-transitions).

Proof: Write F_e for the pushforward of G_e from V(K^(e+1)). It is annihilated
by K^(e+1): on each affine open the action factors through the quotient ring, and
the section image of the recursively defined power is the corresponding ideal
power. Both F_(e+1) and F_e are annihilated by K^(e+2). Closed pushforward and
completion on V(K^(e+2)) therefore identify maps between them with maps between
their I-completions. Lift the adjacent transition of the double quotient system,
conjugated by the supplied comparison isomorphisms, to obtain t. Its completion
square is the displayed equation by construction. The map factors through the
K^(e+1)-quotient since the target is annihilated by that power. Completion of this
factor is an isomorphism: the iterated K-quotient equals the smaller K-quotient,
naturally in the I-level. Both modules in the factor lie on V(K^(e+1)), where
completion is an equivalence and reflects isomorphisms. Thus the factor is the
required q, and its composite with the quotient projection is t. -/
theorem formalSecondIdealAlgebraization_transitions
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (G : ∀ e : ℕ, CoherentModules (K ^ (e + 1)).subscheme)
    (β : ∀ e : ℕ,
      formalCompletionSystem I
          ((Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G e).obj) ≅
        (M.obj ⋙ formalCompletionFunctor K).flip.obj (op e)) :
    ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (e + 1)).2
        ((Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G e).obj)) ∧
      ∃ t : (Scheme.Modules.pushforward (K ^ (e + 2)).subschemeι).obj (G (e + 1)).obj ⟶
          (Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G e).obj,
        (∃ q : formalModuleQuotient K (e + 1)
            ((Scheme.Modules.pushforward (K ^ (e + 2)).subschemeι).obj (G (e + 1)).obj) ≅
            (Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G e).obj,
          formalModuleQuotientπ K (e + 1) _ ≫ q.hom = t) ∧
        formalCompletionMap I t ≫ (β e).hom =
          (β (e + 1)).hom ≫
            (M.obj ⋙ formalCompletionFunctor K).flip.map (homOfLE (Nat.le_succ e)).op := by
  sorry

end AlgebraicGeometry
