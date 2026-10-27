/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.CategoryTheory.ComonadStandardResolution
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# Unit extra degeneracies after applying the right adjoint

Source: Stacks Project, Simplicial, Situation 08N9 and Lemmas 08NC and 08ND
(blueprint: lem-trf-adjunction-right-image-extra-degeneracies).
-/

@[expose] public section

universe vS vA uS uA

open CategoryTheory Opposite Simplicial

namespace CategoryTheory.Adjunction

variable {S : Type uS} [Category.{vS} S] {A : Type uA} [Category.{vA} A]

/-- The adjunction unit supplies the left extra degeneracies of the right-adjoint
image of every supplied standard comonad resolution. The extra degeneracies live
in the parameter functor category, and their heterogeneous equalities specify the
unit maps across the prescribed equalities of the terms with comonad powers.
Source: Stacks Project, Situation 08N9 and Lemmas 08NC and 08ND
(blueprint: lem-trf-adjunction-right-image-extra-degeneracies).

Proof: Write G = FU. The prescribed faces are D_i^m = U(G^i ε G^(m-i))
and degeneracies are S_i^m = U(G^i δ G^(m-i)), with augmentation Uε.
Define h_{-1} = ηU and h_n = η at UG^(n+1). The right triangle identity
at a gives h_{-1} followed by Uε equal to the identity. At G^(n+1)a it
gives h_n followed by D_0^(n+1) equal to the identity, including n = 0.
Unit naturality at Uε_a gives h_0 followed by D_1^1 equal to Uε_a
followed by h_{-1}; this handles the augmented boundary separately.
For 0 ≤ i ≤ n+1, D_(i+1)^(n+2) = UF(D_i^(n+1)), so unit naturality
at D_i^(n+1) gives the remaining face equations. This includes i = n+1,
where the zeroth power is the identity. Likewise S_(i+1)^(n+1) = UF(S_i^n),
so naturality at S_i^n gives every degeneracy equation, including n = i = 0.
Finally unit naturality at UG^(n+1)(f), also at n = -1, makes each h_n
natural in a. The augmentation and all operators already are natural, and
componentwise equality proves the equations in the functor category. These are
exactly the five equation fields of Mathlib's ExtraDegeneracy structure. -/
theorem exists_rightImageExtraDegeneracies {F : S ⥤ A} {U : A ⥤ S} (adj : F ⊣ U)
    (B : SimplicialObject (A ⥤ A))
    (e : B ⟶ (SimplicialObject.const (A ⥤ A)).obj (𝟭 A))
    (hB : Comonad.IsStandardSimplicialResolution adj.toComonad B e) :
    ∃ ed : SimplicialObject.Augmented.ExtraDegeneracy
      (((SimplicialObject.Augmented.whiskering (A ⥤ A) (A ⥤ S)).obj
        ((Functor.whiskeringRight A A S).obj U)).obj
          { left := B, right := 𝟭 A, hom := e }),
      HEq ed.s' (Functor.whiskerLeft U adj.unit) ∧
      ∀ n : ℕ, HEq (ed.s n)
        (Functor.whiskerLeft
          (Comonad.resolutionPower adj.toComonad.toFunctor (n + 1) ⋙ U) adj.unit) := by
  sorry

end CategoryTheory.Adjunction
