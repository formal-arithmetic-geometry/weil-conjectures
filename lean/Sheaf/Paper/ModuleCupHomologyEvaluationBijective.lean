/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.ModuleCupHomologyEvaluation
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Bijectivity of canonical homology evaluation

Source: Stacks Project, Tag 064B, Lemma 13.19.8.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable (k : Type u) [CommRing k] [HasDerivedCategory.{u} (ModuleCat.{u} k)]

/-- The canonical evaluation map is bijective on every derived object.
Source: Stacks Project, Tag 064B, Lemma 13.19.8.
(blueprint: lem-sc-module-cup-homology-evaluation-bijective)
Proof: first take A = Q(K). The single free rank-one complex S(n) is bounded above
and each of its terms is projective, so it is K-projective. The K-projective
localization bijection identifies derived morphisms from Q(S(n)) to Q(K) with
chain maps S(n) to K modulo homotopy. Such maps correspond bijectively to cycles
z in degree n by sending the degree-n generator 1 to iCycles(z); k-linearity
makes this generator determine the map. Two maps are homotopic precisely when
their cycles differ by a boundary: the degree-(n-1) component of a homotopy gives
the boundary, and a preimage of a boundary defines this component and hence a
homotopy. Therefore evaluation induces a bijection with H^n(K). Naturality of
homologyFunctorFactors identifies this bijection with cupHomologyEvaluation.
For arbitrary A, essential surjectivity of Q provides an isomorphism Q(K) ≅ A.
Postcomposition with that isomorphism and its homology map are bijections and
intertwine the two evaluation maps by functoriality, transferring bijectivity.
No boundedness on K is used; for the zero ring both sides are singletons. -/
theorem cupHomologyEvaluation_bijective
    (A : DerivedCategory (ModuleCat.{u} k)) (n : ℤ) :
    Function.Bijective (cupHomologyEvaluation k A n) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
