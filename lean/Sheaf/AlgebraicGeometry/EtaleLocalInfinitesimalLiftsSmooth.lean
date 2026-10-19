/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift
import WeilConjectures.AlgebraicGeometry.FormallySmooth
import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# Étale-local infinitesimal lifts imply smoothness

Source: Stacks Project, More on Morphisms, Tag 02H6, infinitesimal lifting criterion,
and Étale Cohomology, Tag 03P2, quasi-coherent cohomology comparison
(blueprint: lem-per-etale-local-infinitesimal-lifts-smooth).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A locally finitely presented morphism with étale-local solutions to every affine
first-order lifting problem is smooth. Source: Stacks Project, Tag 02H6, using the
sheaf of lifts argument and the étale comparison of Tag 03P2.
(blueprint: lem-per-etale-local-infinitesimal-lifts-smooth)

Proof: Fix an affine first-order thickening and a commutative test square. On the
étale site of the thickened affine scheme, consider the sheaf of lifts of `a₀` over `b`.
The hypothesis makes it locally nonempty. The difference of two lifts is a derivation
with values in the square-zero defining ideal. Thus the sheaf of lifts is a torsor under
the sheaf of such derivations, namely the pushforward from `T₀` of
Hom(`a₀`-pullback of Ω(V/W), I). Local finite
presentation makes the differentials finitely presented, so this Hom sheaf is
quasi-coherent on `T₀`; its pushforward to `T` is quasi-coherent as well. Tag 03P2
identifies its étale H¹ with its Zariski H¹, which vanishes on the affine scheme `T`.
Consequently the torsor is trivial and has a global section, giving a global lift
for every test square. Hence `f` is formally smooth. Together with local finite
presentation, the infinitesimal lifting criterion of Tag 02H6 gives smoothness. -/
theorem smooth_of_etale_local_infinitesimal_lifts
    {V W : Scheme.{u}} (f : V ⟶ W) [LocallyOfFinitePresentation f]
    (h_lift : ∀ (T₀ T : Scheme.{u}) [IsAffine T₀] [IsAffine T] (i : T₀ ⟶ T),
      IsFirstOrderThickening i →
      ∀ (a₀ : T₀ ⟶ V) (b : T ⟶ W), a₀ ≫ f = i ≫ b →
      ∃ (J : Type u) (Tj : J → Scheme.{u}) (v : ∀ j : J, Tj j ⟶ T),
        (∀ j : J, Etale (v j)) ∧
        (∀ t : T, ∃ (j : J) (x : Tj j), v j x = t) ∧
        ∃ a : ∀ j : J, Tj j ⟶ V,
          ∀ j : J, a j ≫ f = v j ≫ b ∧
            pullback.snd i (v j) ≫ a j = pullback.fst i (v j) ≫ a₀) :
    Smooth f := by
  sorry

end AlgebraicGeometry
