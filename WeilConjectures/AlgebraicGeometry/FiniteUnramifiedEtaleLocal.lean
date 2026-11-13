/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.UnramifiedEtaleLocalDecomposition
import WeilConjectures.AlgebraicGeometry.FiniteUnramifiedEtaleLocalReduction

/-!
# Étale-local decomposition of finite unramified morphisms

## References

* [Stacks Project, Tag 04HJ](https://stacks.math.columbia.edu/tag/04HJ)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite unramified morphism `f : Y ⟶ X` (finite, locally of finite type, open-immersion
diagonal) becomes a finite disjoint union of closed immersions after passing to an étale
neighbourhood of any point of its target: there are an étale `g : U ⟶ X`, a point `u` over `x`,
a finite `J` and open-and-closed pieces `ι j : V j ⟶ Y ×_X U` exhibiting `Y ×_X U` as their
coproduct, each `ι j ≫ pullback.snd f g` a closed immersion. The neighbourhood need not
induce an isomorphism on residue fields. (Stacks, Tag 04HJ.) -/
theorem exists_etale_closed_immersion_decomposition_of_finite_unramified
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [LocallyOfFiniteType f]
    [IsOpenImmersion (pullback.diagonal f)] (x : X) :
    ∃ (U : Scheme.{u}) (g : U ⟶ X) (u : U),
      Etale g ∧ g.base u = x ∧
      ∃ (J : Type u) (V : J → Scheme.{u}) (ι : ∀ j, V j ⟶ pullback f g),
        Finite J ∧
        Nonempty (IsColimit (Cofan.mk (pullback f g) ι)) ∧
        (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j)) ∧
        (∀ j, IsClosedImmersion (ι j ≫ pullback.snd f g)) := by
  obtain ⟨n, pts, hpts, h⟩ := finite_decomposition_input f x
  exact finite_coproduct_of_unramified_decomposition f x n pts hpts h

end AlgebraicGeometry
