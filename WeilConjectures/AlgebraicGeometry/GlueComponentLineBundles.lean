/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.ExistsGluedInvertible
import WeilConjectures.AlgebraicGeometry.ExistsGluedSection

/-!
# Gluing invertible modules and sections across components

## References

* Stacks Project, Varieties, Lemma 09NE.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/--
Let `Y` be reduced and covered by finitely many closed subschemes `i a : Z a ⟶ Y` with
discrete pairwise intersections. Invertible modules `M a` on the components glue to an
invertible module on `Y`, and sections nonvanishing at every point of the pairwise
intersections glue as well (Stacks, Varieties Lemma 09NE).
Module pullback is `tensorPullback`; `res N a` is restriction of
global sections to `Z a`, the unit of its canonical adjunction. `X_s` is `nonvanishingLocus`:
nonzero in the residue-field fibre.
-/
theorem glueComponentLineBundles
    {Y : Scheme.{u}} [IsReduced Y] {ι : Type v} [Finite ι]
    (Z : ι → Scheme.{u}) (i : ∀ a : ι, Z a ⟶ Y) [∀ a : ι, IsClosedImmersion (i a)]
    (hcover : (⋃ a : ι, Set.range (i a)) = Set.univ)
    (hdiscrete : ∀ a b : ι, a ≠ b →
      DiscreteTopology ↥(Set.range (i a) ∩ Set.range (i b)))
    (M : ∀ a : ι, (Z a).Modules) [∀ a : ι, (M a).IsInvertible] :
    let res : ∀ (N : Y.Modules) (a : ι), Γ(N, ⊤) → Γ((tensorPullback (i a)).obj N, ⊤) :=
      fun N a t ↦
        ((Classical.choose (exists_tensorPullbackAdjunction (i a))).unit.app N).val.app
          (op ⊤) t
    (∃ N : Y.Modules, N.IsInvertible ∧
      ∀ a : ι, Nonempty ((tensorPullback (i a)).obj N ≅ M a)) ∧
    ∀ s : ∀ a : ι, Γ(M a, ⊤),
      (∀ a b : ι, a ≠ b → Set.range (i a) ∩ Set.range (i b) ⊆
        i a '' nonvanishingLocus (M a) (s a)) →
      ∃ (N : Y.Modules) (t : Γ(N, ⊤)), N.IsInvertible ∧
        ∀ a : ι, ∃ e : (tensorPullback (i a)).obj N ≅ M a,
          e.hom.val.app (op ⊤) (res N a t) = s a := by
  dsimp
  constructor
  · exact existsGluedInvertible Z i hcover hdiscrete M
  · intro s hs
    exact existsGluedSection Z i hcover hdiscrete M s hs

end AlgebraicGeometry.Scheme.Modules
