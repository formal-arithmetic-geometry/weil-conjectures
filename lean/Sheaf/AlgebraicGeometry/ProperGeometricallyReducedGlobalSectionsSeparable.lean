/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Sheaf.FieldTheory.SeparableExtension
import Sheaf.FieldTheory.FiniteExtensionTensorAlgebraicClosureReduced
import Sheaf.Paper.EulerCharacteristicWellDefined

/-!
# Separability of global sections of a proper geometrically reduced scheme

Source: Stacks Project, Varieties, Lemma 0BUG (clause (4))
(blueprint: lem-pc-proper-geometrically-reduced-global-sections-separable).

The `k`-algebra structure on `Γ(X, ⊤)` is the structure map
`AlgebraicGeometry.Scheme.globalSectionsRingHom`, and the field structure is the one given by
`IsField` on the ring `Γ(X, ⊤)`, so both agree with the scheme's own ring structure.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If `X` is proper and geometrically reduced over a field `k`, and the structure map makes
`A = Γ(X, ⊤)` a field extension of `k`, then `A/k` is separable.
Source: Stacks Project, Varieties, Lemma 0BUG, clause (4)
(blueprint: lem-pc-proper-geometrically-reduced-global-sections-separable).

By `lem-pc-euler-characteristic-well-defined` (with `F = 𝒪_X`, `i = 0`) `A` is
finite-dimensional over `k`, so `A/k` is a finite field extension. For an algebraic closure
`k̄` of `k`, `Spec k̄ → Spec k` is flat and `X` is quasi-compact and quasi-separated, so flat
base change identifies `A ⊗_k k̄` with `Γ(X_k̄, 𝒪)`. Geometric reducedness makes `X_k̄`
reduced, hence its global sections, hence `A ⊗_k k̄`, are reduced. The criterion
`lem-pc-finite-extension-tensor-algebraic-closure-reduced-separable` then gives that `A/k`
is separable.
-/
theorem proper_geometricallyReduced_globalSections_isSeparable
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [GeometricallyReduced (X ↘ Spec (.of k))]
    (hA : IsField Γ(X, ⊤)) :
    @Algebra.IsSeparableExtension k Γ(X, ⊤) _ hA.toField
      (Scheme.globalSectionsRingHom k (X := X)).toAlgebra := by
  sorry

end AlgebraicGeometry
