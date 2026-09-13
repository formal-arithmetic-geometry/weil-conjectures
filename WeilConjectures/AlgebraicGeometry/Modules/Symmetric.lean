/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Symmetric sheaves of modules on a group scheme

Let `G` be a group scheme over a base scheme `S`, that is, an object `G : Over S` together with
a `CategoryTheory.GrpObj G` structure, and let `ι` be its inversion. A sheaf of modules `L` on
the underlying scheme `G.left` is **symmetric** if it is fixed by pullback along the inversion:

```
    ι^* L ────≅────→ L
      │              │
      ↓      ι       ↓
   G.left ────────→ G.left
```

Since `ι` is its own inverse, `L ⊗ ι^* L` is symmetric for every `L`. This **symmetrisation** is
how a symmetric line bundle is manufactured out of an arbitrary one.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsSymmetric`: `L` is symmetric, that is, `ι^* L ≅ L`
  (blueprint: part of `def:deg-ample`, the twelfth definition counted in `sec:deg-cost`).

## Main results

- `AlgebraicGeometry.Scheme.Modules.isSymmetric_tensorObj_pullback`: `L ⊗ ι^* L` is symmetric.

## Implementation notes

* The inversion is spelled `ι`, which is `CategoryTheory.GrpObj.inv`, rather than `[-1]`, which
  is `CategoryTheory.GrpObj.zpow G (-1)`: the two are equal by
  `CategoryTheory.GrpObj.zpow_neg_one`, which is a `simp` lemma in the direction of `ι`, so `ι`
  is the form a `simp` call in a downstream proof leaves behind.

* Symmetry is intended for a line bundle `L`; invertibility is not part of the definition, and
  is carried as a hypothesis by the statements that need it, exactly as for
  `AlgebraicGeometry.Scheme.Modules.IsAmple`.

* The blueprint introduces symmetry for a *commutative* group scheme. Commutativity plays no
  part in it, and none is assumed here.

## Blueprint

This file implements the symmetry clause of `def:deg-ample` of
`curve_estimates/28_degree_of_the_isogeny.tex`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped MonObj

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] {L M : G.left.Modules}

/-- A sheaf of modules `L` on a group scheme `G` is **symmetric** if it is fixed by pullback
along the inversion `ι` of `G`, that is, if `ι^* L ≅ L`.
(blueprint: part of `def:deg-ample`) -/
def IsSymmetric (L : G.left.Modules) : Prop :=
  Nonempty ((pullback ι[G].left).obj L ≅ L)

variable {G}

/-- Symmetry is invariant under isomorphism. -/
theorem IsSymmetric.of_iso (hL : L.IsSymmetric G) (e : L ≅ M) : M.IsSymmetric G := by
  obtain ⟨f⟩ := hL
  exact ⟨(pullback ι[G].left).mapIso e.symm ≪≫ f ≪≫ e⟩

/-- Isomorphic sheaves of modules are symmetric together. -/
theorem isSymmetric_congr (e : L ≅ M) : L.IsSymmetric G ↔ M.IsSymmetric G :=
  ⟨fun hL ↦ hL.of_iso e, fun hM ↦ hM.of_iso e.symm⟩

variable (G) in
/-- **Symmetrisation**: `L ⊗ ι^* L` is symmetric, for every sheaf of modules `L` on a group
scheme. Indeed `ι ≫ ι = 𝟙`, so pullback along `ι` exchanges the two factors:
`ι^* (L ⊗ ι^* L) ≅ ι^* L ⊗ (ι ≫ ι)^* L ≅ ι^* L ⊗ L ≅ L ⊗ ι^* L`. -/
theorem isSymmetric_tensorObj_pullback (L : G.left.Modules) :
    (L ⊗ (pullback ι[G].left).obj L).IsSymmetric G := by
  have h : ι[G].left ≫ ι[G].left = 𝟙 G.left := by
    rw [← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left]
  exact ⟨(Functor.Monoidal.μIso (pullback ι[G].left) _ _).symm ≪≫
    tensorIso (Iso.refl _) ((pullbackTriangle h).app L ≪≫ (pullbackId G.left).app L) ≪≫ β_ _ _⟩

end AlgebraicGeometry.Scheme.Modules
