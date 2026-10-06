/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# The pushforward of the structure sheaf along a finite morphism

For a finite morphism `g : X ⟶ Y`, the `𝒪_Y`-module `g_* 𝒪_X` is coherent when `Y` is locally
noetherian, and when `Y` is integral it is free on a nonempty open subset of `Y`, of rank the
degree `g.finrank (genericPoint Y)` of `g` at the generic point.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pushforward_unit`: `g_* 𝒪_X` is of
  finite presentation.
- `AlgebraicGeometry.Scheme.Modules.exists_pullback_pushforward_unit_iso_free`: `g_* 𝒪_X` is
  generically free of rank `g.finrank (genericPoint Y)`.
- `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward`: the pushforward of a
  finite locally free module along a finite flat morphism of finite presentation is finite
  locally free.
- `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_pushforward_unit`: for `g` finite
  locally free of degree `d`, `g_* 𝒪_X` is finite locally free of rank `d`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- **The pushforward of the structure sheaf along a finite morphism is coherent.** If
`g : X ⟶ Y` is finite and `Y` is locally noetherian, then `g_* 𝒪_X` is of finite presentation:
over an affine open `Spec A` of `Y` it is the `𝒪`-module associated with the finite, hence
finitely presented, `A`-module `Γ(X, g ⁻¹ᵁ Spec A)`. -/
theorem isFinitePresentation_pushforward_unit [IsLocallyNoetherian Y] (g : X ⟶ Y) [IsFinite g] :
    ((pushforward g).obj (𝟙_ X.Modules)).IsFinitePresentation :=
  sorry

/-- **The pushforward of the structure sheaf along a finite morphism is generically free.** If
`g : X ⟶ Y` is finite and `Y` is integral, then `g_* 𝒪_X` is free of rank
`d = g.finrank (genericPoint Y)` on a nonempty open subset of `Y`. Over a nonempty affine open
`Spec A` of `Y`, with `A` a domain of fraction field `k(Y)`, the finite `A`-module
`B = Γ(X, g ⁻¹ᵁ Spec A)` has `B ⊗_A k(Y)` of dimension `d`; a basis of it taken in `B` gives an
`A`-linear map `A^d ⟶ B` which is injective with torsion cokernel, so becomes an isomorphism
after inverting a suitable nonzero `a ∈ A`. -/
theorem exists_pullback_pushforward_unit_iso_free [IsIntegral Y] (g : X ⟶ Y) [IsFinite g] :
    ∃ U : Y.Opens, (U : Set Y).Nonempty ∧
      Nonempty ((Modules.pullback U.ι).obj ((pushforward g).obj (𝟙_ X.Modules)) ≅
        SheafOfModules.free (ULift.{u} (Fin (g.finrank (genericPoint Y))))) :=
  sorry

/-- **Pushforward of finite locally free modules along finite flat morphisms.** If `g : X ⟶ Y`
is finite, flat and locally of finite presentation and `ℱ` is a finite locally free
`𝒪_X`-module, then `g_* ℱ` is a finite locally free `𝒪_Y`-module. Over an affine open `Spec A`
of `Y` with preimage `Spec B`, the `B`-module `M = Γ(ℱ, Spec B)` is finitely generated
projective, and `B` is a finitely generated projective `A`-module, so `M` is a finitely
generated projective `A`-module. -/
theorem isFiniteLocallyFree_pushforward (g : X ⟶ Y) [IsFinite g] [Flat g]
    [LocallyOfFinitePresentation g] (ℱ : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) ℱ] :
    SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) ((pushforward g).obj ℱ) :=
  sorry

/-- **The pushforward of the structure sheaf along a finite locally free morphism.** If
`g : X ⟶ Y` is finite locally free of degree `d`, then `g_* 𝒪_X` is a finite locally free
`𝒪_Y`-module of rank `d`. Over an affine open `Spec A` of `Y` it is the `𝒪`-module associated with
the finite, flat and finitely presented, hence projective, `A`-module `B = Γ(X, g ⁻¹ᵁ Spec A)`, and
its rank at a point `y` is the dimension `d` of the fibre `B ⊗_A κ(y) = Γ(X_y, 𝒪_{X_y})`.

This is the pointer remark to the properties of finite locally free morphisms; the statement is
proved in the blueprint as `lem-pc-flf-properties`.

(blueprint: `rem-ptr-pc-finite-locally-free-11`) -/
theorem isFiniteLocallyFreeOfRank_pushforward_unit (g : X ⟶ Y) (d : ℕ)
    [g.IsFiniteLocallyFreeOfDegree d] :
    ((pushforward g).obj (𝟙_ X.Modules)).IsFiniteLocallyFreeOfRank d :=
  sorry

end AlgebraicGeometry.Scheme.Modules
