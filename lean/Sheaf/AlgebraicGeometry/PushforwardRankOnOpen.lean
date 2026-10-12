module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward

/-! Rank of a finite flat structure-sheaf pushforward on a constant-rank open.
Source: Stacks Project, Tags 02KB and 04MH.
(blueprint: lem-sc-finite-pushforward-rank-on-open)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- On any open where a finite flat locally finitely presented morphism has constant rank
`n`, its structure-sheaf pushforward has finite locally free rank `n`.

Source: Stacks Project, Morphisms of Schemes, Tags 02KB and 04MH.
(blueprint: lem-sc-finite-pushforward-rank-on-open)

Proof: Cover `U` by affine opens `V = Spec A` of `Y` contained in `U`. Since `f` is finite,
its inverse image is affine, say `Spec B`. The module of sections of the pushforward on `V`
is `B` with its `A`-action induced by `f`. Finiteness, flatness and local finite presentation
of `f` make `B` a finite flat finitely presented `A`-module, hence a finite projective module.
At every prime of `A`, its local rank equals `f.finrank` at the corresponding point of `V`,
by the affine definition and base-change invariance of the morphism rank. The hypothesis
therefore makes every such rank equal to `n`. A finite projective module of constant rank
`n` is locally free of rank `n`: near each prime, choose a basis of its free localization
and shrink to a principal open where its finitely many basis vectors and inverse matrix
are defined. These principal opens cover `V`. The associated sheaf is consequently locally
free of rank `n`. Combining the covers for all `V` gives local generators data of rank `n`
on the over-`U` site. If `U` is empty the covering condition is vacuous; for `n = 0` the
localized modules and the free sheaves are zero, so the same argument applies. -/
theorem isFiniteLocallyFreeOfRank_pushforward_unit_over {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (U : Y.Opens) (n : ℕ)
    (h : ∀ y ∈ U, f.finrank y = n) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).over U) n := by
  sorry

end AlgebraicGeometry.Scheme.Modules
