import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import Sheaf.AlgebraicGeometry.Ample

/-! # A nonvanishing section trivializes an invertible module

Source: literature/stacks-project/modules.tex, Lemma (Tag 01CY).
(blueprint: lem-weil-pbc-nonvanishing-section-trivializes)
-/

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- A global section `s` of an invertible module `L` trivializes it on its non-vanishing
locus `Y_s = nonvanishingLocus L s` (germ of `s` outside `𝔪_y L_y`): `Y_s` is the underlying
set of an open `U`, the restriction to `U` (`SheafOfModules.overFunctor`) of the map
`homOfGlobalSection L s : 𝒪_Y ⟶ L`, `a ↦ a • s|`, is an isomorphism
`𝒪_Y|_U ≅ L|_U`, and consequently every section `t` of `L` over an open `V ⊆ U` is
`a • s|_V` for a unique `a ∈ 𝒪_Y(V)` (written `t / s`).

Proof (Stacks, Lemma 01CY): openness and the isomorphism are local, so trivialize `L` on an
open `W`, `L|_W ≅ 𝒪_W` with `s ↦ f`; there `Y_s ∩ W` is the basic open `D(f)`, hence
open, and these opens glue to `U`. At `y ∈ U` the stalk `L_y` is free of rank one and
`s_y ∉ 𝔪_y L_y`, so by Nakayama `s_y` is a basis of `L_y` and the stalk map `a ↦ a s_y` is
bijective; a morphism of sheaves of modules on `U` bijective on all stalks is an
isomorphism. Applying the inverse isomorphism to `t ∈ L(V)`, `V ⊆ U`, gives the unique `a`
(equivalently, the inverse section `s'` of `L^{⊗-1}` over `U` with `s'(s|_U) = 1` gives
`a = s'(t)`).
(blueprint: lem-weil-pbc-nonvanishing-section-trivializes)
-/
theorem nonvanishing_section_trivializes (Y : Scheme.{u}) (L : Y.Modules)
    [L.IsInvertible] (s : Γ(L, ⊤)) :
    ∃ U : Y.Opens, (U : Set Y) = nonvanishingLocus L s ∧
      IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf U).map (homOfGlobalSection L s)) ∧
      ∀ (V : Y.Opens), V ≤ U → ∀ (t : Γ(L, V)),
        ∃! a : Γ(Y, V), t = a • L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s := by
  sorry

end AlgebraicGeometry.Scheme.Modules
