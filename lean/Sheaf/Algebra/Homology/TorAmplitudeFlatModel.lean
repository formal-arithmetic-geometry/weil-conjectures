/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1, reviewer R-taf1249
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.RingTheory.Flat.CategoryTheory
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.FlatOpcyclesTorCriterion
import Sheaf.Algebra.Homology.KFlat

/-!
# Bounded flat models of complexes of modules of finite Tor amplitude

Source: Stacks Project, More on Algebra, Lemma 15.59.3 (Tag 0654)
(blueprint: lem-pc-module-tor-amplitude-flat-model).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- (blueprint: lem-pc-module-tor-amplitude-flat-model) Stacks Project, More on Algebra,
Lemma 15.59.3 (Tag 0654): for a commutative ring `A`, a cochain complex `M` of `A`-modules and
integers `a ≤ b`, the complex `M` has Tor amplitude in `[a, b]` (that is,
`H^i(M ⊗ᴸ_A N) = 0` for every `A`-module `N` and every `i ∉ [a, b]`) if and only if there is a
cochain complex `P` of flat `A`-modules with `P^i = 0` for `i ∉ [a, b]` and an isomorphism
`M ≅ P` in `D(A)`.

Proof: If `P` is a complex of flat modules in degrees `[a, b]`, it is bounded above and hence
K-flat (`lem-pc-module-bounded-flat-kflat`), so `P ⊗ᴸ N` is the ordinary tensor complex
`P ⊗ N`, which lives in degrees `[a, b]`. Conversely, testing against `N = A` shows that `M`
has cohomology in `[a, b]`; take a bounded-above flat resolution `P → M` with `P^i = 0` for
`i > b`. Then `H^{a-1}(P ⊗ N) = H^{a-1}(M ⊗ᴸ N) = 0` for every `N`, so the cokernel
`P^a / d(P^{a-1})` is flat (`lem-pc-module-flat-opcycles-tor-criterion`), and the truncation
`τ^{≥ a} P` is a complex of flat modules in degrees `[a, b]` quasi-isomorphic to `M`. This is
the specialization to `ModuleCat A` of the source's
`DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat`. -/
theorem module_torAmplitudeIn_iff_exists_flat_model {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) (hab : a ≤ b) :
    torAmplitudeIn (ModuleCat.{u} A) a b (Q.obj M) ↔
      ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
        (∀ i : ℤ, Module.Flat A (P.X i)) ∧
        (∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)) ∧
        Nonempty (Q.obj M ≅ Q.obj P) := by
  sorry

end DerivedCategory
