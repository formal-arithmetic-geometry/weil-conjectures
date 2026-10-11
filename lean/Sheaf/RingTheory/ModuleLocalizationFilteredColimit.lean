/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Module localization as the colimit of multiplication by one element

Source: Stacks Project, Section 10.9 (Tag 00CM), module localization at the powers of an
element (blueprint: lem-sc-module-localization-filtered-colimit).
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- (blueprint: lem-sc-module-localization-filtered-colimit) Stacks Project, Tag 00CM:
the canonical map from the colimit of `M --f--> M --f--> M --f--> ...` to `M_f` is an
`R`-linear isomorphism, sending the class of `m` at stage `e` to `m / f^e`.

Proof:
1. Index the copies of `M` by the filtered poset of natural numbers; successive maps
   multiply by `f`. The linear maps `m ↦ m / f^e` are compatible, because
   `(f • m) / f^(e+1) = m / f^e`, and induce a map from the colimit by its universal
   property (def-weil-pbc-category-colimit).
2. Every element of the localization is a fraction `m / f^e`, so this map is surjective
   (def-weil-pbc-module-localization-away; lem-weil-pbc-filtered-colimit-modules-elementwise).
3. If `m / f^e = n / f^d`, the localization equality criterion gives some `r` with
   `f^r • (f^d • m - f^e • n) = 0`. At stage `E = e + d + r` the representatives have
   difference `f^(E-e) • m - f^(E-d) • n = 0`. Thus they represent the same colimit element
   (def-weil-pbc-module-localization-away; lem-weil-pbc-filtered-colimit-modules-elementwise).
4. The induced linear map is bijective and hence a linear isomorphism, with the given formula.
-/
theorem localization_away_colimit
    {R : Type u} [CommRing R] (f : R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    let D : ℕ ⥤ ModuleCat.{v} R :=
      Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of R M)
        (fun _ : ℕ ↦ ModuleCat.ofHom (LinearMap.lsmul R M f))
    ∃ κ : ↥(colimit D) ≃ₗ[R] LocalizedModule.Away f M,
      ∀ (e : ℕ) (m : M),
        κ ((colimit.ι D e) m) =
          LocalizedModule.mk (S := Submonoid.powers f) m ⟨f ^ e, ⟨e, rfl⟩⟩ := by
  sorry

end ModuleCat
