/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.CategoryTheory.Sites.Precoverage
import Sheaf.AlgebraicGeometry.UniversallyClosedOfFpqcCover
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover
import Sheaf.AlgebraicGeometry.OverPullbackDiagonalClosedImmersion
import Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent

/-!
# Proper morphisms descend along fpqc covering families

Source: Stacks Project, Descent, Tag 02L1, `lemma-descending-property-proper`
(blueprint: lem-weil-pbc-proper-morphism-fpqc-descent).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Properness descends along an fpqc covering family.

Source: Stacks Project, Descent, Tag 02L1, `lemma-descending-property-proper`
(blueprint: lem-weil-pbc-proper-morphism-fpqc-descent).

Proof:
1. Each proper base change is separated, universally closed and locally of finite type,
   by `def-weil-proper-morphism`; finite type is local finite type and quasi-compactness
   (`def-weil-finite-type-morphism`).
2. Apply `lem-weil-pbc-fpqc-descend-universally-closed` to obtain universal closedness of `f`.
3. Apply `lem-weil-pbc-fpqc-descend-locally-finite-type` to obtain local finite type of `f`.
4. By `lem-weil-pbc-universally-closed-quasi-compact`, `f` is quasi-compact, hence of finite
   type together with step 3.
5. Pull the covering family back to `D = X ×_S X`, using
   `lem-galois-fpqc-covering-base-change`. Each base change of the diagonal of `f` is a
   closed immersion by `lem-weil-pbc-over-pullback-diagonal-closed-immersion`, since the
   corresponding base change of `f` is separated. The universal property of fibre products
   (`def-pc-fibre-product`) identifies `X ×_D (D ×_S S_i)` with `X ×_S S_i`, compatibly with
   their maps to `D ×_S S_i`: both represent pairs of maps to `X` and `S_i` agreeing over
   `S`, and both maps to the target send such a pair `(a,b)` to `(diagonal a,b)`.
   Apply `lem-pc-fpqc-descend-closed-immersion` to the diagonal over the cover of `D`.
   The diagonal is therefore a closed immersion, so `f` is separated.
6. Universal closedness, finite type and separatedness give properness by
   `def-weil-proper-morphism`.
-/
theorem isProper_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, IsProper (pullback.snd f (g i))) : IsProper f := by
  sorry

end AlgebraicGeometry
