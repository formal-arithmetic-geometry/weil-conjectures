/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.Ample

/-! # Separatedness from an ample invertible module

Source: Stacks Project, Properties, Lemma 09MP (label lemma-ample-separated)
(blueprint: lem-weil-pbc-ample-scheme-separated).
-/

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

universe u

/-- A scheme carrying an ample invertible module is separated.

Source: Stacks Project, Properties, Lemma 09MP, proved using Lemma 01PY and
Definition 01PS (blueprint: lem-weil-pbc-ample-scheme-separated).
Proof (the node's affine-cover argument, rather than the source's valuative argument):
1. The affine nonvanishing loci of positive-degree sections cover `X` by ampleness
   (def-weil-pbc-ample-invertible-module); quasi-compactness is unused.
2. For sections of degrees `p` and `q`, replace them by their `q`-th and `p`-th powers.
   Both now belong to `L.tensorPow (p * q)` and their nonvanishing loci are unchanged
   (lem-weil-pbc-invertible-pullback-tensor).
3. The sections trivialize this invertible module on their respective opens `U` and `V`
   (lem-weil-pbc-nonvanishing-section-trivializes). Write `t = f * s` on `U` and
   `s = g * t` on `V`; then `U ∩ V` is `D(f)` in `U` and `D(g)` in `V`
   (lem-weil-pbc-affine-open-section-vanishing-prime).
4. The intersection is affine, and its ring of sections is the localization `A_f` of
   `A = Γ(U, 𝒪_X)` (lem-weil-pbc-affine-open-section-vanishing-prime).
5. On the intersection, `f * g = 1` by uniqueness of the trivializing coefficients
   (lem-weil-pbc-nonvanishing-section-trivializes). Each element of `A_f` is the image
   of `a ⊗ g^k` from `A ⊗[ℤ] Γ(V, 𝒪_X)`, so the restriction-product map is surjective
   (lem-weil-pbc-affine-open-section-vanishing-prime).
6. Apply lem-weil-pbc-separated-affine-cover-criterion over `Spec ℤ` to this cover:
   the intersections are affine and the restriction-product maps are surjective.
   Hence the structure morphism is separated (def-weil-proper-morphism).
-/
theorem isSeparated_of_isAmple (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (hL : L.IsAmple) : X.IsSeparated := by
  sorry

/-- The affine nonvanishing loci of positive tensor-power sections covering a scheme
already imply separatedness; no quasi-compactness assumption is required.

Source: Stacks Project, Properties, Lemma 01PY (label
lemma-affine-s-opens-cover-quasi-separated), used in Lemma 09MP
(blueprint: lem-weil-pbc-ample-scheme-separated).
Proof (the node's affine-cover argument, rather than the source's valuative argument):
1. The affine nonvanishing loci of positive-degree sections cover `X` by `hcover`
   (nonvanishing loci: def-weil-pbc-ample-invertible-module); quasi-compactness is unused.
2. For sections of degrees `p` and `q`, replace them by their `q`-th and `p`-th powers.
   Both now belong to `L.tensorPow (p * q)` and their nonvanishing loci are unchanged
   (lem-weil-pbc-invertible-pullback-tensor).
3. The sections trivialize this invertible module on their respective opens `U` and `V`
   (lem-weil-pbc-nonvanishing-section-trivializes). Write `t = f * s` on `U` and
   `s = g * t` on `V`; then `U ∩ V` is `D(f)` in `U` and `D(g)` in `V`
   (lem-weil-pbc-affine-open-section-vanishing-prime).
4. The intersection is affine, and its ring of sections is the localization `A_f` of
   `A = Γ(U, 𝒪_X)` (lem-weil-pbc-affine-open-section-vanishing-prime).
5. On the intersection, `f * g = 1` by uniqueness of the trivializing coefficients
   (lem-weil-pbc-nonvanishing-section-trivializes). Each element of `A_f` is the image
   of `a ⊗ g^k` from `A ⊗[ℤ] Γ(V, 𝒪_X)`, so the restriction-product map is surjective
   (lem-weil-pbc-affine-open-section-vanishing-prime).
6. Apply lem-weil-pbc-separated-affine-cover-criterion over `Spec ℤ` to this cover:
   the intersections are affine and the restriction-product maps are surjective.
   Hence the structure morphism is separated (def-weil-proper-morphism).
-/
theorem isSeparated_of_affine_nonvanishing_cover (X : Scheme.{u}) (L : X.Modules)
    [L.IsInvertible]
    (hcover : ∀ x : X, ∃ n : ℕ, 0 < n ∧
      ∃ s : (L.tensorPow n).val.presheaf.obj (Opposite.op ⊤), ∃ U : X.Opens,
        x ∈ U ∧ IsAffineOpen U ∧ (U : Set X) = nonvanishingLocus (L.tensorPow n) s) :
    X.IsSeparated := by
  sorry

end AlgebraicGeometry
