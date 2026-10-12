/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleLocus

/-!
# Purity of the branch locus over a scheme smooth over a normal Noetherian base

Let `S` be a Noetherian integral normal scheme with generic point `η`, `f : X ⟶ S` smooth, and
`Y ⟶ X` the relative normalization of `X` in a normal scheme `W` lying over `η`. Let `s ≠ η`.
If `Y ⟶ X` is étale over the fibres of `f` at all strict generizations of `s`, and over a dense
subset of the fibre `X_s`, then it is étale over all of `X_s`
(`AlgebraicGeometry.Scheme.Hom.mem_etaleLocus_fromNormalization_of_smooth`).

This combines two purity results of [Stacks, Tag 0BJE], localized at `s`:
- if `𝒪_{S,s}` has dimension one, it is a discrete valuation ring, the fibre `X_s` is a regular
  effective Cartier divisor of `X ×_S Spec 𝒪_{S,s}`, and this is the purity across a regular
  divisor [Stacks 0EYE];
- if `𝒪_{S,s}` has dimension at least two, it has depth at least two (normality,
  [Stacks 031S]), and this is [Stacks 0EYB]: `FÉt_X ⟶ FÉt_U` is an equivalence for an open
  `U ⊆ X` containing the fibres over the points of depth at most one and dense in all fibres.
In both cases the finite étale extension is normal and finite over `X`, and it agrees with `Y`
over `f⁻¹(η)`, hence it is the normalization `Y`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- **Purity for normal covers of a scheme smooth over a normal Noetherian base** ([Stacks 0EYE]
in codimension one, [Stacks 0EYB] in codimension at least two). Let `S` be a Noetherian integral
normal scheme, `f : X ⟶ S` smooth, `w : W ⟶ X` a qcqs morphism from a locally Noetherian normal
scheme `W` lying over the generic point of `S`, and `p : Y ⟶ X` the relative normalization of
`X` in `W`. Let `s ∈ S` be a point other than the generic point. Assume that `p` is étale at all
points of `Y` lying over strict generizations of `s`, and that every point of the fibre `X_s`
generizes inside `X_s` to a point over which `p` is étale. Then `p` is étale at every point of `Y`
lying over `s`.

Proof sketch. Replace `S` by `Spec 𝒪_{S,s}` (normalization commutes with this flat base change,
integral closure commuting with localization). The étale locus `E` of `p` is open; its image `U`
in `X` (the points over which `p` is étale) is open as `p` is integral, contains the fibres over
the strict generizations of `s` and the generic points of the irreducible components of `X_s`.
If `dim 𝒪_{S,s} = 1`, then `𝒪_{S,s}` is a discrete valuation ring with uniformizer `π`,
`X_s = V(π)` is an effective Cartier divisor which is regular (smooth over a field), and
`p|_U` is unramified in codimension one, so it extends to a finite étale `Y' ⟶ X`
([Stacks 0EYE]). If `dim 𝒪_{S,s} ≥ 2`, then `depth 𝒪_{S,s} ≥ 2` ([Stacks 031S]), the points of
depth at most one are strict generizations of `s`, and `U_s` is dense in `X_s`, so `p|_U` extends to
a finite étale `Y' ⟶ X` ([Stacks 0EYB]). In both cases `Y'` is normal (étale over the normal `X`)
and finite over `X`, and `W ⟶ Y'` is dominant, so `Y'` is the normalization of `X` in `W`, i.e.
`Y' = Y`. -/
theorem mem_etaleLocus_fromNormalization_of_smooth {S X W : Scheme.{u}} [IsNoetherian S]
    [IsIntegral S] (hS : ∀ s : S, IsIntegrallyClosed (S.presheaf.stalk s))
    (f : X ⟶ S) [Smooth f] (w : W ⟶ X) [QuasiCompact w] [QuasiSeparated w]
    [IsLocallyNoetherian W]
    (hW : ∀ z : W, IsDomain (W.presheaf.stalk z) ∧ IsIntegrallyClosed (W.presheaf.stalk z))
    (hWη : ∀ z : W, f (w z) = genericPoint S) (s : S) (hs : s ≠ genericPoint S)
    (H : ∀ y : w.normalization, f (w.fromNormalization y) ⤳ s →
      f (w.fromNormalization y) ≠ s → y ∈ w.fromNormalization.etaleLocus)
    (hgen : ∀ x : X, f x = s → ∃ x' : X, x' ⤳ x ∧ f x' = s ∧
      ∀ y : w.normalization, w.fromNormalization y = x' → y ∈ w.fromNormalization.etaleLocus)
    (y : w.normalization) (hy : f (w.fromNormalization y) = s) :
    y ∈ w.fromNormalization.etaleLocus :=
  sorry

end AlgebraicGeometry.Scheme.Hom
