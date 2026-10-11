/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Kaehler.Basic

/-! # Smooth affine opens with vanishing differentials are étale
Source: Stacks Project, Morphisms, Section 02GH, Definition 02GI and Lemma 01V6
(blueprint: lem-weil-pbc-smooth-zero-differentials-affine-open-etale).
-/
universe u
open CategoryTheory
namespace AlgebraicGeometry
/-- A smooth morphism is étale on an affine open where the module of differentials vanishes.
Source: Stacks Project, Morphisms, Section 02GH, Definition 02GI and Lemma 01V6.
The ring map `R = Γ(S, V) → A = Γ(U, W)` is the algebra structure whose `algebraMap` is
`g.appLE V W hWV` (hypothesis `hφ`); `Ω_{A/R} = 0` is `Subsingleton (KaehlerDifferential R A)`.
(blueprint: lem-weil-pbc-smooth-zero-differentials-affine-open-etale)
Proof (the five steps of the node):
1. Factor the restriction through `V` using
   `lem-weil-pbc-morphism-factors-through-open-subscheme`. The map `W → V` is smooth by
   `lem-weil-pbc-smooth-restrict-open-subschemes` (a).
2. Identify `W` and `V` with the spectra of their section rings using
   `lem-weil-pbc-affine-open-spec-points`. The square for `Spec` of the induced ring map
   commutes by `lem-weil-pbc-affine-opens-induced-ring-map-spec-square`; uniqueness of
   factorization through `V` identifies that map with `W → V` under these isomorphisms.
3. Transport smoothness across these isomorphisms by
   `lem-weil-pbc-smooth-restrict-open-subschemes` (c), then apply
   `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`. The section ring map is smooth:
   it is finitely presented, its first cotangent homology vanishes, and its differential
   module is finite projective (`def-weil-pbc-smooth-ring-map`).
4. Together with the assumed vanishing of differentials, these properties make the ring
   map étale (Stacks Algebra, Definition 00U1). Its spectrum map is étale by
   `lem-weil-pbc-etale-ring-map-iff-etale-affine`.
5. The two affine identification isomorphisms and the inclusion `V → S` are open
   immersions, hence étale by `lem-weil-pbc-etale-composition-cancellation` (1).
   Compose them with the spectrum map using part (2) of that node to obtain étaleness
   of `W → V` and then of the required restriction `W → S`.
-/
theorem smooth_zero_differentials_affine_open_etale
    {U S : Scheme.{u}} (g : U ⟶ S) [Smooth g]
    (V : S.Opens) (W : U.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hWV : W ≤ g ⁻¹ᵁ V) [Algebra Γ(S, V) Γ(U, W)]
    (hφ : algebraMap Γ(S, V) Γ(U, W) = (g.appLE V W hWV).hom)
    (hΩ : Subsingleton (KaehlerDifferential Γ(S, V) Γ(U, W))) :
    Etale (W.ι ≫ g) := by
  sorry
end AlgebraicGeometry
