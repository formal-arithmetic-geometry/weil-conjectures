/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Sheaf.AlgebraicGeometry.Morphisms.FiniteAffineFamilyFppfAlgebra

/-!
# Finite affine charts subordinate to fppf local lifts

Source: Stacks Project, Descent, Tag 06NB, `lemma-curiosity`, first proof paragraph;
Topologies, Tag 021P, `lemma-fppf-affine`
(blueprint: lem-sfb-fppf-lifts-finite-affine-charts).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An arbitrary scheme morphism with lifts on an fppf covering admits, over every affine
open of its target, a finite affine fppf covering lifting into affine opens of its source.
The rings in the statement are the canonical global-section rings:
`B = Γ(V.toScheme, ⊤)`, `A j = Γ((U j).toScheme, ⊤)` and `D j = Γ(T j, ⊤)`.
Affineness identifies these schemes with the spectra of those rings. The maps on rings
are the actual `appTop` maps, and the product map is `RingHom.pi` of those maps.

Source: Stacks Project, Descent, Tag 06NB, `lemma-curiosity`, first proof paragraph;
Topologies, Tag 021P, `lemma-fppf-affine`
(blueprint: lem-sfb-fppf-lifts-finite-affine-charts).

Proof:
1. Pull the given covering back to V. Its projections g_i form an fppf covering by
   lem-trf-fppf-covering-base-change and def-pc-fibre-product. Compose the other projections
   with s_i. The resulting maps sigma_i satisfy a sigma_i = inclusion_V g_i, so their images
   lie in the inverse image of V. If V is empty choose n = 0 instead.
2. Cover the inverse image of V by affine opens U_k using lem-weil-pbc-affine-opens-basis.
   The inverse images sigma_i^{-1}(U_k) cover each pulled-back source. Their Zariski coverings
   are fppf by lem-pc-zariski-coverings-are-fppf. Compose these coverings with g_i using
   lem-sfb-space-fppf-covering-calculus and its equivalence for scheme families.
3. Apply lem-pc-fppf-affine-refinement to that covering over the affine V. This gives finitely
   many affine T_j, each lying over one U_k. The open factorization from
   lem-weil-pbc-morphism-factors-through-open-subscheme gives t_j and the restricted map a.
   Uniqueness of open factorization gives r_j = t_j followed by the restricted a.
4. The contravariance in def-weil-affine-spectrum gives the displayed ring factorizations.
   The affine criteria lem-weil-pbc-flat-morphism-affine-criterion and
   lem-weil-pbc-lfp-affine-opens-finite-presentation make every B to D_j flat and finitely
   presented. Finite presentation implies finite type by
   def-weil-pbc-finitely-presented-algebra and def-weil-pbc-finite-type-algebra.
5. Apply lem-a1-finite-affine-family-fppf-algebra with base and intermediate ring both B
   and identity base map. The fppf family is jointly surjective; step 4 supplies its algebra
   hypotheses. The coordinate map to the finite product is faithfully flat and finitely
   presented. For empty V the empty family gives B = D = 0, and the same algebra lemma
   includes this case. No property of a is used. -/
theorem exists_finite_affine_charts_of_fppf_lifts
    {X Y : Scheme.{u}} (a : X ⟶ Y) {I : Type v}
    (Yᵢ : I → Scheme.{u}) (q : ∀ i : I, Yᵢ i ⟶ Y)
    (s : ∀ i : I, Yᵢ i ⟶ X)
    (hq : Presieve.ofArrows Yᵢ q ∈ fppfPrecoverage Y)
    (hs : ∀ i : I, s i ≫ a = q i) (V : Y.Opens) (hV : IsAffineOpen V) :
    ∃ (n : ℕ) (U : Fin n → X.Opens)
      (e : ∀ j : Fin n, U j ≤ a ⁻¹ᵁ V)
      (T : Fin n → Scheme.{u})
      (t : ∀ j : Fin n, T j ⟶ (U j).toScheme)
      (r : ∀ j : Fin n, T j ⟶ V.toScheme),
      (∀ j : Fin n, IsAffineOpen (U j)) ∧
      (∀ j : Fin n, IsAffine (T j)) ∧
      (∀ j : Fin n, r j = t j ≫ a.resLE V (U j) (e j)) ∧
      Presieve.ofArrows T r ∈ fppfPrecoverage V.toScheme ∧
      (∀ j : Fin n,
        (r j).appTop = (a.resLE V (U j) (e j)).appTop ≫ (t j).appTop) ∧
      (∀ j : Fin n, (r j).appTop.hom.Flat ∧ (r j).appTop.hom.FinitePresentation) ∧
      (RingHom.pi (fun j : Fin n ↦ (r j).appTop.hom)).FaithfullyFlat ∧
      (RingHom.pi (fun j : Fin n ↦ (r j).appTop.hom)).FinitePresentation ∧
      (IsEmpty V.toScheme → n = 0 ∧ Subsingleton Γ(V.toScheme, ⊤) ∧
        Subsingleton (∀ j : Fin n, Γ(T j, ⊤))) := by
  sorry

end AlgebraicGeometry.Scheme
