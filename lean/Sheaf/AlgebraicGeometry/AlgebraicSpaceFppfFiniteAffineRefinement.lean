/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties

/-! # Finite affine scheme refinements of algebraic-space fppf coverings

Source: Stacks Project, Topologies on Algebraic Spaces, Tag 0DFQ,
lemma-zariski-etale-smooth-syntomic-fppf-fpqc, proof; Topologies, Tags 021P and 022C
(blueprint: lem-sfb-space-fppf-finite-affine-refinement).

The finite family is indexed by `Fin n`, including `n = 0`. Its maps and factorization
identities are over the original base scheme. The singleton map is the canonical map
from the scheme coproduct, rather than a separately chosen affine covering.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An fppf family of algebraic spaces has a finite affine scheme refinement over every
affine scheme mapping to its target. The finite coproduct is affine and its induced map
is flat, locally of finite presentation and surjective, and gives both singleton coverings.
Source: Stacks Project, Tag 0DFQ, lemma-zariski-etale-smooth-syntomic-fppf-fpqc, proof;
Topologies, Tag 021P, lemma-fppf-affine, and Tag 022C
(blueprint: lem-sfb-space-fppf-finite-affine-refinement).

Proof, following the accepted four-step split:
1. Form Z_i = T times_Y Y_i by lem-trf-space-fibre-products-etale-covers.
   By clauses (2), (1), (3) and (4) of lem-sfb-space-fppf-covering-calculus,
   pulling back the fppf family, choosing surjective etale scheme atlases W_i of Z_i,
   and composing yields an fppf covering of schemes W_i to T. The atlases exist by
   def-trf-algebraic-space. No quasi-compactness or separation of W_i or Y_i is used.
2. Apply lem-pc-fppf-affine-refinement to obtain finitely many affine opens V_j
   in W_a(j). Their maps p_j to T are flat and locally of finite presentation and
   jointly surjective. Compose V_j to Z_a(j) with Z_a(j) to Y_a(j) to define r_j.
   The fibre-product square gives r_j followed by q_a(j) = p_j followed by t.
3. Use lem-weil-pbc-scheme-coproduct-family to form the scheme coproduct and its
   induced map. By lem-weil-pbc-finite-affine-coproduct-spectrum it is the spectrum
   of the finite product of the affine coordinate rings. Its coprojections form
   an open cover, etale by lem-weil-pbc-open-immersion-etale. The family criterion
   of lem-sfb-scheme-etale-source-target-properties gives flatness and local finite
   presentation of the induced map. Any point of T lifts through one p_j, hence
   through the coproduct, proving surjectivity.
4. By def-pc-fppf-site these properties give the singleton fppf covering.
   Apply lem-trf-fppf-covering-is-fpqc to get the singleton fpqc covering.
   For empty T take n = 0: the empty coproduct is Spec of the zero ring by the
   empty case of lem-weil-pbc-finite-affine-coproduct-spectrum; all pointwise
   conditions and factorizations are vacuous. Flatness and local finite presentation
   are vacuous by def-weil-flat-morphism and def-sbc-locally-finite-presentation. -/
theorem exists_finite_affine_fppf_refinement {S : Scheme.{u}} {I : Type w}
    (Y : AlgebraicSpace S) (Yᵢ : I → AlgebraicSpace S) (q : ∀ i : I, Yᵢ i ⟶ Y)
    (hflat : ∀ i : I, MapIsFlat (q i))
    (hlfp : ∀ i : I, MapIsLocallyOfFinitePresentation (q i))
    (hsurj : IsJointlySurjective (fun i : I ↦ (q i).hom.hom))
    (T : Over S) [IsAffine T.left] (t : yoneda.obj T ⟶ Y.obj.obj) :
    ∃ (n : ℕ) (a : Fin n → I) (V : Fin n → Over S)
      (p : ∀ j : Fin n, V j ⟶ T)
      (r : ∀ j : Fin n, yoneda.obj (V j) ⟶ (Yᵢ (a j)).obj.obj),
      (∀ j : Fin n, IsAffine (V j).left) ∧
      (∀ j : Fin n, r j ≫ (q (a j)).hom.hom = yoneda.map (p j) ≫ t) ∧
      (∀ j : Fin n, Flat (p j).left ∧ LocallyOfFinitePresentation (p j).left) ∧
      (∀ x : T.left, ∃ (j : Fin n) (v : (V j).left), (p j).left.base v = x) ∧
      IsAffine (∐ fun j : Fin n ↦ (V j).left) ∧
      Flat (Sigma.desc (fun j : Fin n ↦ (p j).left)) ∧
      Surjective (Sigma.desc (fun j : Fin n ↦ (p j).left)) ∧
      LocallyOfFinitePresentation (Sigma.desc (fun j : Fin n ↦ (p j).left)) ∧
      Presieve.singleton (Sigma.desc (fun j : Fin n ↦ (p j).left)) ∈
        Scheme.fppfPrecoverage T.left ∧
      Presieve.singleton (Sigma.desc (fun j : Fin n ↦ (p j).left)) ∈
        Scheme.fpqcPrecoverage T.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
